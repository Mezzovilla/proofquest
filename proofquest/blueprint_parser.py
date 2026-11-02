"""Parser for leanblueprint ``content.tex`` files."""

from __future__ import annotations

import re
from pathlib import Path

from .game_model import ENV_KINDS, Blueprint, BlueprintNode


class BlueprintError(Exception):
    pass


_ENV_RE = re.compile(
    r"\\begin\{(" + "|".join(ENV_KINDS) + r")\}(.*?)\\end\{\1\}", re.DOTALL
)
_PROOF_RE = re.compile(r"\\begin\{proof\}(.*?)\\end\{proof\}", re.DOTALL)
_CHAPTER_RE = re.compile(r"\\chapter\*?\{([^{}]*)\}")
_SECTION_RE = re.compile(r"\\section\*?\{([^{}]*)\}")
_INPUT_RE = re.compile(r"\\input\{([^{}]*)\}")
_FORMAL_MACRO_RE = re.compile(r"\\(lean|uses)\{([^{}]*)\}")
_ANY_ENV_RE = re.compile(r"\\begin\{([^{}]+)\}(.*?)\\end\{\1\}", re.DOTALL)


def _strip_comments(tex: str) -> str:
    """Remove LaTeX comments (unescaped ``%`` to end of line)."""
    return re.sub(r"(?<!\\)%[^\n]*", "", tex)


def _resolve_inputs(tex: str, base_dir: Path, depth: int = 0) -> str:
    if depth > 10:
        raise BlueprintError("\\input nesting too deep (cycle?)")

    def _sub(match: re.Match[str]) -> str:
        name = match.group(1)
        path = base_dir / name
        if path.suffix == "":
            path = path.with_suffix(".tex")
        if not path.exists():
            raise BlueprintError(f"\\input file not found: {path}")
        content = _strip_comments(path.read_text(encoding="utf-8"))
        return _resolve_inputs(content, base_dir, depth + 1)

    return _INPUT_RE.sub(_sub, tex)


def _macro_values(body: str, macro: str) -> list[str]:
    values: list[str] = []
    for match in re.finditer(r"\\" + macro + r"\{([^{}]*)\}", body):
        values.extend(v.strip() for v in match.group(1).split(",") if v.strip())
    return values


def _dedupe(values: list[str]) -> list[str]:
    return list(dict.fromkeys(values))


def _optional_title(body: str) -> str | None:
    match = re.match(r"\s*\[([^\]]*)\]", body)
    return match.group(1).strip() if match else None


def parse_blueprint(content_tex: Path) -> Blueprint:
    """Parse ``content.tex`` (following ``\\input``) into a :class:`Blueprint`."""
    if not content_tex.exists():
        raise BlueprintError(f"blueprint content file not found: {content_tex}")
    tex = _strip_comments(content_tex.read_text(encoding="utf-8"))
    tex = _resolve_inputs(tex, content_tex.parent)

    chapters = [(m.start(), m.group(1)) for m in _CHAPTER_RE.finditer(tex)]
    sections = [(m.start(), m.group(1)) for m in _SECTION_RE.finditer(tex)]

    def _current(markers: list[tuple[int, str]], pos: int) -> str | None:
        name = None
        for start, title in markers:
            if start < pos:
                name = title
            else:
                break
        return name

    env_matches = list(_ENV_RE.finditer(tex))

    nodes: list[BlueprintNode] = []
    parse_issues: list[str] = []
    seen_labels: set[str] = set()
    nested_proof_spans: set[tuple[int, int]] = set()
    for order, match in enumerate(env_matches):
        kind, body = match.group(1), match.group(2)
        labels = _macro_values(body, "label")
        if not labels:
            raise BlueprintError(
                f"{kind} environment #{order + 1} has no \\label; "
                "every environment needs a label to appear in the dependency graph"
            )
        label = labels[0]
        if label in seen_labels:
            raise BlueprintError(f"duplicate \\label{{{label}}}")
        seen_labels.add(label)

        proof_matches = list(_PROOF_RE.finditer(body))
        for proof_match in proof_matches:
            nested_proof_spans.add(
                (
                    match.start(2) + proof_match.start(),
                    match.start(2) + proof_match.end(),
                )
            )
        if len(proof_matches) > 1:
            parse_issues.append(
                f"{label}: multiple nested proof environments are not supported"
            )
        proof_match = proof_matches[0] if proof_matches else None
        proof_tex = proof_match.group(1).strip() if proof_match else None
        statement_body = _PROOF_RE.sub("", body)
        title = _optional_title(body)
        if title is not None:
            statement_body = re.sub(r"^\s*\[[^\]]*\]", "", statement_body, count=1)

        nodes.append(
            BlueprintNode(
                kind=kind,
                label=label,
                lean_names=_macro_values(body, "lean"),
                title=title,
                statement_tex=statement_body.strip(),
                proof_tex=proof_tex,
                uses=_dedupe(_macro_values(body, "uses")),
                leanok="\\leanok" in body,
                chapter=_current(chapters, match.start()) or "Main",
                section=_current(sections, match.start()),
                order=order,
            )
        )

    # leanblueprint writes `\begin{proof} ... \end{proof}` *after* the closing
    # `\end{theorem}`/`\end{lemma}` (a top-level sibling environment, not nested
    # inside the statement). Attach each such proof to the environment that ends
    # immediately before it, and merge any `\uses` the proof carries.
    attached_proof_spans: set[tuple[int, int]] = set()
    for proof_match in _PROOF_RE.finditer(tex):
        span = proof_match.span()
        if span in nested_proof_spans:
            continue
        owner = None
        for idx, env_match in enumerate(env_matches):
            if env_match.end() <= proof_match.start():
                owner = idx
            else:
                break
        if owner is None:
            parse_issues.append("proof environment has no preceding blueprint node")
            continue
        between = tex[env_matches[owner].end() : proof_match.start()]
        if between.strip():
            parse_issues.append(
                f"proof environment after {nodes[owner].label} is not adjacent and was not attached"
            )
            continue
        if nodes[owner].proof_tex is not None:
            parse_issues.append(
                f"{nodes[owner].label}: multiple proof environments are not supported"
            )
            continue
        proof_body = proof_match.group(1).strip()
        nodes[owner].proof_tex = proof_body
        nodes[owner].uses = _dedupe(
            nodes[owner].uses + _macro_values(proof_body, "uses")
        )
        attached_proof_spans.add(span)

    consumed_spans = [match.span() for match in env_matches] + list(attached_proof_spans)
    unknown_envs = [
        match
        for match in _ANY_ENV_RE.finditer(tex)
        if match.group(1) not in (*ENV_KINDS, "proof")
    ]
    for macro_match in _FORMAL_MACRO_RE.finditer(tex):
        if any(start <= macro_match.start() and macro_match.end() <= end for start, end in consumed_spans):
            continue
        macro = f"\\{macro_match.group(1)}{{{macro_match.group(2)}}}"
        enclosing = next(
            (
                match.group(1)
                for match in unknown_envs
                if match.start() <= macro_match.start() < match.end()
            ),
            None,
        )
        context = f" inside unsupported {enclosing} environment" if enclosing else ""
        parse_issues.append(
            f"unconsumed formal binding {macro}{context}; only "
            + ", ".join(ENV_KINDS)
            + " environments are parsed"
        )

    if not nodes:
        parse_issues.append("selected blueprint contains no supported formal nodes")

    chapter_titles = [title for _, title in chapters] or ["Main"]

    # Chapter introduction: text between \chapter{...} and the first
    # \section or environment that follows it.
    chapter_intros: dict[str, str] = {}
    boundaries = sorted(
        [m.start() for m in _ENV_RE.finditer(tex)]
        + [pos for pos, _ in sections]
        + [pos for pos, _ in chapters]
        + [len(tex)]
    )
    for match in _CHAPTER_RE.finditer(tex):
        end_of_macro = match.end()
        next_boundary = min(b for b in boundaries if b > match.start() and b >= end_of_macro)
        chapter_intros[match.group(1)] = tex[end_of_macro:next_boundary].strip()

    return Blueprint(
        nodes=nodes,
        chapters=chapter_titles,
        chapter_intros=chapter_intros,
        parse_issues=_dedupe(parse_issues),
    )
