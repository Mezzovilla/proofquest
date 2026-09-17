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
    seen_labels: set[str] = set()
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

        proof_match = _PROOF_RE.search(body)
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
                uses=_macro_values(body, "uses"),
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
    for proof_match in _PROOF_RE.finditer(tex):
        owner = None
        for idx, env_match in enumerate(env_matches):
            if env_match.end() <= proof_match.start():
                owner = idx
            else:
                break
        if owner is not None:
            proof_body = proof_match.group(1).strip()
            if nodes[owner].proof_tex is None:
                nodes[owner].proof_tex = proof_body
            for use in _macro_values(proof_body, "uses"):
                if use not in nodes[owner].uses:
                    nodes[owner].uses.append(use)

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

    return Blueprint(nodes=nodes, chapters=chapter_titles, chapter_intros=chapter_intros)
