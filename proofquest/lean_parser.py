"""Text-level extraction of declarations from Lean 4 source files.

This intentionally supports only the regular declaration style found in
blueprint-driven projects (plain ``def``/``theorem``/``lemma`` with binders
and a ``:=``/``:= by`` body). It does not handle ``where`` clauses, mutual
blocks, or exotic notations in signatures.
"""

from __future__ import annotations

import re
from collections.abc import Set as AbstractSet
from pathlib import Path

from .game_model import LeanDecl

_EXCLUDED_DIRS = {
    ".lake",
    ".git",
    "build",
    "docbuild",
    "blueprint",
    "home_page",
}

_DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|partial|scoped)\s+)*"
    r"(def|theorem|lemma|abbrev|instance|structure)\s+([A-Za-z_][\w'.]*)",
)

_MODIFIER_LINE_RE = re.compile(
    r"(?:private|protected|noncomputable|partial|scoped)\s*"
)

_LOCAL_SYNTAX_RE = re.compile(
    r"(?:(?:local|scoped|private|protected)\s+)*"
    r"(?:notation3?|infixl?|infixr?|prefix|postfix|syntax|macro_rules|macro|"
    r"elab_rules|elab|unexpander|app_unexpander|declare_syntax_cat|"
    r"attribute|set_option|initialize)\b"
)

_LOCAL_SYNTAX_KIND_RE = re.compile(
    r"(?:(?:local|scoped|private|protected)\s+)*([A-Za-z_][\w']*)"
)

_BOUNDARY_RE = re.compile(
    r"^(?:@\[|/--|--|namespace\b|end\b|section\b|open\b|variable\b|import\b|"
    r"(?:private|protected|noncomputable|partial|scoped)\s*$|"
    + _LOCAL_SYNTAX_RE.pattern
    + r"|(?:(?:private|protected|noncomputable|partial|scoped)\s+)*"
    r"(?:def|theorem|lemma|abbrev|instance|structure|example)\b)"
)

_OPEN, _CLOSE = "([{⟨", ")]}⟩"


def _split_signature(decl_text: str, keyword: str, name: str) -> tuple[str, str | None]:
    """Split a declaration into (signature, proof) at the top-level ``:=``."""
    header_re = re.compile(
        r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|scoped)\s+)*"
        + keyword
        + r"\s+"
        + re.escape(name)
    )
    match = header_re.match(decl_text)
    if not match:
        raise LeanParseError(f"cannot re-match declaration header of {name}")
    rest = decl_text[match.end():]

    depth = 0
    i = 0
    skip_next_assign = False  # skip `:=` belonging to a `let` in the signature
    has_where_body = False
    while i < len(rest):
        ch = rest[i]
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
        elif ch == '"':  # skip string literals
            i += 1
            while i < len(rest) and rest[i] != '"':
                i += 2 if rest[i] == "\\" else 1
        elif depth == 0 and rest.startswith("where", i) and (
            i == 0 or not (rest[i - 1].isalnum() or rest[i - 1] in "_.'")
        ) and (i + 5 >= len(rest) or not (rest[i + 5].isalnum() or rest[i + 5] in "_.'")):
            has_where_body = True
        elif depth == 0 and rest[i:i+3] == "let" and (i + 3 >= len(rest) or not rest[i+3].isalnum() and rest[i+3] != "_"):
            skip_next_assign = True
        elif depth == 0 and rest.startswith(":=", i):
            if has_where_body:
                pass
            elif skip_next_assign:
                skip_next_assign = False
            else:
                return rest[:i].strip(), rest[i + 2:].strip()
        i += 1
    return rest.strip(), None


class LeanParseError(Exception):
    pass


def _parse_file(
    path: Path, project_modules: AbstractSet[str] = frozenset()
) -> list[LeanDecl]:
    lines = path.read_text(encoding="utf-8").splitlines()
    decls: list[LeanDecl] = []
    ns_stack: list[tuple[str, str | None]] = []  # (kind, name)
    var_stack: list[list[str]] = []  # saved `variable` lines per section
    active_vars: list[str] = []  # currently active `variable` lines
    file_imports: list[str] = []  # external imports (Mathlib.* etc.)
    active_opens: list[str] = []  # active `open` statements

    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if stripped.startswith("import "):
            module = stripped.removeprefix("import ").strip()
            if module not in project_modules:
                file_imports.append(module)
            i += 1
            continue
        if stripped.startswith("open "):
            active_opens.append(stripped)
            i += 1
            continue
        if stripped.startswith("namespace "):
            ns_stack.append(("ns", stripped.removeprefix("namespace ").strip()))
            i += 1
            continue
        if stripped == "section" or stripped.startswith("section "):
            ns_stack.append(("sec", stripped.removeprefix("section").strip() or None))
            var_stack.append(list(active_vars))
            i += 1
            continue
        if stripped == "end" or stripped.startswith("end "):
            if ns_stack:
                kind, _ = ns_stack.pop()
                if kind == "sec" and var_stack:
                    active_vars = var_stack.pop()
            i += 1
            continue
        if stripped.startswith("variable "):
            active_vars.append(stripped)
            i += 1
            continue

        match = _DECL_RE.match(line) if not line[:1].isspace() else None
        header = i
        if match is None and _MODIFIER_LINE_RE.fullmatch(stripped):
            k = i
            while (
                k + 1 < len(lines)
                and _MODIFIER_LINE_RE.fullmatch(lines[k + 1].strip())
            ):
                k += 1
            if (
                k + 1 < len(lines)
                and not lines[k + 1][:1].isspace()
                and _DECL_RE.match(lines[k + 1])
            ):
                header = k + 1
                match = _DECL_RE.match(lines[header])
        if match:
            keyword, name = match.group(1), match.group(2)
            j = header + 1
            while j < len(lines):
                nxt = lines[j]
                if nxt.strip() and not nxt[:1].isspace() and _BOUNDARY_RE.match(nxt):
                    break
                j += 1
            block = "\n".join(lines[i:j]).rstrip()
            if name.startswith("_root_."):
                resolved = name.removeprefix("_root_.")
                namespace, _, name = resolved.rpartition(".")
                full_name = resolved
            else:
                namespace = ".".join(n for kind, n in ns_stack if kind == "ns" and n)
                full_name = f"{namespace}.{name}" if namespace else name
            signature, proof = _split_signature(block, keyword, match.group(2))
            decls.append(
                LeanDecl(
                    keyword=keyword,
                    name=name,
                    full_name=full_name,
                    namespace=namespace,
                    signature=signature,
                    proof=proof,
                    source_text=block,
                    variables=list(active_vars),
                    imports=list(file_imports),
                    opens=list(active_opens),
                    line=i,
                )
            )
            i = j
            continue
        i += 1
    return decls


def _strip_comments_keep_lines(text: str) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0
    while i < n:
        ch = text[i]
        if depth == 0 and ch == '"':
            out.append('"')
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    out.append(text[i:i + 2])
                    i += 2
                else:
                    out.append(text[i])
                    i += 1
            if i < n:
                out.append('"')
                i += 1
        elif depth == 0 and text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
        elif text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth == 0:
            out.append(ch)
            i += 1
        else:
            if ch == "\n":
                out.append("\n")
            i += 1
    return "".join(out)


def _module_local_commands(
    path: Path, project_modules: AbstractSet[str]
) -> tuple[list[tuple[int, str]], list[str]]:
    """``((line, command kind) list, project module imports)`` of one file.

    Complements ``_parse_file`` (which only sees files through their
    declarations): a file may define notation yet declare nothing. Only the
    command *kind* (``notation``, ``set_option``, ...) is kept, never the raw
    command text. ``set_option ... in`` applies to a single command and is
    not file context, so it is ignored.
    """
    text = _strip_comments_keep_lines(path.read_text(encoding="utf-8"))
    syntax: list[tuple[int, str]] = []
    project_imports: list[str] = []
    for lineno, line in enumerate(text.splitlines()):
        stripped = line.strip()
        if stripped.startswith("import "):
            module = stripped.removeprefix("import ").strip()
            if module in project_modules:
                project_imports.append(module)
            continue
        match = _LOCAL_SYNTAX_RE.match(stripped)
        if match:
            kind = _LOCAL_SYNTAX_KIND_RE.match(stripped).group(1)
            if kind == "set_option" and re.search(r"(?:^|\s)in(?:\s|$)", stripped):
                continue
            syntax.append((lineno, kind))
    return syntax, project_imports


def _module_local_syntax(
    module: str,
    commands: dict[str, tuple[list[tuple[int, str]], list[str]]],
    own_upto_line: int | None = None,
) -> list[str]:
    """Command kinds of the project-local syntax context for ``module``.

    The module's own commands count only up to ``own_upto_line`` (a command
    cannot affect declarations earlier in the file); transitively imported
    project modules contribute all of theirs, since their commands are
    elaborated at import time.
    """
    seen: set[str] = set()
    ordered: list[str] = []
    stack = [module]
    first = True
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        syntax, imports = commands.get(current, ([], []))
        for lineno, kind in syntax:
            if first and own_upto_line is not None and lineno >= own_upto_line:
                continue
            if kind not in ordered:
                ordered.append(kind)
        first = False
        stack.extend(reversed(imports))
    return ordered


def parse_project(project_dir: Path, exclude: tuple[Path, ...] = ()) -> dict[str, LeanDecl]:
    """Parse every Lean source file of the project, keyed by full name."""
    project_dir = project_dir.resolve()
    excluded = tuple(path.resolve() for path in exclude)
    decls: dict[str, LeanDecl] = {}
    source_files: list[Path] = []
    for path in sorted(project_dir.rglob("*.lean")):
        if any(path.is_relative_to(directory) for directory in excluded):
            continue
        relative_parts = path.relative_to(project_dir).parts
        if any(part in _EXCLUDED_DIRS for part in relative_parts):
            continue
        source_files.append(path)
    project_modules = {
        ".".join(path.relative_to(project_dir).with_suffix("").parts)
        for path in source_files
    }
    commands = {
        ".".join(path.relative_to(project_dir).with_suffix("").parts):
            _module_local_commands(path, project_modules)
        for path in source_files
    }
    for path in source_files:
        module = ".".join(path.relative_to(project_dir).with_suffix("").parts)
        for decl in _parse_file(path, project_modules):
            decl.module = module
            decl.local_syntax = _module_local_syntax(module, commands, decl.line)
            decls[decl.full_name] = decl
    return decls
