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
    r"(def|theorem|lemma|abbrev|instance)\s+([A-Za-z_][\w'.]*)",
)

_BOUNDARY_RE = re.compile(
    r"^(?:@\[|/--|--|namespace\b|end\b|section\b|open\b|variable\b|import\b|"
    r"(?:(?:private|protected|noncomputable|partial|scoped)\s+)*"
    r"(?:def|theorem|lemma|abbrev|instance|example)\b)"
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
        elif depth == 0 and rest[i:i+3] == "let" and (i + 3 >= len(rest) or not rest[i+3].isalnum() and rest[i+3] != "_"):
            skip_next_assign = True
        elif depth == 0 and rest.startswith(":=", i):
            if skip_next_assign:
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

        match = _DECL_RE.match(line)
        if match and not line[:1].isspace():
            keyword, name = match.group(1), match.group(2)
            j = i + 1
            while j < len(lines):
                nxt = lines[j]
                if nxt.strip() and not nxt[:1].isspace() and _BOUNDARY_RE.match(nxt):
                    break
                j += 1
            block = "\n".join(lines[i:j]).rstrip()
            namespace = ".".join(n for kind, n in ns_stack if kind == "ns" and n)
            signature, proof = _split_signature(block, keyword, name)
            decls.append(
                LeanDecl(
                    keyword=keyword,
                    name=name,
                    full_name=f"{namespace}.{name}" if namespace else name,
                    namespace=namespace,
                    signature=signature,
                    proof=proof,
                    source_text=block,
                    variables=list(active_vars),
                    imports=list(file_imports),
                    opens=list(active_opens),
                )
            )
            i = j
            continue
        i += 1
    return decls


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
    for path in source_files:
        for decl in _parse_file(path, project_modules):
            decls[decl.full_name] = decl
    return decls
