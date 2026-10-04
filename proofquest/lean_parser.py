"""Text-level extraction of declarations from Lean 4 source files.

This intentionally supports only the regular declaration style found in
blueprint-driven projects (plain ``def``/``theorem``/``lemma`` with binders
and a ``:=``/``:= by`` body). It does not handle ``where`` clauses, mutual
blocks, or exotic notations in signatures.
"""

from __future__ import annotations

import re
from collections.abc import Set as AbstractSet
from dataclasses import dataclass
from pathlib import Path

from .game_model import LeanDecl, LeanNotation

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

_ASCII_IDENT = r"[A-Za-z_][A-Za-z0-9_']*"
_QUALIFIED_IDENT = _ASCII_IDENT + r"(?:\." + _ASCII_IDENT + r")*"
_NOTATION_RE = re.compile(r"^notation\s+(.+?)\s*=>\s*(.+)$")
_NOTATION_TOKEN_RE = re.compile(r'"((?:\\.|[^"\\])*)"|(' + _ASCII_IDENT + r")")
_NOTATION_TARGET_RE = re.compile(
    r"^(_root_\.)?(" + _QUALIFIED_IDENT + r")((?:\s+" + _ASCII_IDENT + r")*)\s*$"
)


@dataclass(frozen=True)
class _NotationCandidate:
    line: int
    namespace: str
    pattern: str
    target: str
    arguments: tuple[str, ...]
    explicit_root: bool


@dataclass(frozen=True)
class _LocalCommand:
    module: str
    line: int
    kind: str
    namespace: str
    notation: _NotationCandidate | None


@dataclass(frozen=True)
class _ModuleContext:
    commands: tuple[_LocalCommand, ...]
    project_imports: tuple[str, ...]
    external_imports: tuple[str, ...]


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


def _parse_plain_notation(
    line: str, lineno: int, namespace: str, has_continuation: bool
) -> _NotationCandidate | None:
    if has_continuation:
        return None
    match = _NOTATION_RE.fullmatch(line)
    if match is None:
        return None
    pattern, rhs = match.group(1).strip(), match.group(2).strip()
    pos = 0
    literal_count = 0
    arguments: list[str] = []
    for token in _NOTATION_TOKEN_RE.finditer(pattern):
        if pattern[pos:token.start()].strip():
            return None
        if token.group(1) is not None:
            literal_count += 1
        else:
            arguments.append(token.group(2))
        pos = token.end()
    if pattern[pos:].strip() or literal_count == 0 or len(arguments) != len(set(arguments)):
        return None
    target_match = _NOTATION_TARGET_RE.fullmatch(rhs)
    if target_match is None:
        return None
    target = target_match.group(2)
    target_arguments = tuple(target_match.group(3).split())
    if target_arguments != tuple(arguments):
        return None
    return _NotationCandidate(
        line=lineno,
        namespace=namespace,
        pattern=pattern,
        target=target,
        arguments=tuple(arguments),
        explicit_root=target_match.group(1) is not None,
    )


def _module_local_commands(
    path: Path, module: str, project_modules: AbstractSet[str]
) -> _ModuleContext:
    """``((line, command kind) list, project module imports)`` of one file.

    Complements ``_parse_file`` (which only sees files through their
    declarations): a file may define notation yet declare nothing. Only the
    command *kind* (``notation``, ``set_option``, ...) is kept, never the raw
    command text. ``set_option ... in`` applies to a single command and is
    not file context, so it is ignored.
    """
    text = _strip_comments_keep_lines(path.read_text(encoding="utf-8"))
    commands: list[_LocalCommand] = []
    project_imports: list[str] = []
    external_imports: list[str] = []
    namespace = ""
    ns_stack: list[tuple[str, str]] = []
    raw_lines = text.splitlines()
    for lineno, line in enumerate(raw_lines):
        stripped = line.strip()
        if stripped.startswith("import "):
            imported_module = stripped.removeprefix("import ").strip()
            if imported_module in project_modules:
                project_imports.append(imported_module)
            else:
                external_imports.append(imported_module)
            continue
        if stripped.startswith("namespace "):
            name = stripped.removeprefix("namespace ").strip()
            ns_stack.append(("ns", name))
            namespace = ".".join(
                part for kind, part in ns_stack if kind == "ns" and part
            )
            continue
        if stripped == "section" or stripped.startswith("section "):
            ns_stack.append(("sec", ""))
            continue
        if stripped == "end" or stripped.startswith("end "):
            if ns_stack:
                ns_stack.pop()
            namespace = ".".join(
                part for kind, part in ns_stack if kind == "ns" and part
            )
            continue
        match = _LOCAL_SYNTAX_RE.match(stripped)
        if match:
            kind = _LOCAL_SYNTAX_KIND_RE.match(stripped).group(1)
            if kind == "set_option" and re.search(r"(?:^|\s)in(?:\s|$)", stripped):
                continue
            next_line = next(
                (raw_lines[k] for k in range(lineno + 1, len(raw_lines)) if raw_lines[k].strip()),
                "",
            )
            has_continuation = bool(next_line and next_line[:1].isspace())
            commands.append(
                _LocalCommand(
                    module=module,
                    line=lineno,
                    kind=kind,
                    namespace=namespace,
                    notation=(
                        _parse_plain_notation(stripped, lineno, namespace, has_continuation)
                        if stripped.startswith("notation ")
                        else None
                    ),
                )
            )
    return _ModuleContext(
        commands=tuple(commands),
        project_imports=tuple(project_imports),
        external_imports=tuple(external_imports),
    )


def _module_context(
    module: str,
    contexts: dict[str, _ModuleContext],
    own_upto_line: int,
) -> list[_LocalCommand]:
    ordered: list[_LocalCommand] = []
    seen: set[str] = set()

    def visit(current: str, own: bool) -> None:
        if current in seen:
            return
        seen.add(current)
        context = contexts.get(current)
        if context is None:
            return
        for imported in context.project_imports:
            visit(imported, False)
        for command in context.commands:
            if not own or command.line < own_upto_line:
                ordered.append(command)

    visit(module, True)
    return ordered


def _canonical_notation_pattern(pattern: str) -> tuple[tuple[str, str], ...]:
    tokens: list[tuple[str, str]] = []
    argument = 0
    for match in _NOTATION_TOKEN_RE.finditer(pattern):
        if match.group(1) is None:
            argument += 1
            tokens.append(("argument", str(argument)))
        else:
            tokens.append(("literal", match.group(1)))
    return tuple(tokens)


def _resolve_notation_target(
    notation: _NotationCandidate, decls: dict[str, LeanDecl]
) -> str | None:
    candidates = []
    if notation.explicit_root:
        candidates.append(notation.target)
    else:
        if notation.namespace:
            parts = notation.namespace.split(".")
            for i in range(len(parts), 0, -1):
                candidates.append(".".join(parts[:i]) + "." + notation.target)
        candidates.append(notation.target)
    for candidate in candidates:
        decl = decls.get(candidate)
        if decl is not None:
            return decl.full_name if decl.is_definition else None
    return None


def _module_local_syntax(
    module: str,
    contexts: dict[str, _ModuleContext],
    decls: dict[str, LeanDecl],
    own_upto_line: int,
) -> tuple[list[str], list[LeanNotation]]:
    syntax: list[str] = []
    notations: list[LeanNotation] = []
    patterns: dict[tuple[tuple[str, str], ...], str] = {}
    ambiguous = False
    for command in _module_context(module, contexts, own_upto_line):
        if command.kind != "notation" or command.notation is None:
            if command.kind not in syntax:
                syntax.append(command.kind)
            continue
        target = _resolve_notation_target(command.notation, decls)
        if target is None:
            if command.kind not in syntax:
                syntax.append(command.kind)
            continue
        key = _canonical_notation_pattern(command.notation.pattern)
        previous = patterns.get(key)
        if previous is not None:
            if previous != target:
                ambiguous = True
            continue
        patterns[key] = target
        notation = LeanNotation(
            module=command.module,
            line=command.line,
            namespace=command.notation.namespace,
            pattern=command.notation.pattern,
            target=target,
            arguments=command.notation.arguments,
        )
        if notation not in notations:
            notations.append(notation)
    if ambiguous and "notation" not in syntax:
        syntax.append("notation")
    return syntax, notations


def _generated_roots(project_dir: Path) -> list[Path]:
    roots: list[Path] = []
    for game_root in sorted(
        path for path in project_dir.rglob("Game.lean") if path.is_file()
    ):
        root = game_root.parent
        markers = (
            root / "Game" / "Metadata.lean",
            root / "Game" / "Generated" / "Defs.lean",
            root / "lakefile.lean",
            root / "lean-toolchain",
        )
        if not all(marker.is_file() for marker in markers):
            continue
        if "MakeGame" in game_root.read_text(encoding="utf-8", errors="replace"):
            roots.append(root)
    return roots


def _module_external_imports(
    contexts: dict[str, _ModuleContext]
) -> dict[str, list[str]]:
    resolved: dict[str, list[str]] = {}
    visiting: set[str] = set()

    def visit(module: str) -> list[str]:
        if module in resolved:
            return resolved[module]
        if module in visiting:
            return []
        visiting.add(module)
        context = contexts.get(module)
        imports = list(context.external_imports) if context else []
        if context:
            for imported in context.project_imports:
                for external in visit(imported):
                    if external not in imports:
                        imports.append(external)
        visiting.remove(module)
        resolved[module] = imports
        return imports

    for module in contexts:
        visit(module)
    return resolved


def parse_project(project_dir: Path, exclude: tuple[Path, ...] = ()) -> dict[str, LeanDecl]:
    """Parse every Lean source file of the project, keyed by full name."""
    project_dir = project_dir.resolve()
    excluded = tuple(path.resolve() for path in exclude)
    generated_roots = _generated_roots(project_dir)
    decls: dict[str, LeanDecl] = {}
    source_files: list[Path] = []
    for path in sorted(project_dir.rglob("*.lean")):
        if any(path.is_relative_to(directory) for directory in excluded):
            continue
        if any(path.is_relative_to(directory) for directory in generated_roots):
            continue
        relative_parts = path.relative_to(project_dir).parts
        if any(part in _EXCLUDED_DIRS for part in relative_parts):
            continue
        source_files.append(path)
    project_modules = {
        ".".join(path.relative_to(project_dir).with_suffix("").parts)
        for path in source_files
    }
    contexts = {}
    for path in source_files:
        module = ".".join(path.relative_to(project_dir).with_suffix("").parts)
        contexts[module] = _module_local_commands(path, module, project_modules)
    external_imports = _module_external_imports(contexts)
    parsed_by_module: dict[str, list[LeanDecl]] = {}
    for path in source_files:
        module = ".".join(path.relative_to(project_dir).with_suffix("").parts)
        module_decls = _parse_file(path, project_modules)
        for decl in module_decls:
            decl.module = module
            decl.imports = external_imports.get(module, decl.imports)
            decls[decl.full_name] = decl
        parsed_by_module[module] = module_decls
    for module, module_decls in parsed_by_module.items():
        for decl in module_decls:
            decl.local_syntax, decl.notations = _module_local_syntax(
                module, contexts, decls, decl.line
            )
    return decls
