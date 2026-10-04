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

from .game_model import LeanContextCommand, LeanDecl, LeanNotation

_EXCLUDED_DIRS = {
    ".lake",
    ".git",
    "build",
    "docbuild",
    "blueprint",
    "home_page",
}

_MODS = r"(?:private|protected|noncomputable|partial|scoped|local)"

_DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"((?:" + _MODS + r"\s+)*)"
    r"(def|theorem|lemma|abbrev|instance|structure|class)\s+([A-Za-z_][\w'.]*)",
)

_ANON_INSTANCE_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"((?:" + _MODS + r"\s+)*)instance(?=\s*[:(\[{⦃])",
)

_MODIFIER_LINE_RE = re.compile(_MODS + r"\s*")

_SUPPORTED_INSTANCE_MODS = frozenset({"local", "private", "noncomputable", "partial"})

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
    end_line: int
    kind: str
    namespace: str
    scope: tuple[str, ...]
    source_text: str
    modifiers: tuple[str, ...]
    notation: _NotationCandidate | None
    supported: bool = False
    target_line: int | None = None


@dataclass(frozen=True)
class _ModuleContext:
    commands: tuple[_LocalCommand, ...]
    project_imports: tuple[str, ...]
    external_imports: tuple[str, ...]
    source_path: str


_BOUNDARY_RE = re.compile(
    r"^(?:@\[|/--|--|namespace\b|end\b|section\b|open\b|variable\b|import\b|"
    + _MODS + r"\s*$|"
    + _LOCAL_SYNTAX_RE.pattern
    + r"|(?:" + _MODS + r"\s+)*"
    r"(?:def|theorem|lemma|abbrev|instance|structure|class|example)\b)"
)

_OPEN, _CLOSE = "([{⟨", ")]}⟩"

_COMMAND_LOCAL_IN_RE = re.compile(r"(?:^|\s)in(?:\s|$)")
_INLINE_COMMENT_RE = re.compile(r"/-.*?-/")

def _has_command_local_in(line: str) -> bool:
    code = _INLINE_COMMENT_RE.sub("", line.split("--", 1)[0])
    return _COMMAND_LOCAL_IN_RE.search(code) is not None


def _split_signature(decl_text: str, keyword: str, name: str) -> tuple[str, str | None]:
    """Split a declaration into (signature, proof) at the top-level ``:=``."""
    header_re = re.compile(
        r"^(?:@[\s\S]*?\]\s*)?(?:(?:private|protected|noncomputable|partial|scoped|local)\s+)*"
        + keyword
        + r"\s+"
        + re.escape(name)
    )
    match = header_re.match(decl_text)
    if not match:
        raise LeanParseError(f"cannot re-match declaration header of {name}")
    return _split_body(decl_text[match.end():])


def _split_body(rest: str) -> tuple[str, str | None]:
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


def _match_decl_header(line: str) -> tuple[str, str | None, tuple[str, ...]] | None:
    match = _DECL_RE.match(line)
    if match is not None:
        return match.group(2), match.group(3), tuple(match.group(1).split())
    match = _ANON_INSTANCE_RE.match(line)
    if match is not None:
        return "instance", None, tuple(match.group(1).split())
    return None


def _instance_supported(modifiers: tuple[str, ...], proof: str | None, block: str) -> bool:
    return (
        proof is not None
        and not block.lstrip().startswith("@[")
        and set(modifiers) <= _SUPPORTED_INSTANCE_MODS
    )


def _parse_file(
    path: Path,
    project_modules: AbstractSet[str] = frozenset(),
    module: str = "",
) -> list[LeanDecl]:
    lines = path.read_text(encoding="utf-8").splitlines()
    slug = "m" + (module or path.with_suffix("").as_posix()).encode("utf-8").hex()
    decls: list[LeanDecl] = []
    seen_names: dict[str, tuple[int, str]] = {}
    ns_stack: list[tuple[str, str | None, int]] = []  # (kind, name)
    var_stack: list[tuple[list[str], list[str]]] = []  # saved `variable` lines per section
    active_vars: list[str] = []  # currently active `variable` lines
    file_imports: list[str] = []  # external imports (Mathlib.* etc.)
    active_opens: list[str] = []  # active `open` statements
    attr_start: int | None = None
    attr_depth = 0

    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if attr_start is not None and attr_depth > 0:
            attr_depth += stripped.count("[") - stripped.count("]")
            i += 1
            continue
        if stripped.startswith("@["):
            depth = stripped.count("[") - stripped.count("]")
            tail = stripped[stripped.rfind("]") + 1 :].strip() if depth <= 0 else ""
            if depth > 0 or not tail:
                if attr_start is None:
                    attr_start = i
                attr_depth = depth
                i += 1
                continue
        if stripped.startswith("import "):
            imported_module = stripped.removeprefix("import ").strip()
            if imported_module not in project_modules:
                file_imports.append(imported_module)
            attr_start = None
            i += 1
            continue
        if stripped.startswith("open "):
            if not _has_command_local_in(stripped):
                active_opens.append(stripped)
            attr_start = None
            i += 1
            continue
        if stripped.startswith("namespace "):
            ns_stack.append(("ns", stripped.removeprefix("namespace ").strip(), i))
            var_stack.append((list(active_vars), list(active_opens)))
            attr_start = None
            i += 1
            continue
        if stripped == "section" or stripped.startswith("section "):
            ns_stack.append(
                ("sec", stripped.removeprefix("section").strip() or None, i)
            )
            var_stack.append((list(active_vars), list(active_opens)))
            attr_start = None
            i += 1
            continue
        if stripped == "end" or stripped.startswith("end "):
            if ns_stack:
                ns_stack.pop()
                active_vars, active_opens = var_stack.pop()
            attr_start = None
            i += 1
            continue
        if stripped.startswith("variable "):
            if not _has_command_local_in(stripped):
                active_vars.append(stripped)
            attr_start = None
            i += 1
            continue

        found = _match_decl_header(line) if not line[:1].isspace() else None
        header = i
        if found is None and _MODIFIER_LINE_RE.fullmatch(stripped):
            k = i
            while (
                k + 1 < len(lines)
                and _MODIFIER_LINE_RE.fullmatch(lines[k + 1].strip())
            ):
                k += 1
            if (
                k + 1 < len(lines)
                and not lines[k + 1][:1].isspace()
                and _match_decl_header(lines[k + 1])
            ):
                header = k + 1
                found = _match_decl_header(lines[header])
        if found:
            keyword, name, modifiers = found
            modifiers = tuple(
                word
                for modifier_line in lines[i:header]
                for word in modifier_line.split()
            ) + modifiers
            j = header + 1
            while j < len(lines):
                nxt = lines[j]
                if nxt.strip() and not nxt[:1].isspace() and _BOUNDARY_RE.match(nxt):
                    break
                j += 1
            block_start = attr_start if attr_start is not None else i
            attr_start = None
            block = "\n".join(lines[block_start:j]).rstrip()
            namespace = ".".join(n for kind, n, _ in ns_stack if kind == "ns" and n)
            scope = tuple(
                f"{kind}:{n or '_'}@{ln}" for kind, n, ln in ns_stack
            )
            if name is None:
                match = re.search(r"\binstance\b", block)
                signature, proof = _split_body(block[match.end():])
                name = f"_instance_{slug}_l{i}"
            else:
                signature, proof = _split_signature(block, keyword, name)
            if keyword == "instance" and not _instance_supported(
                modifiers, proof, block
            ):
                i = j
                continue
            if name.startswith("_root_."):
                resolved = name.removeprefix("_root_.")
                namespace, _, name = resolved.rpartition(".")
                full_name = resolved
            else:
                full_name = f"{namespace}.{name}" if namespace else name
            if full_name in seen_names and (
                name.startswith("_instance_m")
                or seen_names[full_name][1].startswith("_instance_m")
            ):
                raise LeanParseError(
                    f"{path}:{i + 1}: declaration name {full_name} collides "
                    f"with a declaration at line {seen_names[full_name][0] + 1}"
                )
            seen_names[full_name] = (i, name)
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
                    modifiers=modifiers,
                    scope=scope,
                )
            )
            i = j
            continue
        if (
            stripped
            and not stripped.startswith("--")
            and not _MODIFIER_LINE_RE.fullmatch(stripped)
        ):
            attr_start = None
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


_COMMAND_KIND_RE = re.compile(r"^((?:" + _MODS + r"\s+)*)([A-Za-z_][\w']*)")

_FILE_LOCAL_KINDS = frozenset({"set_option"})


def _command_local_target(lines: list[str], lineno: int, path: Path) -> int:
    k = lineno + 1
    while k < len(lines):
        stripped = lines[k].strip()
        if not stripped:
            k += 1
            continue
        if stripped.startswith("@["):
            depth = stripped.count("[") - stripped.count("]")
            tail = (
                stripped[stripped.rfind("]") + 1 :].strip() if depth <= 0 else ""
            )
            if depth > 0 or not tail:
                while depth > 0 and k + 1 < len(lines):
                    k += 1
                    depth += lines[k].count("[") - lines[k].count("]")
                if depth <= 0:
                    k += 1
                continue
            return k
        if not lines[k][:1].isspace():
            return k
        break
    raise LeanParseError(
        f"{path}:{lineno + 1}: cannot determine the source command affected "
        "by command-local `in`"
    )


def _command_block(lines: list[str], lineno: int) -> tuple[str, int]:
    end = lineno + 1
    while end < len(lines) and lines[end].strip() and lines[end][:1].isspace():
        end += 1
    return "\n".join(lines[lineno:end]).rstrip(), end - 1


def _module_local_commands(
    path: Path, module: str, source_path: str, project_modules: AbstractSet[str]
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
    ns_stack: list[tuple[str, str, int]] = []
    raw_lines = text.splitlines()
    pending_mods: list[str] = []
    attr_start: int | None = None
    attr_depth = 0
    lineno = 0
    while lineno < len(raw_lines):
        line = raw_lines[lineno]
        stripped = line.strip()
        code = stripped
        if attr_start is not None and attr_depth > 0:
            attr_depth += stripped.count("[") - stripped.count("]")
            lineno += 1
            continue
        if stripped.startswith("@["):
            depth = stripped.count("[") - stripped.count("]")
            tail = stripped[stripped.rfind("]") + 1 :].strip() if depth <= 0 else ""
            if depth > 0 or not tail:
                if attr_start is None:
                    attr_start = lineno
                attr_depth = depth
                lineno += 1
                continue
            code = tail
        if stripped and _MODIFIER_LINE_RE.fullmatch(stripped):
            pending_mods.extend(stripped.split())
            lineno += 1
            continue
        if stripped:
            hold, pending_mods = pending_mods, []
        else:
            hold = []
        if code.startswith("import "):
            imported_module = code.removeprefix("import ").strip()
            if imported_module in project_modules:
                project_imports.append(imported_module)
            else:
                external_imports.append(imported_module)
            attr_start = None
            lineno += 1
            continue
        if code.startswith("namespace "):
            name = code.removeprefix("namespace ").strip()
            ns_stack.append(("ns", name, lineno))
            namespace = ".".join(
                part for kind, part, _ in ns_stack if kind == "ns" and part
            )
            attr_start = None
            lineno += 1
            continue
        if code == "section" or code.startswith("section "):
            name = code.removeprefix("section").strip()
            ns_stack.append(("sec", name, lineno))
            attr_start = None
            lineno += 1
            continue
        if code == "end" or code.startswith("end "):
            if ns_stack:
                ns_stack.pop()
            namespace = ".".join(
                part for kind, part, _ in ns_stack if kind == "ns" and part
            )
            attr_start = None
            lineno += 1
            continue
        scope = tuple(
            f"{kind}:{name or '_'}@{ln}" for kind, name, ln in ns_stack
        )
        if code.startswith(("open ", "variable ")):
            in_match = _COMMAND_LOCAL_IN_RE.search(code)
            target_line = None
            if in_match is not None:
                target_line = (
                    lineno
                    if code[in_match.end() :].strip()
                    else _command_local_target(raw_lines, lineno, path)
                )
            commands.append(
                _LocalCommand(
                    module=module,
                    line=lineno,
                    end_line=lineno,
                    kind=code.split(None, 1)[0],
                    namespace=namespace,
                    scope=scope,
                    source_text=stripped,
                    modifiers=tuple(hold),
                    notation=None,
                    supported=in_match is None,
                    target_line=target_line,
                )
            )
            hold = []
            attr_start = None
            lineno += 1
            continue
        match = _LOCAL_SYNTAX_RE.match(code)
        is_instance = False
        if match is None and not line[:1].isspace():
            head = _COMMAND_KIND_RE.match(code)
            if head is not None and head.group(2) == "instance":
                is_instance = True
        if match is None and not is_instance:
            if stripped:
                attr_start = None
            lineno += 1
            continue
        head = _COMMAND_KIND_RE.match(code)
        modifiers = tuple(hold) + tuple(head.group(1).split())
        kind = "instance" if is_instance else head.group(2)
        if kind == "set_option" and re.search(r"(?:^|\s)in(?:\s|$)", code):
            attr_start = None
            lineno += 1
            continue
        source_start = attr_start if attr_start is not None else lineno
        body_text, end_line = _command_block(raw_lines, lineno)
        source_text = "\n".join(raw_lines[source_start : end_line + 1]).rstrip()
        attr_start = None
        supported = False
        notation = None
        if kind == "notation" and set(modifiers) <= {"local"}:
            notation_line = re.sub(
                r"^(?:" + _MODS + r"\s+)*", "", code
            )
            next_line = next(
                (
                    raw_lines[k]
                    for k in range(lineno + 1, len(raw_lines))
                    if raw_lines[k].strip()
                ),
                "",
            )
            has_continuation = bool(next_line and next_line[:1].isspace())
            notation = _parse_plain_notation(
                notation_line, lineno, namespace, has_continuation
            )
            supported = notation is not None
        elif is_instance:
            rest = body_text[re.search(r"\binstance\b", body_text).end():]
            _, proof = _split_body(rest)
            supported = _instance_supported(modifiers, proof, source_text)
        commands.append(
            _LocalCommand(
                module=module,
                line=source_start,
                end_line=end_line,
                kind=kind,
                namespace=namespace,
                scope=scope,
                source_text=source_text,
                modifiers=modifiers,
                notation=notation,
                supported=supported,
            )
        )
        lineno = end_line + 1
    return _ModuleContext(
        commands=tuple(commands),
        project_imports=tuple(project_imports),
        external_imports=tuple(external_imports),
        source_path=source_path,
    )


def _context_modules(
    module: str, contexts: dict[str, _ModuleContext]
) -> list[tuple[str, bool]]:
    ordered: list[tuple[str, bool]] = []
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
        ordered.append((current, own))

    visit(module, True)
    return ordered


def _scope_prefix(inner: tuple[str, ...], outer: tuple[str, ...]) -> bool:
    return len(inner) <= len(outer) and outer[: len(inner)] == inner


def _opened_namespaces(decl: LeanDecl) -> tuple[set[str], set[str]]:
    opened: set[str] = set()
    scoped_opened: set[str] = set()
    for open_stmt in decl.opens:
        scoped = False
        for token in open_stmt.split()[1:]:
            if token == "scoped":
                scoped = True
                continue
            if token in ("noncomputable", "private"):
                continue
            if token.startswith("(") or token in ("hiding", "renaming", "in"):
                break
            if re.fullmatch(_ASCII_IDENT + r"(?:\." + _ASCII_IDENT + r")*", token):
                (scoped_opened if scoped else opened).add(token)
            else:
                break
    return opened, scoped_opened


def _namespace_visible(required: str, decl: LeanDecl, opened: set[str]) -> bool:
    if not required:
        return True
    return (
        decl.namespace == required
        or decl.namespace.startswith(required + ".")
        or required in opened
    )


def _command_visible(
    command: _LocalCommand,
    own: bool,
    decl: LeanDecl,
    opened: set[str],
    scoped_opened: set[str],
) -> bool:
    modifiers = set(command.modifiers)
    if own:
        if command.line >= decl.line:
            return False
        if command.target_line is not None:
            return command.target_line == decl.line
        if (
            "local" in modifiers
            or command.kind in _FILE_LOCAL_KINDS
            or command.kind in ("open", "variable")
        ):
            return _scope_prefix(command.scope, decl.scope)
        if "scoped" in modifiers:
            return _scope_prefix(command.scope, decl.scope) or _namespace_visible(
                command.namespace, decl, scoped_opened
            )
        return True
    if (
        command.target_line is not None
        or "local" in modifiers
        or command.kind in _FILE_LOCAL_KINDS
        or command.kind in ("open", "variable")
    ):
        return False
    if "scoped" in modifiers:
        return _namespace_visible(command.namespace, decl, scoped_opened)
    return True


def _instance_visible(
    inst: LeanDecl, own: bool, decl: LeanDecl, scoped_opened: set[str]
) -> bool:
    modifiers = set(inst.modifiers)
    if "local" in modifiers:
        return (
            own
            and inst.line < decl.line
            and _scope_prefix(inst.scope, decl.scope)
        )
    if own:
        return inst.line < decl.line
    if "scoped" in modifiers:
        return _namespace_visible(inst.namespace, decl, scoped_opened)
    return True


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
    if notation.explicit_root or "." in notation.target:
        return notation.target
    return None


def _module_local_syntax(
    module: str,
    contexts: dict[str, _ModuleContext],
    decls: dict[str, LeanDecl],
    decl: LeanDecl,
    instances_by_module: dict[str, list[LeanDecl]],
) -> tuple[list[str], list[LeanNotation], tuple[LeanContextCommand, ...], list[LeanDecl]]:
    syntax: list[str] = []
    notations: list[LeanNotation] = []
    context: list[LeanContextCommand] = []
    instances: list[LeanDecl] = []
    seen_instances: set[str] = set()
    patterns: dict[tuple[tuple[str, str], ...], str] = {}
    ambiguous = False
    opened, scoped_opened = _opened_namespaces(decl)
    for current, own in _context_modules(module, contexts):
        module_context = contexts[current]
        source_path = module_context.source_path
        for command in module_context.commands:
            if not _command_visible(command, own, decl, opened, scoped_opened):
                continue
            supported = command.supported
            if command.kind == "notation" and command.notation is not None:
                target = _resolve_notation_target(command.notation, decls)
                if target is not None:
                    key = _canonical_notation_pattern(command.notation.pattern)
                    previous = patterns.get(key)
                    if previous is None:
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
                    elif previous != target:
                        supported = False
                        ambiguous = True
                else:
                    supported = False
            context.append(
                LeanContextCommand(
                    module=command.module,
                    source_path=source_path,
                    line=command.line,
                    end_line=command.end_line,
                    namespace=command.namespace,
                    scope=command.scope,
                    kind=command.kind,
                    source_text=command.source_text,
                    exported=not (
                        "local" in command.modifiers
                        or command.kind in _FILE_LOCAL_KINDS
                        or command.kind in ("open", "variable")
                    ),
                    supported=supported,
                )
            )
            if not supported and command.kind not in syntax:
                syntax.append(command.kind)
        for inst in instances_by_module.get(current, ()):
            if not _instance_visible(inst, own, decl, scoped_opened):
                continue
            if inst.full_name not in seen_instances:
                seen_instances.add(inst.full_name)
                instances.append(inst)
    if ambiguous and "notation" not in syntax:
        syntax.append("notation")
    return syntax, notations, tuple(context), instances


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
    project_modules = {}
    module_names = {}
    for path in source_files:
        module = ".".join(path.relative_to(project_dir).with_suffix("").parts)
        project_modules[module] = path
        module_names[path] = module
    parsed_by_module: dict[str, list[LeanDecl]] = {}
    for path in source_files:
        module = module_names[path]
        source_path = path.relative_to(project_dir).as_posix()
        module_decls = _parse_file(path, set(project_modules), module)
        for decl in module_decls:
            decl.module = module
            decl.source_path = source_path
            if decl.full_name in decls and (
                decl.name.startswith("_instance_m")
                or decls[decl.full_name].name.startswith("_instance_m")
            ):
                previous = decls[decl.full_name]
                raise LeanParseError(
                    f"{source_path}:{decl.line + 1}: declaration name "
                    f"{decl.full_name} collides with module "
                    f"{previous.module}:{previous.line + 1}"
                )
            decls[decl.full_name] = decl
        parsed_by_module[module] = module_decls
    contexts = {}
    for path in source_files:
        module = module_names[path]
        source_path = path.relative_to(project_dir).as_posix()
        contexts[module] = _module_local_commands(
            path, module, source_path, set(project_modules)
        )
    external_imports = _module_external_imports(contexts)
    instances_by_module = {
        module: [d for d in module_decls if d.keyword == "instance"]
        for module, module_decls in parsed_by_module.items()
    }
    for module, module_decls in parsed_by_module.items():
        for decl in module_decls:
            decl.imports = external_imports.get(module, decl.imports)
            (
                decl.local_syntax,
                decl.notations,
                decl.context,
                decl.instances,
            ) = _module_local_syntax(
                module, contexts, decls, decl, instances_by_module
            )
    return decls
