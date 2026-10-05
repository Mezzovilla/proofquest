"""Text-level extraction of declarations from Lean 4 source files.

This intentionally supports only the regular declaration style found in
blueprint-driven projects (plain ``def``/``theorem``/``lemma`` with binders
and a ``:=``/``:= by`` body). It does not handle ``where`` clauses, mutual
blocks, or exotic notations in signatures.
"""

from __future__ import annotations

import re
import textwrap
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
_UNICODE_IDENT = r"[^\W\d][\w'!?]*"
_NOTATION_RE = re.compile(r"^notation\s+(.+?)\s*=>\s*(.+)$")
_NOTATION3_RE = re.compile(r"^notation3?\s+(.+?)\s*=>\s*(.+)$")
_NOTATION_TOKEN_RE = re.compile(r'"((?:\\.|[^"\\])*)"|(' + _ASCII_IDENT + r")")
_NOTATION_TARGET_RE = re.compile(
    r"^(_root_\.)?(" + _QUALIFIED_IDENT + r")((?:\s+" + _ASCII_IDENT + r")*)\s*$"
)
_NOTATION_LITERAL_RE = re.compile(r'^"((?:\\.|[^"\\])*)"$')
_EXPRESSION_TOKEN_RE = re.compile(
    r"(?:" + _UNICODE_IDENT + r"(?:\." + _UNICODE_IDENT + r")*|\d+|[()\-])"
)
_EXPRESSION_KEYWORDS = frozenset(
    {
        "by", "where", "fun", "let", "in", "if", "then", "else", "match",
        "do", "forall", "exists", "sorry", "example", "have", "show",
        "calc", "this", "at", "with", "open", "end", "variable",
    }
)
_ATTRIBUTE_HEADER_RE = re.compile(r"^attribute\s+\[([^\]]*)\]\s*(.+)$")
_INSTANCE_ATTR_RE = re.compile(r"^(local\s+)?instance(?:\s+(\d+))?$")
_ATTR_TARGET_RE = re.compile(r"^(?:_root_\.)?" + _QUALIFIED_IDENT + r"$")


@dataclass(frozen=True)
class _NotationCandidate:
    line: int
    namespace: str
    pattern: str
    target: str
    arguments: tuple[str, ...]
    explicit_root: bool
    expression: str | None = None


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
    variables: tuple[str, ...] = ()
    opens: tuple[str, ...] = ()
    attr_targets: tuple[str, ...] = ()
    attr_action: str | None = None
    attr_priority: int | None = None


@dataclass(frozen=True)
class _ModuleContext:
    commands: tuple[_LocalCommand, ...]
    project_imports: tuple[str, ...]
    external_imports: tuple[str, ...]
    source_path: str


_SCOPE_COMMAND_RE = re.compile(
    r"^((?:" + _MODS + r"\s+)*)(namespace|section)\b(.*)$"
)

_BOUNDARY_RE = re.compile(
    r"^(?:@\[|namespace\b|end\b|section\b|open\b|variable\b|import\b|"
    r"universe\b|axiom\b|inductive\b|opaque\b|mutual\b|deriving\b|#\w|"
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
    masked = "\n".join(_masked_source(decl_text)[0])
    match = header_re.match(masked)
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


def _split_instance_where(body: str) -> tuple[str, str | None]:
    depth = 0
    comment_depth = 0
    i = 0
    n = len(body)
    while i < n:
        ch = body[i]
        if comment_depth > 0:
            if body.startswith("/-", i):
                comment_depth += 1
                i += 2
            elif body.startswith("-/", i):
                comment_depth -= 1
                i += 2
            else:
                i += 1
            continue
        if ch == '"':
            i += 1
            while i < n and body[i] != '"':
                i += 2 if body[i] == "\\" else 1
            i += 1
            continue
        if body.startswith("--", i):
            while i < n and body[i] != "\n":
                i += 1
            continue
        if body.startswith("/-", i):
            comment_depth += 1
            i += 2
            continue
        if ch in _OPEN:
            depth += 1
            i += 1
            continue
        if ch in _CLOSE:
            depth -= 1
            if depth < 0:
                break
            i += 1
            continue
        if (
            depth == 0
            and body.startswith("where", i)
            and (i == 0 or not (body[i - 1].isalnum() or body[i - 1] in "_.'"))
            and (
                i + 5 >= n
                or not (body[i + 5].isalnum() or body[i + 5] in "_.'")
            )
        ):
            fields = textwrap.dedent(body[i + 5:]).strip("\n")
            return body[:i].rstrip(), fields
        i += 1
    return body, None


def _where_record(fields: str) -> str:
    return "{\n" + _indent(fields, 2) + "\n}" if fields.strip() else "{}"


def _instance_proof(body: str) -> tuple[str, str | None]:
    signature, proof = _split_body(body)
    if proof is not None:
        return signature, proof
    signature, fields = _split_instance_where(signature)
    if fields is None:
        return signature, None
    return signature, _where_record(fields)


def _indent(text: str, spaces: int) -> str:
    pad = " " * spaces
    return "\n".join(
        pad + line if line.strip() else line for line in text.splitlines()
    )


def _parse_expression_notation(
    code: str, lineno: int, namespace: str
) -> _NotationCandidate | None:
    notation_line = re.sub(r"^(?:" + _MODS + r"\s+)*", "", code.strip())
    match = _NOTATION3_RE.match(notation_line)
    if match is None:
        return None
    pattern = match.group(1).strip()
    expression = match.group(2).strip()
    literal = _NOTATION_LITERAL_RE.fullmatch(pattern)
    if literal is None or re.fullmatch(_UNICODE_IDENT, literal.group(1)) is None:
        return None
    pos = 0
    for token in _EXPRESSION_TOKEN_RE.finditer(expression):
        if expression[pos:token.start()].strip():
            return None
        head = token.group(0).split(".")[0]
        if head in _EXPRESSION_KEYWORDS:
            return None
        pos = token.end()
    if pos == 0 or expression[pos:].strip():
        return None
    return _NotationCandidate(
        line=lineno,
        namespace=namespace,
        pattern=pattern,
        target="",
        arguments=(),
        explicit_root=False,
        expression=expression,
    )


def _parse_instance_attribute(code: str):
    match = _ATTRIBUTE_HEADER_RE.match(code.strip())
    if match is None:
        return None
    bracket = match.group(1).strip()
    rest = match.group(2).strip()
    if not rest or "[" in rest:
        return None
    action = "enable"
    local = False
    priority = None
    if bracket == "-instance":
        action = "disable"
    else:
        bracket_match = _INSTANCE_ATTR_RE.fullmatch(bracket)
        if bracket_match is None:
            return None
        local = bracket_match.group(1) is not None
        if bracket_match.group(2) is not None:
            priority = int(bracket_match.group(2))
    targets = tuple(rest.split())
    if not all(_ATTR_TARGET_RE.fullmatch(target) for target in targets):
        return None
    return action, local, priority, targets


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


def _masked_source(text: str) -> tuple[list[str], list[bool]]:
    """``text`` split into lines with comments and string contents blanked.

    ``sheltered[j]`` is True when line ``j`` begins inside a ``/-`` block
    comment or a string literal, so command-looking text there is not real.
    """
    out: list[str] = []
    sheltered: list[bool] = []
    depth = 0
    in_string = False
    i = 0
    n = len(text)
    line_start = True
    while i < n:
        if line_start:
            sheltered.append(depth > 0 or in_string)
            line_start = False
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            elif text[i] == "\n":
                out.append("\n")
                i += 1
                line_start = True
            else:
                out.append(" ")
                i += 1
            continue
        if in_string:
            if text[i] == "\\":
                out.extend("  ")
                i += 2
            elif text[i] == '"':
                out.append(" ")
                i += 1
                in_string = False
            elif text[i] == "\n":
                out.append("\n")
                i += 1
                line_start = True
            else:
                out.append(" ")
                i += 1
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            out.extend("  ")
            i += 2
            continue
        ch = text[i]
        out.append(ch)
        i += 1
        if ch == '"':
            in_string = True
        if ch == "\n":
            line_start = True
    masked_lines = "".join(out).split("\n")
    while len(sheltered) < len(masked_lines):
        sheltered.append(False)
    return masked_lines, sheltered


def _parse_file(
    path: Path,
    project_modules: AbstractSet[str] = frozenset(),
    module: str = "",
) -> list[LeanDecl]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    masked_lines, sheltered = _masked_source(text)
    slug = "m" + (module or path.with_suffix("").as_posix()).encode("utf-8").hex()
    decls: list[LeanDecl] = []
    seen_names: dict[str, tuple[int, str]] = {}
    ns_stack: list[tuple[str, str | None, int, bool]] = []
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
        code = (
            masked_lines[i].strip()
            if i < len(masked_lines)
            else stripped
        )
        if not code:
            i += 1
            continue
        if attr_start is not None and attr_depth > 0:
            attr_depth += code.count("[") - code.count("]")
            i += 1
            continue
        if code.startswith("@["):
            depth = code.count("[") - code.count("]")
            tail = code[code.rfind("]") + 1 :].strip() if depth <= 0 else ""
            if depth > 0 or not tail:
                if attr_start is None:
                    attr_start = i
                attr_depth = depth
                i += 1
                continue
        if code.startswith("import "):
            imported_module = code.removeprefix("import ").strip()
            if imported_module not in project_modules:
                file_imports.append(imported_module)
            attr_start = None
            i += 1
            continue
        if code.startswith("open "):
            if not _has_command_local_in(code):
                active_opens.append(code)
            attr_start = None
            i += 1
            continue
        scope_match = _SCOPE_COMMAND_RE.match(code)
        if scope_match is not None:
            mods, kind_word, rest = scope_match.groups()
            noncomp = "noncomputable" in mods.split()
            k = i - 1
            while (
                k >= 0
                and lines[k].strip()
                and _MODIFIER_LINE_RE.fullmatch(lines[k].strip())
            ):
                noncomp = noncomp or "noncomputable" in lines[k].split()
                k -= 1
            name = rest.strip() or None
            ns_stack.append(
                ("ns" if kind_word == "namespace" else "sec", name, i, noncomp)
            )
            var_stack.append((list(active_vars), list(active_opens)))
            attr_start = None
            i += 1
            continue
        if code == "end" or code.startswith("end "):
            if ns_stack:
                ns_stack.pop()
                active_vars, active_opens = var_stack.pop()
            attr_start = None
            i += 1
            continue
        if code.startswith("variable "):
            if not _has_command_local_in(code):
                active_vars.append(code)
            attr_start = None
            i += 1
            continue

        found = (
            _match_decl_header(masked_lines[i])
            if i < len(masked_lines) and not line[:1].isspace()
            else None
        )
        header = i
        if found is None and _MODIFIER_LINE_RE.fullmatch(code):
            k = i
            while k + 1 < len(lines):
                next_code = (
                    masked_lines[k + 1].strip()
                    if k + 1 < len(masked_lines)
                    else ""
                )
                if not next_code or _MODIFIER_LINE_RE.fullmatch(next_code):
                    k += 1
                    continue
                break
            if (
                k + 1 < len(lines)
                and k + 1 < len(masked_lines)
                and not lines[k + 1][:1].isspace()
                and _match_decl_header(masked_lines[k + 1])
            ):
                header = k + 1
                found = _match_decl_header(masked_lines[header])
        if found:
            keyword, name, modifiers = found
            modifiers = tuple(
                word
                for modifier_line in masked_lines[i:header]
                for word in modifier_line.split()
            ) + modifiers
            j = header + 1
            while j < len(lines):
                nxt = lines[j]
                nxt_code = masked_lines[j] if j < len(masked_lines) else ""
                if (
                    nxt_code.strip()
                    and not nxt_code[:1].isspace()
                    and _BOUNDARY_RE.match(nxt_code)
                ):
                    break
                if (
                    nxt.startswith("/--")
                    and not (j < len(sheltered) and sheltered[j])
                ):
                    break
                j += 1
            block_start = attr_start if attr_start is not None else i
            attr_start = None
            block = "\n".join(lines[block_start:j]).rstrip()
            namespace = ".".join(
                n for kind, n, _ln, _nc in ns_stack if kind == "ns" and n
            )
            scope = tuple(
                f"{kind}:{n or '_'}@{ln}" for kind, n, ln, _nc in ns_stack
            )
            if name is None:
                masked_block = "\n".join(_masked_source(block)[0])
                match = re.search(r"\binstance\b", masked_block)
                signature, proof = _instance_proof(block[match.end():])
                name = f"_instance_{slug}_l{i}"
            elif keyword == "instance":
                signature, proof = _split_signature(block, keyword, name)
                if proof is None:
                    signature, fields = _split_instance_where(signature)
                    if fields is not None:
                        proof = _where_record(fields)
            else:
                signature, proof = _split_signature(block, keyword, name)
            if keyword == "instance" and not _instance_supported(
                modifiers, proof, block
            ):
                i = j
                continue
            enclosing_namespace = namespace
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
                    context_namespace=enclosing_namespace,
                    noncomputable_section=any(
                        nc for _k, _n, _ln, nc in ns_stack
                    ),
                )
            )
            i = j
            continue
        if code and not _MODIFIER_LINE_RE.fullmatch(code):
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
    while end < len(lines) and (
        not lines[end].strip() or lines[end][:1].isspace()
    ):
        end += 1
    while end > lineno and not lines[end - 1].strip():
        end -= 1
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
    ns_stack: list[tuple[str, str, int, bool]] = []
    saved_env: list[tuple[list[str], list[str]]] = []
    active_vars: list[str] = []
    active_opens: list[str] = []
    raw_lines = text.splitlines()
    pending_mods: list[str] = []
    mods_start: int | None = None
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
            if mods_start is None:
                mods_start = lineno
            pending_mods.extend(stripped.split())
            lineno += 1
            continue
        if stripped:
            hold, pending_mods = pending_mods, []
            hold_mods_start, mods_start = mods_start, None
        else:
            hold = []
            hold_mods_start = None
        if code.startswith("import "):
            imported_module = code.removeprefix("import ").strip()
            if imported_module in project_modules:
                project_imports.append(imported_module)
            else:
                external_imports.append(imported_module)
            attr_start = None
            lineno += 1
            continue
        scope_match = _SCOPE_COMMAND_RE.match(code)
        if scope_match is not None:
            mods, kind_word, rest = scope_match.groups()
            noncomp = "noncomputable" in (*mods.split(), *hold)
            name = rest.strip()
            ns_stack.append(
                (
                    "ns" if kind_word == "namespace" else "sec",
                    name,
                    lineno,
                    noncomp,
                )
            )
            saved_env.append((list(active_vars), list(active_opens)))
            namespace = ".".join(
                part for kind, part, _ln, _nc in ns_stack if kind == "ns" and part
            )
            attr_start = None
            lineno += 1
            continue
        if code == "end" or code.startswith("end "):
            if ns_stack:
                ns_stack.pop()
            if saved_env:
                active_vars, active_opens = saved_env.pop()
            namespace = ".".join(
                part for kind, part, _ln, _nc in ns_stack if kind == "ns" and part
            )
            attr_start = None
            lineno += 1
            continue
        scope = tuple(
            f"{kind}:{name or '_'}@{ln}" for kind, name, ln, _nc in ns_stack
        )
        if code.startswith(("open ", "variable ")):
            kind = code.split(None, 1)[0]
            in_match = _COMMAND_LOCAL_IN_RE.search(code)
            target_line = None
            if in_match is not None:
                target_line = (
                    lineno
                    if code[in_match.end() :].strip()
                    else _command_local_target(raw_lines, lineno, path)
                )
            if in_match is None:
                source_text = stripped
                supported = True
                if kind == "open":
                    active_opens.append(stripped)
                else:
                    active_vars.append(stripped)
            else:
                source_text = stripped[: in_match.start()].rstrip()
                supported = kind == "open" and target_line != lineno
            commands.append(
                _LocalCommand(
                    module=module,
                    line=lineno,
                    end_line=lineno,
                    kind=kind,
                    namespace=namespace,
                    scope=scope,
                    source_text=source_text,
                    modifiers=tuple(hold),
                    notation=None,
                    supported=supported,
                    target_line=target_line,
                    variables=tuple(active_vars),
                    opens=tuple(active_opens),
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
        if attr_start is None and hold_mods_start is not None:
            source_start = hold_mods_start
        body_text, end_line = _command_block(raw_lines, lineno)
        source_text = "\n".join(raw_lines[source_start : end_line + 1]).rstrip()
        attr_start = None
        supported = False
        notation = None
        attr_targets: tuple[str, ...] = ()
        attr_action: str | None = None
        attr_priority: int | None = None
        if kind in ("notation", "notation3") and set(modifiers) <= {"local"}:
            next_line = next(
                (
                    raw_lines[k]
                    for k in range(lineno + 1, len(raw_lines))
                    if raw_lines[k].strip()
                ),
                "",
            )
            has_continuation = bool(next_line and next_line[:1].isspace())
            if kind == "notation":
                notation_line = re.sub(
                    r"^(?:" + _MODS + r"\s+)*", "", code
                )
                notation = _parse_plain_notation(
                    notation_line, lineno, namespace, has_continuation
                )
            if notation is None and modifiers == ("local",) and not has_continuation:
                notation = _parse_expression_notation(code, lineno, namespace)
            supported = notation is not None
        elif is_instance:
            masked_body = "\n".join(_masked_source(body_text)[0])
            rest = body_text[re.search(r"\binstance\b", masked_body).end():]
            _, proof = _instance_proof(rest)
            supported = _instance_supported(modifiers, proof, source_text)
        elif kind == "attribute" and not modifiers:
            parsed = _parse_instance_attribute(body_text)
            if parsed is not None:
                attr_action, attr_local, attr_priority, attr_targets = parsed
                if attr_local:
                    modifiers = modifiers + ("local",)
                supported = True
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
                variables=tuple(active_vars),
                opens=tuple(active_opens),
                attr_targets=attr_targets,
                attr_action=attr_action,
                attr_priority=attr_priority,
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
            if token.startswith("_root_."):
                token = token.removeprefix("_root_.")
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
            or command.attr_action == "disable"
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
        or command.attr_action == "disable"
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


def _open_ident_tokens(open_text: str) -> tuple[list[str], bool, bool]:
    tokens: list[str] = []
    scoped = False
    exotic = False
    for token in open_text.split()[1:]:
        if token == "scoped":
            scoped = True
            continue
        if token in ("noncomputable", "private"):
            continue
        if token.startswith("(") or token in ("hiding", "renaming", "in"):
            exotic = True
            break
        if re.fullmatch(_QUALIFIED_IDENT, token):
            tokens.append(token)
        else:
            exotic = True
            break
    return tokens, scoped, exotic


def _ns_interpretations(token: str, namespace: str) -> list[str]:
    if token.startswith("_root_."):
        return [token.removeprefix("_root_.")]
    out: list[str] = []
    if namespace:
        parts = namespace.split(".")
        for i in range(len(parts), 0, -1):
            out.append(".".join(parts[:i]) + "." + token)
    out.append(token)
    return out


def _open_unsafe(
    open_text: str,
    namespace: str,
    project_scopes: set[str],
    scoped_namespaces: set[str],
) -> bool:
    tokens, scoped, exotic = _open_ident_tokens(open_text)
    hits: set[str] = set()
    for token in tokens:
        hits.update(_ns_interpretations(token, namespace))
    if scoped:
        return bool(hits & scoped_namespaces)
    if exotic:
        return bool(hits & (project_scopes | scoped_namespaces))
    return False


def _canonical_open(
    open_text: str,
    namespace: str,
    context_ns: str,
    project_scopes: set[str],
) -> list[tuple[str, str, bool]] | None:
    """Rewrite an ``open`` command for replay in a declaration's context.

    Returns ``(emitted, resolution, at_root)`` triples, one per opened
    namespace token. ``emitted`` is the ``open`` line to write — at file
    root when ``at_root`` is set (outside the consuming ``namespace``
    wrapper), otherwise inside it — while ``resolution`` is the lookup-
    equivalent entry kept on the declaration. Each token is resolved against
    ``namespace``, the command's *original* namespace: a token naming a
    known project scope emits its resolved absolute name, and any other
    token keeps its original spelling only where the emitted position
    reproduces the original lookup — the command's own namespace, or a
    root-level command replayed at root (``_root_.`` is not valid in an
    ``open`` target). Anything else returns ``None``: the command cannot be
    reproduced without possibly changing resolution and must fail closed.
    """
    tokens, _scoped, exotic = _open_ident_tokens(open_text)
    if exotic or not tokens:
        if namespace == context_ns:
            return [(open_text, open_text, False)]
        return None
    lead = "open"
    for token in open_text.split()[1:]:
        if token in ("scoped", "noncomputable", "private"):
            lead += " " + token
        else:
            break
    out: list[tuple[str, str, bool]] = []
    for token in tokens:
        if token.startswith("_root_."):
            base = token.removeprefix("_root_.")
            out.append((f"{lead} {base}", f"{lead} _root_.{base}", True))
        elif namespace == context_ns:
            out.append((f"{lead} {token}", f"{lead} {token}", False))
        else:
            resolved = next(
                (
                    candidate
                    for candidate in _ns_interpretations(token, namespace)
                    if candidate in project_scopes
                ),
                None,
            )
            if resolved is not None:
                out.append(
                    (f"{lead} {resolved}", f"{lead} _root_.{resolved}", True)
                )
            elif not namespace or namespace in project_scopes:
                out.append(
                    (f"{lead} {token}", f"{lead} _root_.{token}", True)
                )
            else:
                return None
    return out


def _resolve_command_target(
    name: str, command: _LocalCommand, decls: dict[str, LeanDecl]
) -> str | None:
    if name.startswith("_root_."):
        return name
    if command.namespace:
        parts = command.namespace.split(".")
        for i in range(len(parts), 0, -1):
            candidate = ".".join(parts[:i]) + "." + name
            if candidate in decls:
                return "_root_." + candidate
    if name in decls:
        return "_root_." + name
    matches: set[str] = set()
    for open_stmt in command.opens:
        tokens, scoped, _ = _open_ident_tokens(open_stmt)
        if scoped:
            continue
        for token in tokens:
            for opened in _ns_interpretations(token, command.namespace):
                if f"{opened}.{name}" in decls:
                    matches.add(f"{opened}.{name}")
    if len(matches) > 1:
        return None
    if matches:
        return "_root_." + next(iter(matches))
    return "_root_." + name if "." in name else None


def _project_scopes(decls: dict[str, LeanDecl]) -> set[str]:
    scopes: set[str] = set()
    for decl in decls.values():
        for dotted in (decl.module, decl.namespace):
            if not dotted:
                continue
            parts = dotted.split(".")
            for i in range(1, len(parts) + 1):
                scopes.add(".".join(parts[:i]))
    return scopes


def _module_local_syntax(
    module: str,
    contexts: dict[str, _ModuleContext],
    decls: dict[str, LeanDecl],
    decl: LeanDecl,
    instances_by_module: dict[str, list[LeanDecl]],
    project_scopes: set[str],
    scoped_namespaces: set[str],
) -> tuple[list[str], list[LeanNotation], tuple[LeanContextCommand, ...], list[LeanDecl]]:
    syntax: list[str] = []
    notations: list[LeanNotation] = []
    context: list[LeanContextCommand] = []
    instances: list[LeanDecl] = []
    seen_instances: set[str] = set()
    patterns: dict[tuple[tuple[str, str], ...], str] = {}
    ambiguous = False
    opened, scoped_opened = _opened_namespaces(decl)
    decl_context_ns = (
        decl.context_namespace
        if decl.context_namespace is not None
        else decl.namespace
    )
    own_opens: list[str] = []
    target_opens: list[str] = []
    for current, own in _context_modules(module, contexts):
        module_context = contexts[current]
        source_path = module_context.source_path
        for command in module_context.commands:
            if not _command_visible(command, own, decl, opened, scoped_opened):
                continue
            supported = command.supported
            targets: tuple[str, ...] = ()
            if command.kind == "open":
                if supported and _open_unsafe(
                    command.source_text,
                    command.namespace,
                    project_scopes,
                    scoped_namespaces,
                ):
                    supported = False
                if supported:
                    canonical = _canonical_open(
                        command.source_text,
                        command.namespace,
                        decl_context_ns,
                        project_scopes,
                    )
                    if canonical is None:
                        supported = False
                    else:
                        bucket = (
                            target_opens
                            if command.target_line is not None
                            else own_opens
                        )
                        for _, resolution, _at_root in canonical:
                            if resolution not in bucket:
                                bucket.append(resolution)
            elif command.kind in ("notation", "notation3") and command.notation is not None:
                if command.notation.expression is not None:
                    resolved = command.notation.expression
                else:
                    resolved = _resolve_notation_target(command.notation, decls)
                if resolved is not None:
                    key = _canonical_notation_pattern(command.notation.pattern)
                    previous = patterns.get(key)
                    if previous is None:
                        patterns[key] = resolved
                        notation = LeanNotation(
                            module=command.module,
                            line=command.line,
                            namespace=command.notation.namespace,
                            pattern=command.notation.pattern,
                            target=resolved if command.notation.expression is None else "",
                            arguments=command.notation.arguments,
                            expression=command.notation.expression,
                            variables=command.variables,
                            opens=command.opens,
                        )
                        if notation not in notations:
                            notations.append(notation)
                    elif previous != resolved:
                        supported = False
                        ambiguous = True
                else:
                    supported = False
            elif command.kind == "instance":
                inst = next(
                    (
                        candidate
                        for candidate in instances_by_module.get(
                            command.module, ()
                        )
                        if command.line <= candidate.line <= command.end_line
                    ),
                    None,
                )
                if inst is not None:
                    targets = (inst.full_name,)
            elif command.kind == "attribute" and supported:
                resolved_targets: list[str] = []
                for target in command.attr_targets:
                    resolved_target = _resolve_command_target(
                        target, command, decls
                    )
                    if resolved_target is None:
                        supported = False
                        break
                    resolved_targets.append(resolved_target)
                targets = tuple(resolved_targets)
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
                        or command.attr_action == "disable"
                    ),
                    supported=supported,
                    targets=targets,
                    instance_action=command.attr_action,
                    priority=command.attr_priority,
                    variables=command.variables,
                    opens=command.opens,
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
    decl.opens = own_opens + target_opens
    if ambiguous and "notation" not in syntax:
        syntax.append("notation")
    return syntax, notations, tuple(context), instances


_DEP_DECL_NAME_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?((?:" + _MODS + r"\s+)*)"
    r"(?:theorem|lemma)\s+([^\s(:{«\[@]+)"
)


def _dependency_theorem_index(packages_dir: Path) -> dict[str, set[str]]:
    """Index ``short name → full names`` of theorems in dependency sources."""
    index: dict[str, set[str]] = {}
    if not packages_dir.is_dir():
        return index
    for package in sorted(packages_dir.iterdir()):
        if not package.is_dir():
            continue
        for path in package.rglob("*.lean"):
            if ".lake" in path.relative_to(package).parts:
                continue
            try:
                text = path.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError):
                continue
            stack: list[str] = []
            for line in _masked_source(text)[0]:
                stripped = line.strip()
                if not stripped:
                    continue
                scope_match = _SCOPE_COMMAND_RE.match(stripped)
                if scope_match is not None:
                    _mods, kind_word, rest = scope_match.groups()
                    stack.append(
                        rest.strip() if kind_word == "namespace" else ""
                    )
                    continue
                if stripped == "end" or stripped.startswith("end "):
                    if stack:
                        stack.pop()
                    continue
                decl = _DEP_DECL_NAME_RE.match(line)
                if decl is None:
                    continue
                if "private" in decl.group(1).split():
                    continue
                name = decl.group(2)
                if name.startswith("_root_."):
                    full = name.removeprefix("_root_.")
                else:
                    full = ".".join(
                        [part for part in stack if part] + [name]
                    )
                index.setdefault(full.rpartition(".")[2], set()).add(full)
    return index


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
    project_scopes = _project_scopes(decls)
    scoped_namespaces = {
        command.namespace
        for context in contexts.values()
        for command in context.commands
        if "scoped" in command.modifiers and command.namespace
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
                module,
                contexts,
                decls,
                decl,
                instances_by_module,
                project_scopes,
                scoped_namespaces,
            )
    return decls
