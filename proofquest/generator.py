"""Assemble the game model and render the GameSkeleton file tree."""

from __future__ import annotations

import itertools
import re
from pathlib import Path

from .dep_graph import topological_order
from .game_model import (
    Blueprint,
    BlueprintNode,
    DefsStage,
    Game,
    LeanDecl,
    LeanNotation,
    Level,
    World,
)
from .latex_to_md import latex_to_markdown, lean_interp_string, lean_string
from .lean_parser import _canonical_open, _masked_source, _open_ident_tokens

_TACTIC_DOCS = {
    "apply": "`apply t` matches the goal against the conclusion of `t` and creates goals for its hypotheses.",
    "constructor": "`constructor` splits a goal built from a structure (like `∧`) into one goal per field.",
    "exact": "`exact e` closes the goal if `e` is a proof of it.",
    "have": "`have h : t := e` introduces a new hypothesis `h : t` proved by `e`.",
    "intro": "`intro x` introduces a variable or hypothesis from the goal.",
    "omega": "`omega` solves linear arithmetic goals over `Nat` and `Int`.",
    "rfl": "`rfl` proves goals of the form `a = a` (definitional equality).",
    "rw": "`rw [h]` rewrites the goal using the equality `h`.",
    "simp": "`simp` simplifies the goal using simp lemmas.",
    "unfold": "`unfold f` unfolds the definition of `f` in the goal.",
}

# Tactics whose names are Lean keywords must be quoted with guillemets in
# `TacticDoc` / `NewTactic` commands.
_LEAN_KEYWORDS = {"have", "show", "calc", "suffices", "exists", "open", "in", "if", "let"}

# Tactics that `_tactics_in_proof` may report. Only a name in this set is
# treated as a tactic; every other first-token of a proof line (lemma names,
# local identifiers like `S`/`M`, structure projections, ...) is ignored, so
# the generated `TacticDoc`/`NewTactic` lists stay meaningful.
_KNOWN_TACTICS = frozenset(
    {
        "abel",
        "abel_nf",
        "aesop",
        "apply",
        "assumption",
        "by_cases",
        "by_contra",
        "calc",
        "case",
        "cases",
        "change",
        "choose",
        "congr",
        "constructor",
        "contradiction",
        "contrapose",
        "dsimp",
        "exact",
        "exact_mod_cast",
        "ext",
        "field_simp",
        "funext",
        "gcongr",
        "have",
        "induction",
        "infer_instance",
        "intro",
        "intros",
        "left",
        "let",
        "linarith",
        "nlinarith",
        "norm_cast",
        "norm_num",
        "obtain",
        "omega",
        "positivity",
        "push",
        "push_neg",
        "rfl",
        "rcases",
        "refine",
        "right",
        "ring",
        "ring_nf",
        "rintro",
        "rwa",
        "rw",
        "set",
        "show",
        "simp",
        "simpa",
        "subst",
        "suffices",
        "tauto",
        "trivial",
        "unfold",
        "use",
    }
)


# Non-tactic Lean term/tactic syntax keywords. A token matching one of these is
# neither a tactic (it is not in `_KNOWN_TACTICS`) nor a reference to a theorem;
# it is just Lean syntax, so `_theorem_refs_in_proof` must ignore it.
_TERM_KEYWORDS = frozenset(
    {
        "by", "then", "else", "with", "from", "at", "in", "do", "fun", "if",
        "match", "where", "this", "Type", "Prop", "Sort", "sorry", "using",
        "generalizing", "as", "forall", "exists", "True", "False", "Exists",
    }
)

# Matches a (possibly dotted/qualified) Lean identifier, e.g. `le_max_left`,
# `Nat.succ_pos` or `mul_inv_cancel₀` (Lean identifiers may end in subscript
# digits or primes).
_IDENT_PART = r"[^\W\d][\w'!?]*"
_IDENT_RE = re.compile(_IDENT_PART + r"(?:\." + _IDENT_PART + r")*")
_UNAME = r"[^\W\d][\w']*"

# Generalized field notation / anonymous-constructor-style accessors, e.g.
# `h.mp`, `foo.symm`, `bar.1`: the *last* component is not part of the
# identifier's real (declared) name, so it must be stripped before checking
# whether the name refers to an actual declaration.
_ACCESSOR_SUFFIXES = frozenset(
    {
        "mp", "mpr", "symm", "elim", "left", "right", "some", "none", "out",
        "fst", "snd", "val", "property", "choose", "resolve", "ne", "le",
        "lt", "not", "mono", "trans", "coe", "mk", "cases", "rec", "apply",
        "det", "comp", "toFun", "invFun", "1", "2",
    }
)


def _strip_accessor_suffix(name: str) -> str:
    """Drop trailing generalized-field-notation components (see above)."""
    parts = name.split(".")
    while len(parts) > 1 and parts[-1] in _ACCESSOR_SUFFIXES:
        parts.pop()
    return ".".join(parts)


# A binder group such as `(a b : ℝ)`, `{X Y : Type*}` or `[NormedSpace 𝕜 X]`,
# stopping at the first top-level `:` (so nested parens without a `:`, like
# `(a + b)`, never match).
_BINDER_GROUP_RE = re.compile(r"[(\{\[⦃]\s*([^():{}\[\]⦃⦄]+?)\s*:")

_HAVE_LET_SET_RE = re.compile(r"\b(?:have|let|set|by_contra|by_cases|generalize)\s+(" + _UNAME + r")")
_INTRO_RE = re.compile(r"\b(?:intro|intros|rintro)\s+([^\n]*)")
_OBTAIN_RE = re.compile(r"\bobtain\s+([^\n]*?)\s*:=")
_RCASES_WITH_RE = re.compile(r"\brcases\b[^\n]*?\bwith\s+([^\n]*)")
_FUN_RE = re.compile(r"\bfun\s+([^\n]*?)=>")
_FORALL_EXISTS_RE = re.compile(r"[∀∃]\s*([^,]*),")
_CHOOSE_RE = re.compile(r"\bchoose\s+([^\n]*?)\busing\b")
_SET_WITH_RE = re.compile(r"\bwith\s+(" + _UNAME + r")")


def _strip_lean_comments(text: str) -> str:
    """Drop ``--`` and ``/- -/`` comments, so their prose is never mistaken
    for identifiers (Lean comments are not part of the elaborated proof)."""
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    return re.sub(r"--[^\n]*", "", text)

# Content following a top-level `:=` (but not `:= by`, which switches to
# tactic mode) is a term; so is the argument of `exact`/`apply`/`refine`.
_ASSIGN_TERM_RE = re.compile(r":=\s*(?!by\b)(\S.*)$")
_EXACT_RE = re.compile(r"\b(?:exact\??|apply|refine)\s+(.*)$")


def _tactic_ident(tactic: str) -> str:
    return f"«{tactic}»" if tactic in _LEAN_KEYWORDS else tactic


def _binder_names(text: str) -> set[str]:
    """Names bound by binder groups such as ``(a b : T)`` or ``[Foo X]``."""
    names: set[str] = set()
    for match in _BINDER_GROUP_RE.finditer(text):
        for token in match.group(1).split():
            if re.fullmatch(_UNAME, token):
                names.add(token)
    return names


def _proof_bound_names(proof: str) -> set[str]:
    """Names locally bound within a tactic proof (``have``, ``intro``, ...).

    This does not track scoping precisely (a name is considered bound for the
    whole proof, not just after its binder); that is harmless here since a
    false "bound" name only means one less (unlikely) theorem candidate.
    """
    names: set[str] = set()
    names.update(match.group(1) for match in _HAVE_LET_SET_RE.finditer(proof))
    names.update(match.group(1) for match in _SET_WITH_RE.finditer(proof))
    for regex in (_INTRO_RE, _OBTAIN_RE, _RCASES_WITH_RE, _FUN_RE, _CHOOSE_RE):
        for match in regex.finditer(proof):
            names.update(re.findall(_UNAME, match.group(1)))
    for match in _FORALL_EXISTS_RE.finditer(proof):
        segment = match.group(1)
        colon = segment.find(":")
        names.update(
            re.findall(
                _UNAME,
                segment[:colon] if colon >= 0 else segment,
            )
        )
        for inner in _QUANTIFIER_TYPE_RE.finditer(segment):
            names.update(inner.group(1).split())
    return names


def _term_spans(proof: str) -> list[str]:
    """Snippets of a proof that are Lean terms rather than tactic syntax.

    Theorem applications occur in term position: the right-hand side of a
    ``have``/``let`` binder, the justification of a ``calc`` step, or the
    argument of ``exact``/``apply``/``refine``. Restricting the scan to these
    spans keeps tactic names (already excluded via `_KNOWN_TACTICS`) and
    incidental identifiers out of the theorem-reference results.
    """
    lines = proof.splitlines()
    spans: list[str] = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        indent = len(line) - len(line.lstrip())
        if re.search(r":=\s*$", line):
            # trailing `:=`: the term is the indented continuation below.
            block: list[str] = []
            j = i + 1
            while j < n and lines[j].strip() and (len(lines[j]) - len(lines[j].lstrip())) > indent:
                block.append(lines[j].strip())
                j += 1
            if block:
                spans.append(" ".join(block))
            i = j
            continue
        assign_match = _ASSIGN_TERM_RE.search(line)
        if assign_match:
            spans.append(assign_match.group(1))
        else:
            exact_match = _EXACT_RE.search(line.strip())
            if exact_match:
                spans.append(exact_match.group(1))
        i += 1
    return spans


def _theorem_refs_in_proof(proof: str, bound_names: set[str]) -> list[str]:
    """Theorem/lemma identifiers referenced by a sample proof.

    In first-appearance order. This is a text-level approximation of
    resolving the proof's constants in the elaborated environment: any
    identifier appearing in term position that is not a known tactic, not
    Lean syntax, and not locally bound (by the signature, active
    ``variable``s, or proof-local binders) is treated as a reference to an
    external theorem.
    """
    proof = _strip_lean_comments(proof)
    bound = bound_names | _proof_bound_names(proof)
    refs: list[str] = []
    seen: set[str] = set()
    for span in _term_spans(proof):
        for match in _IDENT_RE.finditer(span):
            if match.start() > 0 and span[match.start() - 1] == ".":
                # Dot notation on a *compound* term, e.g. `(T (α n)).le_opNorm`
                # or `(h1 h2).1`: the receiver isn't an identifier (our own
                # dotted-chain pattern would otherwise have matched it
                # together with this component), so this is a generic field
                # projection, not a literal (namespace-qualified) name -
                # there is no way to recover the real name from syntax alone.
                continue
            name = _strip_accessor_suffix(match.group(0))
            if name.strip("_") == "":
                continue  # `_`, `__`, ...: calc/pattern placeholders, not identifiers
            head = name.split(".", 1)[0]
            if head in _KNOWN_TACTICS or head in _TERM_KEYWORDS or head in _LEAN_KEYWORDS:
                continue
            if head in bound:
                continue
            if name in seen:
                continue
            seen.add(name)
            refs.append(name)
    return refs


def _context_namespace(decl: LeanDecl) -> str:
    return (
        decl.context_namespace
        if decl.context_namespace is not None
        else decl.namespace
    )


def _open_namespace_names(open_stmt: str, namespace: str) -> list[str]:
    names: list[str] = []
    scoped = False
    for token in open_stmt.split()[1:]:
        if token == "scoped":
            scoped = True
            continue
        if token in ("noncomputable", "private"):
            continue
        if token.startswith("(") or token in ("hiding", "renaming", "in"):
            break
        if not re.fullmatch(_IDENT_PART + r"(?:\." + _IDENT_PART + r")*", token):
            break
        if scoped:
            continue
        if token.startswith("_root_."):
            token = token.removeprefix("_root_.")
            if token not in names:
                names.append(token)
            continue
        if namespace:
            parts = namespace.split(".")
            for i in range(len(parts), 0, -1):
                candidate = ".".join(parts[:i]) + "." + token
                if candidate not in names:
                    names.append(candidate)
        if token not in names:
            names.append(token)
    return names


def _decl_open_entries(decl: LeanDecl):
    commands = [
        command
        for command in decl.context
        if command.kind == "open" and command.supported
    ]
    return commands if commands else list(decl.opens)


def _elaboration_namespace(decl: LeanDecl) -> str:
    """Namespace Lean elaborates the declaration body in: the declaration
    name's own prefix (``def Solution'.multiplicity`` resolves names via
    ``Solution'`` even when written at file root, ahead of the enclosing
    namespace)."""
    return decl.full_name.rpartition(".")[0]


def _opened_namespaces(
    opens,
    namespace: str,
    known: set[str],
) -> list[str]:
    opened: list[str] = []
    for entry in opens:
        if isinstance(entry, str):
            open_text, open_ns = entry, namespace
        else:
            open_text, open_ns = entry.source_text, entry.namespace
        tokens, scoped, _exotic = _open_ident_tokens(open_text)
        if scoped:
            continue
        for token in tokens:
            rooted = token.startswith("_root_.")
            base = token.removeprefix("_root_.")
            candidates: list[str] = []
            if not rooted:
                if open_ns:
                    parts = open_ns.split(".")
                    for i in range(len(parts), 0, -1):
                        candidates.append(".".join(parts[:i]) + "." + base)
                candidates.extend(f"{o}.{base}" for o in opened)
            candidates.append(base)
            hits = [c for c in candidates if c in known]
            for ns in hits if hits else [base]:
                if ns not in opened:
                    opened.append(ns)
    return opened


def _known_namespaces(decls: dict[str, LeanDecl]) -> set[str]:
    known: set[str] = set()
    for decl in decls.values():
        for dotted in (decl.namespace, decl.full_name):
            parts = dotted.split(".")
            for i in range(1, len(parts) + 1):
                known.add(".".join(parts[:i]))
    return known


def _resolve_context_decl(
    name: str,
    namespace: str,
    opens,
    decls: dict[str, LeanDecl],
    origin: str = "",
    enclosing: str | None = None,
) -> LeanDecl | None:
    bare = name.removeprefix("_root_.")
    if name.startswith("_root_."):
        return decls.get(bare)
    chains: list[str] = []
    for scope in (namespace, enclosing):
        if not scope:
            continue
        parts = scope.split(".")
        for i in range(len(parts), 0, -1):
            candidate = ".".join(parts[:i])
            if candidate not in chains:
                chains.append(candidate)
    for scope in chains:
        found = decls.get(scope + "." + bare)
        if found is not None:
            return found
    found = decls.get(bare)
    if found is not None:
        return found
    matches: dict[str, LeanDecl] = {}
    for opened in _opened_namespaces(
        opens,
        enclosing if enclosing is not None else namespace,
        _known_namespaces(decls),
    ):
        dep = decls.get(f"{opened}.{bare}")
        if dep is not None:
            matches[dep.full_name] = dep
    if len(matches) > 1:
        raise GenerationError(
            f"ambiguous identifier {name} in {origin or '<context>'}: "
            "possible project-local interpretations "
            f"{', '.join(sorted(matches))}; qualify the name explicitly in "
            "the source"
        )
    return next(iter(matches.values()), None)


def _resolve_project_decl(
    name: str, decl: LeanDecl, decls: dict[str, LeanDecl]
) -> LeanDecl | None:
    """Look up a proof-referenced identifier among the project's own declarations.

    Project-local theorems become their own level and are unlocked
    automatically by the GameServer once that level is solved, so they must
    not be re-declared with `NewTheorem` (and project-local definitions are
    handled separately, via the blueprint's `\\uses` graph).
    """
    return _resolve_context_decl(
        name,
        _elaboration_namespace(decl),
        _decl_open_entries(decl),
        decls,
        origin=decl.full_name,
        enclosing=_context_namespace(decl),
    )


_QUANTIFIER_TYPE_RE = re.compile(
    r"(" + _UNAME + r"(?:\s+" + _UNAME + r")*)\s*:\s*([^\s:]+)"
)

_HAVE_LET_TYPE_RE = re.compile(
    r"\b(?:have|let)\s+(" + _UNAME + r")\s*:\s*(.+?)\s*:="
)


def _binder_types(text: str) -> dict[str, str]:
    """Map each name bound in ``text``'s binder groups to the head identifier
    of its type expression: ``(S T : Solution')`` gives ``S -> Solution'`` and
    ``T -> Solution'``. Quantifier binders (``∀ S : Solution, ...``), typed
    ``have``/``let`` hypotheses and parenthesized body binders are covered
    the same way. Binders without an explicit type yield no entry.
    """
    types: dict[str, str] = {}
    for match in _BINDER_GROUP_RE.finditer(text):
        depth = 1
        i = match.end()
        start = i
        while i < len(text) and depth:
            ch = text[i]
            if ch in _OPEN:
                depth += 1
            elif ch in _CLOSE:
                depth -= 1
            i += 1
        head = _IDENT_RE.search(text[start:i - 1])
        if head is None:
            continue
        for name in match.group(1).split():
            if re.fullmatch(_UNAME, name):
                types[name] = head.group(0)
    for match in _FORALL_EXISTS_RE.finditer(text):
        for inner in _QUANTIFIER_TYPE_RE.finditer(match.group(1)):
            head = _IDENT_RE.match(inner.group(2).strip())
            if head is None:
                continue
            for name in inner.group(1).split():
                types[name] = head.group(0)
    for match in _HAVE_LET_TYPE_RE.finditer(text):
        head = _IDENT_RE.match(match.group(2).strip())
        if head is not None:
            types[match.group(1)] = head.group(0)
    return types


_OBTAIN_APP_RE = re.compile(
    r"\bobtain\s+⟨([^⟩]*)⟩\s*:=\s*(" + _UNAME + r"(?:\." + _UNAME + r")*)"
)
_RCASES_APP_RE = re.compile(
    r"\brcases\s+(" + _UNAME + r"(?:\." + _UNAME + r")*)"
    r"[^⟨⟩\n]*?\bwith\s+⟨([^⟩]*)⟩"
)

def _exists_binder_types(signature: str) -> list[str | None]:
    types: list[str | None] = []
    depth = 0
    colon = -1
    for i, ch in enumerate(signature):
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
        elif ch == ":" and depth == 0:
            colon = i
            break
    if colon < 0:
        return types
    rest = signature[colon + 1 :].lstrip()
    while rest.startswith("∃"):
        match = re.match(r"∃\s*([^,]*),", rest)
        if match is None:
            break
        inner = match.group(1)
        pos = 0
        for typed in _QUANTIFIER_TYPE_RE.finditer(inner):
            for token in inner[pos : typed.start()].split():
                if re.fullmatch(_UNAME, token.strip("(),")):
                    types.append(None)
            pos = typed.end()
            head = _IDENT_RE.match(typed.group(2).strip())
            types.extend(
                [head.group(0) if head is not None else None]
                * len(typed.group(1).split())
            )
        for token in inner[pos:].split():
            if re.fullmatch(_UNAME, token.strip("(), ")):
                types.append(None)
        rest = rest[match.end() :].lstrip()
    return types


def _obtain_binder_types(
    text: str,
    decl: LeanDecl,
    decls: dict[str, LeanDecl],
    known: dict[str, str],
) -> dict[str, str]:
    types = dict(known)
    namespace = _elaboration_namespace(decl)
    enclosing = _context_namespace(decl)
    events: list[tuple[int, str, str]] = [
        (m.start(), m.group(2), m.group(1))
        for m in _OBTAIN_APP_RE.finditer(text)
    ]
    events += [
        (m.start(), m.group(1), m.group(2))
        for m in _RCASES_APP_RE.finditer(text)
    ]
    for _, head_name, pattern in sorted(events):
        if "." in head_name and head_name.split(".", 1)[0] in types:
            dep = _resolve_bound_dot_ref(head_name, decl, decls, types)
        else:
            dep = _resolve_context_decl(
                head_name,
                namespace,
                _decl_open_entries(decl),
                decls,
                decl.full_name,
                enclosing=enclosing,
            )
        if dep is None:
            continue
        binder_types = []
        for raw_type in _exists_binder_types(dep.signature):
            if raw_type is None:
                binder_types.append(None)
                continue
            resolved = _resolve_context_decl(
                raw_type,
                _elaboration_namespace(dep),
                _decl_open_entries(dep),
                decls,
                dep.full_name,
                enclosing=_context_namespace(dep),
            )
            binder_types.append(
                resolved.full_name if resolved is not None else None
            )
        leaves = [leaf.strip() for leaf in pattern.split(",")]
        if any("⟨" in leaf or "(" in leaf for leaf in leaves):
            continue
        for i, leaf in enumerate(leaves):
            if not leaf or leaf in ("-", "_"):
                continue
            name, _, annotation = leaf.partition(":")
            name = name.strip()
            if not re.fullmatch(_UNAME, name):
                continue
            if annotation.strip():
                head = _IDENT_RE.match(annotation.strip())
                if head is not None:
                    types[name] = head.group(0)
            elif i < len(binder_types) and binder_types[i] is not None:
                types[name] = binder_types[i]
    return types


def _result_type_head(decl: LeanDecl) -> str | None:
    depth = 0
    signature = decl.signature
    for index, char in enumerate(signature):
        if char in _OPEN:
            depth += 1
        elif char in _CLOSE:
            depth -= 1
        elif char == ":" and depth == 0:
            match = _IDENT_RE.match(signature[index + 1 :].lstrip())
            return match.group(0) if match is not None else None
    return None


def _extends_projection_codomain(
    type_decl: LeanDecl | None, segment: str, decls: dict[str, LeanDecl]
) -> str | None:
    if (
        type_decl is None
        or type_decl.keyword not in ("structure", "class")
        or not segment.startswith("to")
        or segment == "to"
    ):
        return None
    match = re.search(
        r"\bextends\b(.+?)\bwhere\b", type_decl.signature, re.DOTALL
    )
    if match is None:
        return None
    for parent in match.group(1).split(","):
        head = _IDENT_RE.match(parent.lstrip())
        if head is None:
            continue
        parent_name = head.group(0)
        if f"to{parent_name.rpartition('.')[2]}" != segment:
            continue
        resolved = _resolve_context_decl(
            parent_name,
            _elaboration_namespace(type_decl),
            _decl_open_entries(type_decl),
            decls,
        )
        return resolved.full_name if resolved is not None else None
    return None


def _resolve_bound_dot_ref(
    name: str,
    decl: LeanDecl,
    decls: dict[str, LeanDecl],
    binder_types: dict[str, str],
    namespace: str | None = None,
    opens=None,
    enclosing: str | None = None,
) -> LeanDecl | None:
    """Resolve ``S.rest`` where ``S`` is a bound variable, the way Lean does:
    by the *receiver type*. ``S : Solution`` makes ``S.y`` denote
    ``Solution.y`` and ``S.two_le_multiplicity`` denote
    ``Solution.two_le_multiplicity`` — never an unrelated ``Foo.y``. The
    type-directed name ``Solution.rest`` is probed literally (raw tail first,
    so a real ``Solution.val`` decl wins over the generic ``.val`` accessor
    interpretation) and through ``decl``'s namespace/opens, even when the
    type itself has no declaration object (``n : Nat`` with a project-local
    ``Nat.succ``). Lean's bare-name fallback is applied only when the
    receiver type is itself a project declaration — a known external type
    (``Nat``) means an external projection, never an unrelated ``Toy.succ``
    guess. When the receiver type cannot be determined at all but a project
    declaration shares the tail, the reference is a material but unresolvable
    dependency: a :class:`GenerationError`, not a silent guess.
    """
    head, _, rest = name.partition(".")
    if namespace is None:
        namespace = _elaboration_namespace(decl)
        if enclosing is None:
            enclosing = _context_namespace(decl)
    if opens is None:
        opens = _decl_open_entries(decl)
    type_head = binder_types.get(head)
    if type_head is not None:
        tails = [
            tail
            for tail in dict.fromkeys((rest, _strip_accessor_suffix(rest)))
            if tail
        ]
        for tail in tails:
            found = _resolve_context_decl(
                f"{type_head}.{tail}",
                namespace,
                opens,
                decls,
                decl.full_name,
                enclosing=enclosing,
            )
            if found is not None:
                return found
        segments = rest.split(".")
        if len(segments) > 1:
            chain_dep: LeanDecl | None = None
            chain_type = type_head
            i = 0
            while i < len(segments):
                found = None
                for j in range(len(segments), i, -1):
                    found = _resolve_context_decl(
                        f"{chain_type}." + ".".join(segments[i:j]),
                        namespace,
                        opens,
                        decls,
                        decl.full_name,
                        enclosing=enclosing,
                    )
                    if found is not None:
                        break
                if found is not None:
                    chain_dep = found
                    if j == len(segments):
                        return found
                    chain_type = _result_type_head(found)
                    if chain_type is None:
                        return found
                    i = j
                    continue
                type_decl = _resolve_context_decl(
                    chain_type, namespace, opens, decls, decl.full_name,
                    enclosing=enclosing,
                )
                codomain = _extends_projection_codomain(
                    type_decl, segments[i], decls
                )
                if codomain is None:
                    break
                chain_type = codomain
                i += 1
            if chain_dep is not None:
                return chain_dep
        type_decl = _resolve_context_decl(
            type_head, namespace, opens, decls, decl.full_name,
            enclosing=enclosing,
        )
        if type_decl is not None:
            for tail in dict.fromkeys((*tails, rest.split(".")[-1])):
                if tail:
                    found = _resolve_context_decl(
                        tail, namespace, opens, decls, decl.full_name,
                        enclosing=enclosing,
                    )
                    if found is not None:
                        return found
        elif type_head[0].isupper() or "." in type_head:
            return None
    candidates = sorted(
        key for key in decls
        if key == rest
        or key.endswith((f".{rest}", f".{_strip_accessor_suffix(rest)}"))
    )
    if candidates:
        raise GenerationError(
            f"cannot determine the receiver type of {name} in "
            f"{decl.full_name}: it could refer to "
            f"{', '.join(candidates)}; annotate the binder type or qualify "
            "the reference explicitly in the source"
        )
    return None


def _source_refs(decl: LeanDecl, decls: dict[str, LeanDecl]) -> list[LeanDecl]:
    """Project-local declarations referenced anywhere in ``decl``'s source.

    A definition copied into ``Defs.lean`` may itself mention other
    project declarations (in its type, body or ``variable`` context); those
    must be copied along or the file will not elaborate. Same resolution
    rules as ``_theorem_refs_in_proof``: identifier candidates are filtered
    against locally bound names and resolved through ``decl``'s own
    namespace/opens via :func:`_resolve_project_decl`.
    """
    text = _strip_lean_comments(decl.source_text)
    text = re.sub(r'"(?:\\.|[^"\\])*"', '""', text)
    text = re.sub(r"(?<![\w'.!?])'(?:\\[^'\\]+|[^'\\])'", "''", text)
    bound = _binder_names(decl.signature)
    bound |= _proof_bound_names(text)
    for var_line in decl.variables:
        bound |= _binder_names(var_line)
    text += "\n" + "\n".join(decl.variables)
    binder_types = _obtain_binder_types(text, decl, decls, _binder_types(text))
    bound.add(decl.name)
    bound.add(decl.full_name)
    refs: list[LeanDecl] = []
    seen_refs: set[str] = set()

    def add_dep(dep: LeanDecl | None) -> None:
        if dep is not None and dep is not decl and dep.full_name not in seen_refs:
            refs.append(dep)
            seen_refs.add(dep.full_name)

    for notation in decl.notations:
        if notation.expression is None:
            add_dep(decls.get(notation.target))
            continue
        notation_text = "\n".join(notation.variables)
        notation_bound = _binder_names(notation_text)
        notation_types = _binder_types(notation_text)
        expr = re.sub(r'"(?:\\.|[^"\\])*"', '""', notation.expression)
        for match in _IDENT_RE.finditer(expr):
            raw = match.group(0)
            name = _strip_accessor_suffix(raw)
            if name.strip("_") == "":
                continue
            head = name.split(".", 1)[0]
            if (
                head in _KNOWN_TACTICS
                or head in _TERM_KEYWORDS
                or head in _LEAN_KEYWORDS
            ):
                continue
            if head in notation_bound:
                dep = (
                    _resolve_bound_dot_ref(
                        raw,
                        decl,
                        decls,
                        notation_types,
                        namespace=notation.namespace,
                        opens=notation.opens,
                    )
                    if "." in raw
                    else None
                )
            else:
                dep = None
                prefix = name
                while prefix:
                    dep = _resolve_context_decl(
                        prefix,
                        notation.namespace,
                        notation.opens,
                        decls,
                        origin=(
                            f"{decl.full_name} "
                            f"(local notation {notation.pattern})"
                        ),
                    )
                    if dep is not None or prefix == name.split(".")[0]:
                        break
                    prefix = prefix.rpartition(".")[0]
            add_dep(dep)
    for command in decl.context:
        if command.kind == "attribute" and command.supported:
            for target in command.targets:
                if target.startswith("_root_."):
                    add_dep(decls.get(target.removeprefix("_root_.")))
    seen: set[str] = set()
    for match in _IDENT_RE.finditer(text):
        raw = match.group(0)
        name = _strip_accessor_suffix(raw)
        if name.strip("_") == "":
            continue
        head = name.split(".", 1)[0]
        if head in _KNOWN_TACTICS or head in _TERM_KEYWORDS or head in _LEAN_KEYWORDS:
            continue
        if raw in seen:
            continue
        seen.add(raw)
        if head in bound:
            dep = (
                _resolve_bound_dot_ref(raw, decl, decls, binder_types)
                if "." in raw
                else None
            )
        else:
            dep = _resolve_project_decl(name, decl, decls)
        if dep is not None and dep is not decl and dep.full_name not in seen_refs:
            refs.append(dep)
            seen_refs.add(dep.full_name)
    return refs


def _project_scopes(decls: dict[str, LeanDecl]) -> set[str]:
    """Dotted prefixes naming something project-local: every module name and
    every declaration namespace, plus all of their prefixes. An ``open`` of
    one of these cannot be reproduced verbatim in a generated file, because
    the opened namespace would only contain the copied subset and silently
    change name resolution.
    """
    scopes: set[str] = set()
    for decl in decls.values():
        for dotted in (decl.module, decl.namespace):
            if not dotted:
                continue
            parts = dotted.split(".")
            for i in range(1, len(parts) + 1):
                scopes.add(".".join(parts[:i]))
    return scopes


def _project_open_targets(
    decl: LeanDecl, project_scopes: set[str]
) -> list[str]:
    """Project-local namespaces opened by ``decl``'s ``open`` statements."""
    bad: list[str] = []
    for open_stmt in decl.opens:
        scoped = False
        exotic = False
        idents: list[str] = []
        for token in open_stmt.split()[1:]:
            if token in ("scoped", "noncomputable", "private"):
                scoped = scoped or token == "scoped"
                continue
            if token.startswith("(") or token in ("hiding", "renaming", "in"):
                exotic = True
                break
            if not re.fullmatch(_IDENT_PART + r"(?:\." + _IDENT_PART + r")*", token):
                exotic = True
                break
            idents.append(token)
        if scoped or not exotic:
            continue
        for token in idents:
            parts = token.split(".")
            if (
                any(
                    ".".join(parts[:i]) in project_scopes
                    for i in range(1, len(parts) + 1)
                )
                and token not in bad
            ):
                bad.append(token)
    return bad


def _decl_origin(decl: LeanDecl) -> str:
    if decl.source_path:
        return f" ({decl.source_path}:{decl.line + 1})"
    return ""


def _unsupported_context_message(
    label: str,
    decl: LeanDecl,
    visiting: list[str],
    target_file: str,
) -> str:
    parts: list[str] = []
    for kind in dict.fromkeys(decl.local_syntax):
        origin = next(
            (
                f" ({command.source_path}:{command.line + 1})"
                for command in decl.context
                if not command.supported
                and command.kind == kind
                and command.source_path
            ),
            "",
        )
        parts.append(kind + origin)
    chain = visiting + [decl.full_name]
    message = (
        f"{label}: copied declaration {decl.full_name}{_decl_origin(decl)} is "
        f"declared in a source context (module {decl.module or '?'}) that "
        f"defines project-local commands which cannot be reproduced in "
        f"{target_file}: " + ", ".join(parts)
    )
    if len(chain) > 1:
        message += f"; dependency chain: {' -> '.join(chain)}"
    message += (
        "; expand the notation/syntax manually or move the declaration (and "
        "the declarations it uses) to a module that does not rely on "
        "project-local syntax"
    )
    return message


def _copy_order(
    roots: list[LeanDecl],
    decls: dict[str, LeanDecl],
    blueprint_theorems: set[str],
    label: str,
    project_scopes: set[str],
    instance_roots: list[LeanDecl] | None = None,
    allow_level_dependencies: bool = False,
    target_file: str = "Game/Generated/Defs.lean",
) -> list[LeanDecl]:
    """``roots`` plus their transitive project-local dependencies, deps first.

    Deterministic: dependencies are visited in the order they are referenced
    in each declaration's source text. Names in ``blueprint_theorems`` are
    blueprint *theorem* declarations: they become game levels via `Statement`
    and can never be copied into a definitions module (the duplicate name
    would clash with the level's own declaration). When
    ``allow_level_dependencies`` is set, such a dependency is skipped instead
    of rejected: the caller is responsible for staging the copied declaration
    after the level that provides it. A declaration from a source context
    that defines project-local notation/syntax cannot be reproduced verbatim
    in a self-contained generated file, so it is rejected by name rather
    than emitted broken; and a dependency cycle (impossible in valid Lean,
    but reachable through the text-level dependency approximation) is
    reported instead of being emitted in an arbitrary order.
    """
    ordered: list[LeanDecl] = []
    seen: set[str] = set()
    seen_context: set[str] = set()
    emitted_ordered: set[str] = set()
    visiting: list[str] = []

    def visit(dep: LeanDecl) -> None:
        if dep.full_name in blueprint_theorems:
            if allow_level_dependencies:
                return
            raise GenerationError(
                f"{label}: copied declaration {visiting[-1] if visiting else dep.full_name} "
                f"depends on blueprint theorem {dep.full_name}{_decl_origin(dep)}, "
                "which becomes a game level and cannot be copied into "
                "a generated definitions module"
            )
        visit_or_context(dep)

    def visit_or_context(decl: LeanDecl, as_context: bool = False) -> None:
        if decl.full_name in visiting:
            cycle = visiting[visiting.index(decl.full_name):] + [decl.full_name]
            raise GenerationError(
                f"{label}: dependency cycle among copied declarations "
                f"({' -> '.join(cycle)}); cannot order them for Defs.lean"
            )
        if decl.full_name in seen or (as_context and decl.full_name in seen_context):
            return
        if decl.local_syntax:
            raise GenerationError(
                _unsupported_context_message(label, decl, visiting, target_file)
            )
        bad_opens = _project_open_targets(decl, project_scopes)
        if bad_opens:
            raise GenerationError(
                f"{label}: copied declaration {decl.full_name}"
                f"{_decl_origin(decl)} relies on project-local `open` "
                f"({', '.join(bad_opens)}) whose namespace cannot be "
                f"reproduced self-contained in {target_file}; "
                "qualify the names explicitly or move the declaration to a "
                "module that does not rely on project-local opens"
            )
        visiting.append(decl.full_name)
        for dep in _source_refs(decl, decls):
            if as_context and dep.full_name in visiting:
                continue
            visit(dep)
        for inst in decl.instances:
            visit_or_context(inst, as_context=True)
        visiting.pop()
        if as_context:
            seen_context.add(decl.full_name)
        else:
            seen.add(decl.full_name)
        if decl.full_name not in emitted_ordered:
            emitted_ordered.add(decl.full_name)
            ordered.append(decl)

    for root in roots:
        if root.full_name in blueprint_theorems:
            if allow_level_dependencies:
                continue
            raise GenerationError(
                f"{label}: blueprint theorem {root.full_name}"
                f"{_decl_origin(root)} becomes a game level and cannot be "
                "copied into a generated definitions module"
            )
        visit_or_context(root)
    for inst in instance_roots or ():
        visit_or_context(inst, as_context=True)
    return ordered


def _looks_like_theorem_name(name: str) -> bool:
    """Best-effort naming-convention check for an *external* (e.g. Mathlib)
    theorem reference that cannot be checked against source.

    Exhaustively verifying arbitrary external names against source isn't
    reliable (some real names live in Lean's core library, which isn't
    fetched into any lake dependency, e.g. `le_max_left`) or cheap (Mathlib
    alone is thousands of files) to do for every `generate` run. Instead this
    relies on a strong, standard Mathlib/Lean naming convention: a theorem's
    name describes a compound proposition and (essentially) always contains
    an underscore in some dotted component, whereas a bare "word" like
    `sSup`, `max` or `dist` is a definition/class field. This intentionally
    trades a little completeness (some real external theorems, or generic
    field-notation accessors like `mem_ball_zero_iff.mp`'s suffix, will be
    missed) for never emitting a `NewTheorem` the GameServer would reject.
    """
    return any("_" in part for part in name.split("."))


def _resolve_inventory_name(
    name: str,
    decl: LeanDecl,
    decls: dict[str, LeanDecl],
    index: dict[str, set[str]] | None,
) -> str | None:
    if not index:
        return name

    def indexed(full: str) -> bool:
        return full in index.get(full.rpartition(".")[2], ())

    namespace = _elaboration_namespace(decl)
    enclosing = _context_namespace(decl)
    chains: list[str] = []
    for scope in (namespace, enclosing):
        if not scope:
            continue
        parts = scope.split(".")
        for i in range(len(parts), 0, -1):
            candidate = ".".join(parts[:i])
            if candidate not in chains:
                chains.append(candidate)
    if "." in name:
        if name.startswith("_root_."):
            token = name.removeprefix("_root_.")
            return token if indexed(token) else None
        for scope in chains:
            candidate = scope + "." + name
            if indexed(candidate):
                return candidate
        if indexed(name):
            return name
        opened_matches = {
            f"{opened}.{name}"
            for opened in _opened_namespaces(
                _decl_open_entries(decl), enclosing, _known_namespaces(decls)
            )
            if indexed(f"{opened}.{name}")
        }
        if len(opened_matches) == 1:
            return next(iter(opened_matches))
        return None
    fulls = index.get(name)
    if not fulls:
        return None
    for scope in chains:
        candidate = scope + "." + name
        if candidate in fulls:
            return candidate
    if name in fulls:
        return name
    matches = {
        f"{opened}.{name}"
        for opened in _opened_namespaces(
            _decl_open_entries(decl), enclosing, _known_namespaces(decls)
        )
        if f"{opened}.{name}" in fulls
    }
    if len(matches) == 1:
        return next(iter(matches))
    return None


def _is_declared_theorem(name: str, decl: LeanDecl, decls: dict[str, LeanDecl]) -> bool:
    """Whether ``name`` is trustworthy enough to declare with `NewTheorem`.

    Checked by *exact* full-name match (as written, or qualified by ``decl``'s
    namespace/opens) against the project's own declarations when possible
    (never by bare short name alone: two unrelated declarations can share a
    short name); otherwise falls back to `_looks_like_theorem_name` for
    external references. Either way, this must never accept a name the
    GameServer's own `getConstInfo` check would reject, since that fails
    `lake build`.
    """
    found = _resolve_project_decl(name, decl, decls)
    if found is not None:
        return found.keyword in ("theorem", "lemma")
    return _looks_like_theorem_name(name)


class GenerationError(Exception):
    pass


def _legacy_doc_syntax(toolchain: str) -> bool:
    """Whether the GameServer at ``toolchain`` needs the pre-v4.23 doc syntax.

    lean4game tags before ``v4.23.0`` (e.g. ``v4.7.0``) require
    ``TheoremDoc NAME as "display" in "category" ["content"]`` — the ``in``
    clause is mandatory — while ``DefinitionDoc`` accepts only
    ``NAME as "display" ["content"]`` (no ``in`` clause at all). From
    ``v4.23.0`` the ``in`` clause is optional on every doc command, so the
    shorter forms are kept there unchanged. Verified against the real
    v4.7.0 GameServer: a docstring *and* a trailing content string together
    are rejected, so content strings are never emitted (the docstring is
    kept instead).
    """
    match = re.search(r"v?(\d+)\.(\d+)\.(\d+)", toolchain)
    if match is None:
        return False
    return (int(match.group(1)), int(match.group(2))) < (4, 23)


def _camel(title: str) -> str:
    words = re.findall(r"[A-Za-z0-9]+", title)
    if not words:
        raise GenerationError(f"cannot derive an identifier from title {title!r}")
    return "".join(word.capitalize() if not word[0].isupper() else word for word in words)


def _tactics_in_proof(proof: str) -> list[str]:
    """Tactics used in a sample proof, in first-appearance order.

    Catches the first token of each tactic line (after bullets) as well as
    tactics that appear inline after ``:= by`` / ``by``. Only tokens in
    :data:`_KNOWN_TACTICS` are reported, so theorem references and other
    identifiers are never mistaken for tactics.
    """
    tactics: list[str] = []
    for line in proof.splitlines():
        match = re.match(r"\s*(?:(?:·|\.|<;>)\s*)*([a-zA-Z_][A-Za-z0-9_']*)", line)
        if match:
            token = match.group(1)
            if token in _KNOWN_TACTICS and token not in tactics:
                tactics.append(token)
        for sub in re.finditer(r"\bby\s+([a-zA-Z_][A-Za-z0-9_']*)", line):
            token = sub.group(1)
            if token in _KNOWN_TACTICS and token not in tactics:
                tactics.append(token)
    return tactics


def _ref_titles(blueprint: Blueprint) -> dict[str, str]:
    return {n.label: (n.title or n.label) for n in blueprint.nodes}


def _find_mixed_cycle(
    start: str, depends: dict[str, list[str]]
) -> list[str] | None:
    """A ``start -> ... -> start`` chain in the mixed dependency graph.

    ``depends`` maps a declaration's full name to the full names it refers
    to in the Lean source (both copied auxiliaries and level theorems).
    Returns the cycle with ``start``'s first repeated node at both ends, or
    ``None`` when ``start`` is not on a cycle.
    """
    color: dict[str, int] = {}
    stack: list[str] = []

    def dfs(node: str) -> list[str] | None:
        color[node] = 1
        stack.append(node)
        for dep in depends.get(node, ()):
            if dep not in depends:
                continue
            state = color.get(dep, 0)
            if state == 1:
                return stack[stack.index(dep):] + [dep]
            if state == 0:
                found = dfs(dep)
                if found is not None:
                    return found
        stack.pop()
        color[node] = 2
        return None

    return dfs(start)


def _level_order(
    blueprint: Blueprint,
    all_nodes: list[BlueprintNode],
    theorem_nodes: list[BlueprintNode],
    decl_by_label: dict[str, LeanDecl],
    node_by_name: dict[str, BlueprintNode],
    thm_refs: dict[str, list[LeanDecl]],
    required_aux: dict[str, list[LeanDecl]],
    aux_edges: dict[str, list[LeanDecl]],
    aux_prereqs,
    decls: dict[str, LeanDecl],
) -> tuple[list[BlueprintNode], list[tuple[str, str]]]:
    """Global emission order of the theorem levels plus world dependencies.

    Ordering constraints are derived from the *projected* prerequisite graph
    over blueprint nodes (theorems and definitions): blueprint ``\\uses``
    edges on any node, references to other blueprint declarations found in a
    target's own source (signature *and* sample proof; a target's proof never
    constrains itself), and level-theorem prerequisites of every required
    auxiliary — so ``U -> T`` holds whenever ``T`` needs a definition that
    transitively needs level ``U``, whether the requirement enters through
    the blueprint or through source. A theorem ancestor of a target in a
    different world induces an edge in the world DAG; when that DAG is
    cyclic the grouped layout cannot satisfy the ordering and generation
    fails with the witnessing dependency chain. Otherwise worlds are
    topo-sorted by blueprint rank, targets are topo-sorted inside each
    world, and the flattened sequence — worlds emitted contiguously — is
    returned, so emission positions are always consistent with
    ``Game.worlds``.
    """
    by_label = blueprint.by_label()
    edges: dict[str, set[str]] = {}

    def add_edge(source: str, target: str) -> None:
        edges.setdefault(source, set()).add(target)

    for node in all_nodes:
        for use in node.uses:
            if use in by_label:
                add_edge(use, node.label)
        if node.is_theorem:
            for ref in thm_refs[node.label]:
                ref_node = node_by_name.get(ref.full_name)
                if ref_node is not None and ref_node.label != node.label:
                    add_edge(ref_node.label, node.label)
            for aux in required_aux[node.label]:
                aux_node = node_by_name.get(aux.full_name)
                if aux_node is not None and aux_node.label != node.label:
                    add_edge(aux_node.label, node.label)
                for name in aux_prereqs(aux.full_name):
                    used = node_by_name.get(name)
                    if used is not None:
                        add_edge(used.label, node.label)
        else:
            for name in node.lean_names:
                named = decls.get(name)
                if named is None:
                    continue
                for dep in aux_edges.get(named.full_name, ()):
                    dep_node = node_by_name.get(dep.full_name)
                    if dep_node is not None and dep_node.label != node.label:
                        add_edge(dep_node.label, node.label)
                for theorem_name in aux_prereqs(named.full_name):
                    used = node_by_name.get(theorem_name)
                    if used is not None and used.label != node.label:
                        add_edge(used.label, node.label)

    predecessors: dict[str, set[str]] = {}
    for source, targets in edges.items():
        for target in targets:
            predecessors.setdefault(target, set()).add(source)

    def label_cycle() -> list[str] | None:
        color: dict[str, int] = {}
        stack: list[str] = []

        def dfs(label: str) -> list[str] | None:
            color[label] = 1
            stack.append(label)
            for dep in sorted(predecessors.get(label, ())):
                state = color.get(dep, 0)
                if state == 1:
                    return stack[stack.index(dep):] + [dep]
                if state == 0:
                    found = dfs(dep)
                    if found is not None:
                        return found
            stack.pop()
            color[label] = 2
            return None

        for node in all_nodes:
            if color.get(node.label, 0) == 0:
                found = dfs(node.label)
                if found is not None:
                    return found
        return None

    cycle = label_cycle()
    if cycle is not None:
        depends: dict[str, list[str]] = {
            name: [dep.full_name for dep in deps]
            for name, deps in aux_edges.items()
        }
        for node in all_nodes:
            decl = decl_by_label.get(node.label)
            if decl is None:
                continue
            names = [
                decl_by_label[use].full_name
                for use in node.uses
                if use in decl_by_label
            ]
            if node.is_theorem:
                names += [aux.full_name for aux in required_aux[node.label]]
                names += [
                    ref.full_name
                    for ref in thm_refs[node.label]
                    if ref.full_name in node_by_name
                ]
            depends[decl.full_name] = depends.get(decl.full_name, []) + [
                name for name in names
                if name not in depends.get(decl.full_name, [])
            ]
        start = decl_by_label[cycle[0]].full_name

        def origin(name: str) -> str:
            found = decls.get(name)
            return _decl_origin(found) if found is not None else ""

        mixed = _find_mixed_cycle(start, depends)
        if mixed is not None:
            chain = " -> ".join(f"{name}{origin(name)}" for name in mixed)
            raise GenerationError(
                f"{cycle[0]}: dependency cycle between copied definitions "
                f"and level theorems prevents a valid emission order: "
                f"{chain}; each step is a source-level dependency in the "
                "named declaration, so no emission order can place every "
                "prerequisite before its dependents"
            )
        chain = " -> ".join(
            f"{label} ({decl_by_label[label].full_name}"
            f"{origin(decl_by_label[label].full_name)})"
            for label in cycle
        )
        raise GenerationError(
            f"{cycle[0]}: dependency cycle prevents a valid emission order: "
            f"{chain}; each step is a blueprint or source-level dependency, "
            "so no emission order can place every prerequisite before its "
            "dependents"
        )

    def path(source: str, target: str) -> list[str]:
        previous = {target: None}
        queue = [target]
        while queue:
            current = queue.pop(0)
            if current == source:
                break
            for pred in sorted(predecessors.get(current, ())):
                if pred not in previous:
                    previous[pred] = current
                    queue.append(pred)
        result = [source]
        while result[-1] != target:
            result.append(previous[result[-1]])
        return result

    theorem_labels = {node.label for node in theorem_nodes}
    projected: dict[tuple[str, str], list[str]] = {}
    for node in theorem_nodes:
        seen: set[str] = set()
        stack = [node.label]
        while stack:
            current = stack.pop()
            for pred in predecessors.get(current, ()):
                if pred not in seen:
                    seen.add(pred)
                    stack.append(pred)
        for ancestor in sorted(seen, key=lambda label: (by_label[label].order, label)):
            if ancestor in theorem_labels and ancestor != node.label:
                projected[(ancestor, node.label)] = path(ancestor, node.label)

    world_of = {node.label: _camel(node.chapter) for node in theorem_nodes}
    world_edges: dict[tuple[str, str], list[str]] = {}
    for (source, target), witness in projected.items():
        pair = (world_of[source], world_of[target])
        if pair[0] != pair[1] and pair not in world_edges:
            world_edges[pair] = witness

    world_rank: dict[str, int] = {}
    for node in theorem_nodes:
        wid = world_of[node.label]
        world_rank[wid] = min(world_rank.get(wid, node.order), node.order)
    world_next: dict[str, set[str]] = {}
    world_indegree = {wid: 0 for wid in world_rank}
    for source, target in world_edges:
        if target not in world_next.setdefault(source, set()):
            world_next[source].add(target)
            world_indegree[target] = world_indegree.get(target, 0) + 1
    ready_worlds = sorted(
        (wid for wid, deg in world_indegree.items() if deg == 0),
        key=lambda wid: world_rank[wid],
    )
    world_seq: list[str] = []
    while ready_worlds:
        wid = ready_worlds.pop(0)
        world_seq.append(wid)
        changed = False
        for nxt in world_next.get(wid, ()):
            world_indegree[nxt] -= 1
            if world_indegree[nxt] == 0:
                ready_worlds.append(nxt)
                changed = True
        if changed:
            ready_worlds.sort(key=lambda item: world_rank[item])
    if len(world_seq) != len(world_rank):
        remaining = sorted(
            (wid for wid in world_rank if wid not in world_seq),
            key=lambda wid: world_rank[wid],
        )
        color: dict[str, int] = {}
        wstack: list[str] = []

        def world_cycle_dfs(wid: str) -> list[str] | None:
            color[wid] = 1
            wstack.append(wid)
            for nxt in sorted(world_next.get(wid, ())):
                state = color.get(nxt, 0)
                if state == 1:
                    return wstack[wstack.index(nxt):] + [nxt]
                if state == 0:
                    found = world_cycle_dfs(nxt)
                    if found is not None:
                        return found
            wstack.pop()
            color[wid] = 2
            return None

        found_cycle = None
        for wid in remaining:
            if color.get(wid, 0) == 0:
                found_cycle = world_cycle_dfs(wid)
                if found_cycle is not None:
                    break
        found_cycle = found_cycle or remaining + [remaining[0]]

        def describe(label: str) -> str:
            decl = decl_by_label.get(label)
            name = decl.full_name if decl is not None else label
            return f"{name}{_decl_origin(decl) if decl is not None else ''} [{label}]"

        hops = []
        for source_wid, target_wid in itertools.pairwise(found_cycle):
            witness = world_edges.get((source_wid, target_wid))
            if witness:
                hops.append(" -> ".join(describe(label) for label in witness))
        raise GenerationError(
            "unsupported grouped world layout: worlds form a dependency "
            f"cycle {' -> '.join(found_cycle)}"
            + (f"; required by {'; '.join(hops)}" if hops else "")
            + "; each world is emitted contiguously, so no global level "
            "order can place every prerequisite before its dependents"
        )

    order_of = {node.label: node.order for node in theorem_nodes}
    result: list[BlueprintNode] = []
    node_by_label = {node.label: node for node in theorem_nodes}
    for wid in world_seq:
        members = [node for node in theorem_nodes if world_of[node.label] == wid]
        indegree = {node.label: 0 for node in members}
        dependents: dict[str, list[str]] = {node.label: [] for node in members}
        for (source, target) in projected:
            if source in indegree and target in indegree:
                indegree[target] += 1
                dependents[source].append(target)
        ready = sorted(
            (label for label, deg in indegree.items() if deg == 0),
            key=lambda label: order_of[label],
        )
        while ready:
            label = ready.pop(0)
            result.append(node_by_label[label])
            changed = False
            for dep in dependents[label]:
                indegree[dep] -= 1
                if indegree[dep] == 0:
                    ready.append(dep)
                    changed = True
            if changed:
                ready.sort(key=lambda lbl: order_of[lbl])

    world_position = {wid: index for index, wid in enumerate(world_seq)}
    dependencies = sorted(
        world_edges,
        key=lambda pair: (world_position[pair[0]], world_position[pair[1]]),
    )
    return result, dependencies


def build_game(
    blueprint: Blueprint,
    decls: dict[str, LeanDecl],
    toolchain: str,
    title: str,
    languages: str = "en",
    theorem_index: dict[str, set[str]] | None = None,
) -> Game:
    """Turn the parsed blueprint + Lean declarations into a game model."""
    order = topological_order(blueprint)
    refs = _ref_titles(blueprint)
    by_label = blueprint.by_label()

    def node_decl(node: BlueprintNode) -> LeanDecl | None:
        for name in node.lean_names:
            if name in decls:
                return decls[name]
        return None

    theorem_names = {
        name for node in order if node.is_theorem for name in node.lean_names
    }
    def_node_by_name: dict[str, BlueprintNode] = {}
    for node in order:
        if node.is_theorem:
            continue
        for name in node.lean_names:
            if name in decls and name not in def_node_by_name:
                def_node_by_name[name] = node

    project_scopes = _project_scopes(decls)
    if theorem_index:
        external_namespaces = frozenset(
            ".".join(parts[:i])
            for names in theorem_index.values()
            for full in names
            for parts in [full.split(".")]
            for i in range(1, len(parts))
        )
        for decl in decls.values():
            decl.external_namespaces = external_namespaces
    definitions: list[tuple[LeanDecl, BlueprintNode | None]] = []
    def_closure_by_label: dict[str, list[LeanDecl]] = {}
    emitted_defs: set[str] = set()

    def append_definitions(
        copied: list[LeanDecl], node: BlueprintNode, named_names: set[str]
    ) -> None:
        for dep in copied:
            if dep.full_name in emitted_defs:
                continue
            emitted_defs.add(dep.full_name)
            owner = node if dep.full_name in named_names else def_node_by_name.get(dep.full_name)
            definitions.append((dep, owner))

    decl_by_label: dict[str, LeanDecl] = {}
    for node in order:
        if node.is_theorem:
            continue
        missing = [name for name in node.lean_names if name not in decls]
        if not node.lean_names or missing:
            raise GenerationError(
                f"{node.label}: definition has no matching Lean declaration "
                f"(\\lean{{{', '.join(node.lean_names) or '?'}}})"
                + (
                    f"; not found in the Lean sources: {', '.join(missing)}"
                    if missing
                    else ""
                )
            )
        named = [decls[name] for name in node.lean_names]
        decl_by_label[node.label] = named[0]
        named_names = {d.full_name for d in named}
        copied = _copy_order(
            named,
            decls,
            theorem_names,
            node.label,
            project_scopes,
            allow_level_dependencies=True,
        )
        append_definitions(copied, node, named_names)
        def_closure_by_label[node.label] = copied

    theorem_nodes = [node for node in order if node.is_theorem]
    theorem_decl: dict[str, LeanDecl] = {}
    theorem_node_by_name: dict[str, BlueprintNode] = {}
    thm_refs: dict[str, list[LeanDecl]] = {}
    required_aux: dict[str, list[LeanDecl]] = {}
    theorem_copied: dict[str, list[LeanDecl]] = {}
    for node in theorem_nodes:
        decl = node_decl(node)
        if decl is None:
            raise GenerationError(
                f"{node.label}: theorem has no matching Lean declaration "
                f"(\\lean{{{', '.join(node.lean_names) or '?'}}})"
            )
        if decl.local_syntax:
            raise GenerationError(
                _unsupported_context_message(
                    node.label, decl, [], "the generated level files"
                ).replace("copied declaration", "theorem", 1)
            )
        bad_opens = _project_open_targets(decl, project_scopes)
        if bad_opens:
            raise GenerationError(
                f"{node.label}: theorem {decl.full_name}{_decl_origin(decl)} "
                f"relies on project-local `open` ({', '.join(bad_opens)}) "
                "whose namespace cannot be reproduced self-contained in the "
                "generated level files; qualify the names explicitly or "
                "move the declaration to a module that does not rely on "
                "project-local opens"
            )
        if not (decl.proof or "").strip():
            raise GenerationError(
                f"level {node.label}: theorem {decl.full_name} has no "
                "proof to reuse as the level's sample solution"
            )
        theorem_decl[node.label] = decl
        decl_by_label[node.label] = decl
        for name in (*node.lean_names, decl.full_name):
            theorem_names.add(name)
            theorem_node_by_name[name] = node
        source_refs = _source_refs(decl, decls)
        thm_refs[node.label] = source_refs
        needed = [r for r in source_refs if r.full_name not in theorem_names]
        seen_needed = {r.full_name for r in needed}
        for inst in decl.instances:
            if inst.full_name not in seen_needed:
                needed.append(inst)
                seen_needed.add(inst.full_name)
        required_aux[node.label] = needed
        notation_roots = [
            decls[notation.target]
            for notation in decl.notations
            if notation.target in decls
        ]
        copied = _copy_order(
            notation_roots + needed,
            decls,
            theorem_names,
            node.label,
            project_scopes,
            instance_roots=decl.instances,
            allow_level_dependencies=True,
            target_file="a staged Game/Generated/DefsAfterNNN.lean module",
        )
        theorem_copied[node.label] = copied
        append_definitions(copied, node, set())

    aux_edges: dict[str, list[LeanDecl]] = {}
    for decl, _ in definitions:
        deps = _source_refs(decl, decls)
        seen_dep = {dep.full_name for dep in deps}
        for inst in decl.instances:
            if inst.full_name not in seen_dep:
                deps.append(inst)
                seen_dep.add(inst.full_name)
        aux_edges[decl.full_name] = deps

    prereq_cache: dict[str, frozenset[str]] = {}

    def aux_prereqs(name: str, stack: tuple[str, ...] = ()) -> frozenset[str]:
        """Blueprint-theorem full names an auxiliary transitively needs."""
        if name in prereq_cache:
            return prereq_cache[name]
        acc: set[str] = set()
        for dep in aux_edges.get(name, ()):
            if dep.full_name in theorem_names:
                acc.add(dep.full_name)
            elif dep.full_name in aux_edges and dep.full_name not in stack:
                acc |= aux_prereqs(dep.full_name, (*stack, name))
        prereq_cache[name] = frozenset(acc)
        return prereq_cache[name]

    node_by_name: dict[str, BlueprintNode] = {}
    for node in order:
        for name in node.lean_names:
            if name in decls and name not in node_by_name:
                node_by_name[name] = node
    for node in theorem_nodes:
        node_by_name.setdefault(theorem_decl[node.label].full_name, node)

    level_order, world_edges = _level_order(
        blueprint,
        order,
        theorem_nodes,
        decl_by_label,
        node_by_name,
        thm_refs,
        required_aux,
        aux_edges,
        aux_prereqs,
        decls,
    )
    position = {node.label: i + 1 for i, node in enumerate(level_order)}

    stage_of: dict[str, int] = {}
    for decl, _ in definitions:
        stage_of[decl.full_name] = max(
            (
                position[theorem_node_by_name[name].label]
                for name in aux_prereqs(decl.full_name)
                if name in theorem_node_by_name
            ),
            default=0,
        )
    for node in level_order:
        for aux in required_aux[node.label]:
            if stage_of[aux.full_name] >= position[node.label]:
                needed = sorted(aux_prereqs(aux.full_name))
                raise GenerationError(
                    f"{node.label}: copied declaration {aux.full_name}"
                    f"{_decl_origin(aux)} is needed by this level but "
                    "depends on level theorem(s) "
                    f"{', '.join(needed)} emitted at or after it; no "
                    "emission order can place the definition between them "
                    "without revisiting an already emitted level or world"
                )

    worlds: dict[str, World] = {}
    world_order: list[str] = []
    introduced_defs: set[str] = set()
    introduced_tactics: list[str] = []
    introduced_theorems: list[str] = []
    level_at: dict[int, Level] = {}
    desired_intro: dict[str, int] = {}

    for node in level_order:
        decl = theorem_decl[node.label]
        notation_copied = theorem_copied[node.label]
        world_id = _camel(node.chapter)
        if world_id in worlds and worlds[world_id].title != node.chapter:
            raise GenerationError(
                f"chapter titles {worlds[world_id].title!r} and {node.chapter!r} "
                f"generate the same world identifier {world_id!r}"
            )
        if world_id not in worlds:
            intro_tex = blueprint.chapter_intros.get(node.chapter, "")
            worlds[world_id] = World(
                world_id=world_id,
                title=node.chapter,
                intro_md=latex_to_markdown(intro_tex, refs),
            )
            world_order.append(world_id)
        world = worlds[world_id]

        pos = position[node.label]

        def introduce(
            dep: LeanDecl, out: list[LeanDecl], at: int = pos
        ) -> None:
            if not dep.is_definition or dep.full_name in introduced_defs:
                return
            if stage_of[dep.full_name] < at:
                introduced_defs.add(dep.full_name)
                out.append(dep)
            else:
                desired_intro.setdefault(dep.full_name, at)

        new_defs: list[LeanDecl] = []
        for dep in notation_copied:
            introduce(dep, new_defs)
        for use in node.uses:
            used = by_label.get(use)
            if used is None or used.is_theorem:
                continue
            for dep in def_closure_by_label[use]:
                introduce(dep, new_defs)

        new_tactics: list[str] = []
        new_theorems: list[str] = []
        proof_text = (decl.proof or "").strip()
        if proof_text:
            if re.match(r"by\b", proof_text):
                proof_body = proof_text[2:]
            else:
                term_lines = proof_text.splitlines()
                proof_body = "exact " + "\n".join(
                    [term_lines[0]]
                    + [
                        "  " + extra if extra.strip() else extra
                        for extra in term_lines[1:]
                    ]
                )
            for tactic in _tactics_in_proof(proof_body):
                if tactic not in introduced_tactics:
                    introduced_tactics.append(tactic)
                    new_tactics.append(tactic)

            bound = _binder_names(decl.signature)
            for var_line in decl.variables:
                bound |= _binder_names(var_line)
            for theorem in _theorem_refs_in_proof(proof_body, bound):
                if _resolve_project_decl(theorem, decl, decls) is not None:
                    continue  # project-local: unlocked automatically once solved
                if not _is_declared_theorem(theorem, decl, decls):
                    continue  # cannot verify it exists and is a theorem: skip it
                resolved = _resolve_inventory_name(theorem, decl, decls, theorem_index)
                if resolved is not None and resolved not in introduced_theorems:
                    introduced_theorems.append(resolved)
                    new_theorems.append(resolved)

        index = len(world.levels) + 1
        level = Level(
            index=index,
            world_id=world_id,
            file_stem=f"L{index:02d}_{decl.name.replace('.', '_')}",
            title=node.title or decl.name,
            intro_md=latex_to_markdown(node.statement_tex, refs),
            hint_md=latex_to_markdown(node.proof_tex, refs) if node.proof_tex else None,
            decl=decl,
            node=node,
            new_definitions=new_defs,
            new_tactics=new_tactics,
            new_theorems=new_theorems,
        )
        world.levels.append(level)
        level_at[pos] = level

    n_levels = len(level_order)
    for decl, _ in definitions:
        if not decl.is_definition or decl.full_name in introduced_defs:
            continue
        target_pos = max(desired_intro.get(decl.full_name, 0), stage_of[decl.full_name] + 1)
        if 1 <= target_pos <= n_levels:
            level_at[target_pos].new_definitions.append(decl)
            introduced_defs.add(decl.full_name)

    staged: dict[int, list[tuple[LeanDecl, BlueprintNode | None]]] = {}
    for pair in definitions:
        staged.setdefault(stage_of[pair[0].full_name], []).append(pair)
    stages = [DefsStage(index=0, level=None, definitions=staged.get(0, []))]
    for index_ in sorted(k for k in staged if k > 0):
        earlier = sorted(
            {
                stage_of[dep.full_name]
                for decl, _ in staged[index_]
                for dep in aux_edges.get(decl.full_name, ())
                if 0 < stage_of.get(dep.full_name, 0) < index_
            }
        )
        stages.append(
            DefsStage(
                index=index_,
                level=level_at.get(index_),
                definitions=staged[index_],
                imports=earlier,
            )
        )

    intro_world: dict[str, str] = {}
    for pos, level in level_at.items():
        for decl in level.new_definitions:
            intro_world.setdefault(decl.full_name, level.world_id)
    dependency_pairs = set(world_edges)
    for node in level_order:
        consumer_world = level_at[position[node.label]].world_id
        used_defs = {aux.full_name for aux in required_aux[node.label]}
        for use in node.uses:
            used_defs.update(
                dep.full_name for dep in def_closure_by_label.get(use, ())
            )
        for name in used_defs:
            source_world = intro_world.get(name)
            if source_world is not None and source_world != consumer_world:
                dependency_pairs.add((source_world, consumer_world))

    return Game(
        title=title,
        intro_md="Prove the theorems of this project, level by level, following its blueprint.",
        languages=languages,
        worlds=[worlds[wid] for wid in world_order],
        definitions=definitions,
        tactics=introduced_tactics,
        theorems=introduced_theorems,
        toolchain=toolchain,
        stages=stages,
        world_dependencies=sorted(dependency_pairs),
        project_scopes=frozenset(project_scopes),
        decls=decls,
    )


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------


def _doc_comment(text: str) -> str:
    """Doc comments are not string literals: only ``-/`` needs protecting."""
    return text.replace("-/", "- /")


_OPEN, _CLOSE = "([{⟨", ")]}⟩"


def _top_level_let_names(signature: str) -> set[str]:
    """Names bound by top-level ``let`` binders in a Lean signature."""
    names: set[str] = set()
    depth = 0
    i = 0
    while i < len(signature):
        ch = signature[i]
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
        elif ch == '"':
            i += 1
            while i < len(signature) and signature[i] != '"':
                i += 2 if signature[i] == "\\" else 1
        elif depth == 0 and signature.startswith("let ", i):
            match = re.match(r"let\s+([A-Za-z_][\w']*)", signature[i:])
            if match:
                names.add(match.group(1))
                i += match.end()
                continue
        i += 1
    return names


def _strip_redundant_set(proof: str, signature: str) -> str:
    """Drop a leading ``set M := ...`` that duplicates a top-level ``let M``.

    The GameServer `Statement` command runs `let_intros` before the sample
    proof, which already introduces every leading `let` binder of the
    signature. Re-issuing `set M := <same term>` after that collides with the
    introduced `M` and later `dsimp only [M]` etc. fail with "made no
    progress". So remove the now-redundant `set`.
    """
    names = _top_level_let_names(signature)
    if not names:
        return proof
    body = proof.strip("\n")
    match = re.match(r"\s*set\s+([A-Za-z_][\w']*)\s*:=\s*", body)
    if not match or match.group(1) not in names:
        return proof
    i = match.end()
    depth = 0
    while i < len(body):
        ch = body[i]
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
        elif ch == '"':
            i += 1
            while i < len(body) and body[i] != '"':
                i += 2 if body[i] == "\\" else 1
        elif ch == "\n" and depth == 0:
            i += 1
            break
        i += 1
    return body[i:].lstrip("\n")


_CHAR_LIT_RE = re.compile(r"'(?:\\[^'\\]+|[^'\\])'")


def _code_mask(text: str) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0
    last_sig = ""
    while i < n:
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
            elif text.startswith("-/", i):
                depth -= 1
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        ch = text[i]
        if ch == '"':
            out.append(" ")
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    out.append("  ")
                    i += 2
                else:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
            if i < n:
                out.append(" ")
                i += 1
            last_sig = '"'
        elif text.startswith("--", i):
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
        elif text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif (
            ch == "'"
            and not (
                last_sig.isalnum() or last_sig in "_'.!?"
            )
            and (literal := _CHAR_LIT_RE.match(text, i)) is not None
        ):
            out.extend(" " * (literal.end() - i))
            i = literal.end()
            last_sig = "'"
        else:
            out.append(ch)
            if not ch.isspace():
                last_sig = ch
            i += 1
    return "".join(out)


_HEADER_NAME_RE = re.compile(
    r"\s*(?:@[\s\S]*?\]\s*)?"
    r"(?:(?:private|protected|noncomputable|partial|scoped|local)\s+)*"
    r"(?:def|theorem|lemma|abbrev|instance|structure|class|opaque|example)\s+"
)


def _qualify_project_refs(
    text: str,
    bound: set[str],
    decl: LeanDecl,
    decls: dict[str, LeanDecl],
    namespace: str | None = None,
    opens=None,
    enclosing: str | None = None,
) -> str:
    if not text or not decls:
        return text
    if namespace is None:
        namespace = _elaboration_namespace(decl)
        if enclosing is None:
            enclosing = _context_namespace(decl)
    if opens is None:
        opens = _decl_open_entries(decl)
    masked = _code_mask(text)
    name_span: tuple[int, int] | None = None
    header = _HEADER_NAME_RE.match(masked)
    if header is not None:
        name_match = _IDENT_RE.match(masked, header.end())
        if name_match is not None:
            name_span = name_match.span()
    edits: list[tuple[int, int, str]] = []
    for match in _IDENT_RE.finditer(masked):
        raw = match.group(0)
        head = raw.split(".", 1)[0]
        if head in bound or raw.startswith("_root_."):
            continue
        if match.start() > 0 and masked[match.start() - 1] == ".":
            continue
        if name_span is not None and match.start() == name_span[0]:
            continue
        if head in _KNOWN_TACTICS or head in _TERM_KEYWORDS or head in _LEAN_KEYWORDS:
            continue
        dep = _resolve_context_decl(
            raw, namespace, opens, decls, decl.full_name, enclosing=enclosing
        )
        if dep is None:
            parts = raw.split(".")
            if len(parts) > 1 and any(
                ".".join(parts[:i]) in decl.external_namespaces
                for i in range(1, len(parts))
            ):
                continue
            probe = raw.rpartition(".")[0]
            while probe:
                dep = _resolve_context_decl(
                    probe, namespace, opens, decls, decl.full_name,
                    enclosing=enclosing,
                )
                if dep is not None:
                    break
                probe = probe.rpartition(".")[0]
            probe = probe or raw
        else:
            probe = raw
        if dep is None or dep.full_name == decl.full_name:
            continue
        edits.append(
            (
                match.start(),
                match.end(),
                f"_root_.{dep.full_name}{raw[len(probe):]}",
            )
        )
    for start, end, replacement in reversed(edits):
        text = text[:start] + replacement + text[end:]
    return text


def _emit_source(decl: LeanDecl, decls: dict[str, LeanDecl]) -> str:
    bound = _binder_names(decl.signature)
    for var_line in decl.variables:
        bound |= _binder_names(var_line)
    if decl.proof is not None:
        bound |= _proof_bound_names(decl.proof)
    if decl.keyword == "instance":
        mods = "".join(
            f"{m} " for m in decl.modifiers if m in ("noncomputable", "partial")
        )
        signature = _qualify_project_refs(decl.signature, bound, decl, decls)
        proof = _qualify_project_refs(decl.proof or "", bound, decl, decls)
        context_ns = _context_namespace(decl)
        if context_ns and decl.full_name.startswith(context_ns + "."):
            name = decl.full_name[len(context_ns) + 1 :]
        elif context_ns:
            name = f"_root_.{decl.full_name}"
        else:
            name = decl.full_name
        return f"{mods}def {name} {signature} := {proof}"
    return _qualify_project_refs(decl.source_text, bound, decl, decls)


def _context_lines(
    decl: LeanDecl, decls: dict[str, LeanDecl]
) -> tuple[list[str], list[str]]:
    """Replayable context commands, split into ``(root_lines, inner_lines)``.

    ``inner_lines`` are emitted inside the declaration's ``namespace``
    wrapper; ``root_lines`` are ``open`` commands that must be placed
    outside it (before it) because their original position was the file
    root or they were resolved to an absolute project scope — re-resolving
    them inside the wrapper could silently pick a different namespace.
    """
    root_lines: list[str] = []
    lines: list[str] = []
    seen_notations: set[LeanNotation] = set()
    registered: set[str] = set()
    context_ns = _context_namespace(decl)
    project_scopes = _project_scopes(decls)
    for command in decl.context:
        if not command.supported:
            continue
        if command.kind == "open":
            canonical = _canonical_open(
                command.source_text,
                command.namespace,
                context_ns,
                project_scopes,
            )
            for emitted, _resolution, at_root in canonical or (
                (command.source_text, command.source_text, False),
            ):
                (root_lines if at_root else lines).append(emitted)
        elif command.kind == "variable":
            bound: set[str] = set()
            for var_line in command.variables:
                bound |= _binder_names(var_line)
            lines.append(
                _qualify_project_refs(
                    command.source_text,
                    bound,
                    decl,
                    decls,
                    namespace=command.namespace,
                    opens=command.opens,
                )
            )
        elif command.kind in ("notation", "notation3"):
            notation = next(
                (
                    n
                    for n in decl.notations
                    if n.module == command.module and n.line == command.line
                ),
                None,
            )
            if notation is not None and notation not in seen_notations:
                seen_notations.add(notation)
                if notation.expression is not None:
                    expression = _qualify_project_refs(
                        notation.expression,
                        _binder_names("\n".join(notation.variables)),
                        decl,
                        decls,
                        namespace=notation.namespace,
                        opens=notation.opens,
                    )
                    lines.append(
                        f"local notation {notation.pattern} => {expression}"
                    )
                else:
                    arguments = " ".join(notation.arguments)
                    lines.append(
                        f"local notation {notation.pattern} => "
                        f"_root_.{notation.target}"
                        + (f" {arguments}" if arguments else "")
                    )
        elif command.kind == "instance":
            for inst in decl.instances:
                if (
                    inst.full_name in command.targets
                    and inst.full_name not in registered
                ):
                    registered.add(inst.full_name)
                    lines.append(
                        f"attribute [local instance] _root_.{inst.full_name}"
                    )
        elif command.kind == "attribute":
            priority = (
                f" {command.priority}" if command.priority is not None else ""
            )
            for target in command.targets:
                if command.instance_action == "disable":
                    lines.append(f"attribute [-instance] {target}")
                else:
                    lines.append(f"attribute [local instance{priority}] {target}")
    for inst in decl.instances:
        if inst.full_name not in registered:
            lines.append(f"attribute [local instance] _root_.{inst.full_name}")
    return root_lines, lines


def _context_section(
    decl: LeanDecl, decls: dict[str, LeanDecl]
) -> tuple[list[str], list[str]]:
    return _context_lines(decl, decls)


def _decl_open_lines(decl: LeanDecl) -> tuple[list[str], list[str]]:
    root: list[str] = []
    inner: list[str] = []
    for entry in decl.opens:
        tokens = entry.split()
        if any(token.startswith("_root_.") for token in tokens):
            root.append(
                " ".join(
                    token.removeprefix("_root_.") for token in tokens
                )
            )
        else:
            inner.append(entry)
    return root, inner


def _context_scaffolds(decl: LeanDecl, project_scopes: set[str]) -> list[str]:
    namespace = _context_namespace(decl)
    blocks: list[str] = []
    seen: set[str] = set()
    for opened in _opened_namespaces(
        _decl_open_entries(decl), namespace, project_scopes
    ):
        if opened in project_scopes and opened not in seen:
            seen.add(opened)
            blocks.append(f"namespace {opened}\nend {opened}")
    return blocks


def _statement_proof(level: Level, decls: dict[str, LeanDecl]) -> str:
    """Proof block of the Statement: sample solution with the LaTeX hint."""
    decl = level.decl
    lines: list[str] = []
    if level.hint_md:
        lines.append(f'Hint "{lean_interp_string(level.hint_md)}"')
    proof = (decl.proof or "").strip()
    if not proof:
        label = level.node.label if level.node is not None else decl.full_name
        raise GenerationError(
            f"level {label}: theorem {decl.full_name} has no "
            "proof to reuse as the level's sample solution"
        )
    bound = _binder_names(decl.signature) | _proof_bound_names(proof)
    for var_line in decl.variables:
        bound |= _binder_names(var_line)
    if re.match(r"by\b", proof):
        body = _strip_redundant_set(proof[2:].strip("\n"), decl.signature)
        body = _qualify_project_refs(body, bound, decl, decls)
        masked, _sheltered = _masked_source(body)
        raw = [
            (line, mask)
            for line, mask in zip(body.splitlines(), masked)
            if line.strip()
        ]
        indent = min(
            (len(line) - len(line.lstrip()) for line, mask in raw if mask.strip()),
            default=0,
        )
        lines.extend(
            line.lstrip() if not mask.strip() else line[indent:]
            for line, mask in raw
        )
    else:
        proof = _qualify_project_refs(proof, bound, decl, decls)
        term_lines = proof.splitlines()
        lines.append("exact " + term_lines[0])
        for extra in term_lines[1:]:
            lines.append("  " + extra if extra.strip() else extra)
    return "by\n" + "\n".join(f"  {line}" for line in lines)


def _render_level(
    game: Game,
    level: Level,
    previous: Level | None,
    staged_module: str | None = None,
) -> str:
    decl = level.decl
    # Levels get Mathlib transitively via Game.Metadata -> Game.Generated.Defs,
    # so we do NOT re-import Mathlib modules here (dedup saves load time).
    imports = ["import Game.Metadata"]
    if previous is not None:
        imports.append(f"import Game.Levels.{previous.world_id}.{previous.file_stem}")
    if staged_module is not None:
        imports.append(f"import {staged_module}")

    parts = [
        "\n".join(imports),
        f'World "{level.world_id}"\nLevel {level.index}',
        f'Title "{lean_string(level.title)}"',
        f'Introduction "\n{lean_string(level.intro_md)}\n"',
    ]

    world_title = next(w.title for w in game.worlds if w.world_id == level.world_id)
    context_ns = _context_namespace(decl)
    mismatched = decl.namespace != context_ns
    statement_name = decl.name if not mismatched else decl.full_name
    bound = _binder_names(decl.signature)
    for var_line in decl.variables:
        bound |= _binder_names(var_line)
    signature = _qualify_project_refs(decl.signature, bound, decl, game.decls)
    statement = (
        f"Statement {statement_name} {signature} := "
        f"{_statement_proof(level, game.decls)}"
    )
    doc = (
        f"/-- {_doc_comment(level.intro_md)} -/\n"
        f'TheoremDoc {decl.full_name} as "{decl.name}" in "{lean_string(world_title)}"'
    )
    footer = []
    if level.new_tactics:
        footer.append("NewTactic " + " ".join(_tactic_ident(t) for t in level.new_tactics))
    if level.new_definitions:
        footer.append("NewDefinition " + " ".join(d.full_name for d in level.new_definitions))
    if level.new_theorems:
        footer.append("NewTheorem " + " ".join(level.new_theorems))
    footer_block = "\n\n" + "\n".join(footer) if footer else ""

    parts.extend(_context_scaffolds(decl, game.project_scopes))
    root_lines, inner = _context_section(decl, game.decls)
    if mismatched and context_ns:
        parts_ns = context_ns.split(".")
        chain = [
            f"open {'.'.join(parts_ns[:i])}"
            for i in range(1, len(parts_ns) + 1)
        ]
        inner = chain + inner
    if inner or root_lines:
        context = "\n".join(inner) + "\n\n" if inner else ""
        body = f"{context}{doc}\n\n{statement}{footer_block}"
        if context_ns and not mismatched:
            body = f"namespace {context_ns}\n\n{body}\n\nend {context_ns}"
        root = "\n".join(root_lines) + "\n\n" if root_lines else ""
        section = (
            "noncomputable section"
            if decl.noncomputable_section
            else "section"
        )
        parts.append(f"{section}\n{root}{body}\n\nend")
    else:
        earlier: set[str] = set()
        var_lines = []
        for var_line in decl.variables:
            bound_here = earlier | _binder_names(var_line)
            var_lines.append(
                _qualify_project_refs(var_line, bound_here, decl, game.decls)
            )
            earlier = bound_here
        var_block = "\n".join(var_lines) + "\n\n" if var_lines else ""
        open_root, open_inner = _decl_open_lines(decl)
        open_block = "\n".join(open_inner) + "\n\n" if open_inner else ""
        body = f"{var_block}{open_block}{doc}\n\n{statement}{footer_block}"
        if context_ns and not mismatched:
            body = f"namespace {context_ns}\n\n{body}\n\nend {context_ns}"
        elif mismatched and context_ns:
            parts_ns = context_ns.split(".")
            chain = "\n".join(
                f"open {'.'.join(parts_ns[:i])}"
                for i in range(1, len(parts_ns) + 1)
            )
            body = f"{chain}\n\n{body}"
        root = "\n".join(open_root) + "\n\n" if open_root else ""
        if decl.noncomputable_section:
            body = f"noncomputable section\n{root}{body}\n\nend"
        else:
            body = root + body
        parts.append(body)

    parts.append('Conclusion "Level completed! 🎉"')
    return "\n\n".join(parts) + "\n"


def _render_world(world: World) -> str:
    imports = "\n".join(
        f"import Game.Levels.{world.world_id}.{level.file_stem}" for level in world.levels
    )
    intro = world.intro_md or f"Welcome to the world *{world.title}*."
    return (
        f"{imports}\n\n"
        f'World "{world.world_id}"\n'
        f'Title "{lean_string(world.title)}"\n\n'
        f'Introduction "\n{lean_string(intro)}\n"\n'
    )


def _render_game_root(game: Game, extra_imports: list[str] | None = None) -> str:
    lines = [f"import Game.Levels.{world.world_id}" for world in game.worlds]
    lines.extend(extra_imports or ())
    imports = "\n".join(lines)
    dependencies = "\n".join(
        f"Dependency {source} → {target}"
        for source, target in game.world_dependencies
    )
    dependency_block = f"{dependencies}\n\n" if dependencies else ""
    return f'''{imports}

Title "{lean_string(game.title)}"
Introduction "
{lean_string(game.intro_md)}
"

Info "
This game was generated automatically by
[proofquest](https://github.com/Mezzovilla/proofquest) from the project's
leanblueprint.
"

/-! Information to be displayed on the servers landing page. -/
Languages "{game.languages}"
CaptionShort "{lean_string(game.title)}"
CaptionLong "A game generated from a leanblueprint dependency graph, where you
prove the theorems of the original project guided by its LaTeX write-up."

{dependency_block}/-! Build the game. Shows warnings if it found a problem with your game. -/
MakeGame
'''


def _render_defs_stage(game: Game, stage: DefsStage) -> str:
    """Render one definitions module: preamble (index 0) or staged.

    The preamble additionally carries the union of the level theorems'
    external imports, because ``Game.Metadata`` is what gives every level
    file its Mathlib context. A staged module imports the level file at
    its global position instead: that pulls in ``Game.Metadata`` (and with
    it the preamble and every earlier stage), and guarantees the level
    theorems the staged declarations depend on are already in scope.
    """
    all_imports: list[str] = []
    seen: set[str] = set()
    # Collect the union of external imports needed by all definitions.
    import_decls = [decl for decl, _ in stage.definitions]
    if stage.index == 0:
        import_decls.extend(
            level.decl for world in game.worlds for level in world.levels
        )
    for decl in list(import_decls):
        import_decls.extend(decl.instances)
    for decl in import_decls:
        for imp in decl.imports:
            if imp not in seen:
                seen.add(imp)
                all_imports.append(imp)
    import_lines = [f"import {imp}" for imp in all_imports]
    if stage.index > 0:
        if stage.level is None:
            raise GenerationError(
                "internal error: staged definitions have no prerequisite level"
            )
        import_lines.append(
            f"import Game.Levels.{stage.level.world_id}.{stage.level.file_stem}"
        )
        module_of = {item.index: item.module for item in game.stages}
        import_lines.extend(
            f"import {module_of[index]}"
            for index in stage.imports
            if index in module_of
        )
    import_lines.append("import GameServer.Commands")
    parts = ["\n".join(import_lines)]
    scaffold_seen: set[str] = set()
    for decl, node in stage.definitions:
        doc_md = (
            latex_to_markdown(node.statement_tex) if node else f"Definition `{decl.full_name}`."
        )
        for scaffold in _context_scaffolds(decl, game.project_scopes):
            if scaffold not in scaffold_seen:
                scaffold_seen.add(scaffold)
                parts.append(scaffold)
        root_lines, inner = _context_section(decl, game.decls)
        doc = (
            f"/-- {_doc_comment(doc_md)} -/\n"
            f'DefinitionDoc {decl.full_name} as "{decl.name}"'
        )
        source = _emit_source(decl, game.decls)
        context_ns = _context_namespace(decl)
        if inner or root_lines:
            context = "\n".join(inner) + "\n\n" if inner else ""
            block = f"{context}{source}\n\n{doc}"
            if context_ns:
                block = (
                    f"namespace {context_ns}\n\n{block}\n\nend {context_ns}"
                )
            root = "\n".join(root_lines) + "\n\n" if root_lines else ""
            section = (
                "noncomputable section"
                if decl.noncomputable_section
                else "section"
            )
            block = f"{section}\n{root}{block}\n\nend"
        else:
            earlier: set[str] = set()
            var_lines = []
            for var_line in decl.variables:
                bound_here = earlier | _binder_names(var_line)
                var_lines.append(
                    _qualify_project_refs(
                        var_line, bound_here, decl, game.decls
                    )
                )
                earlier = bound_here
            var_block = "\n".join(var_lines) + "\n\n" if var_lines else ""
            open_root, open_inner = _decl_open_lines(decl)
            open_block = "\n".join(open_inner) + "\n\n" if open_inner else ""
            block = f"{var_block}{open_block}{source}\n\n{doc}"
            if context_ns:
                block = (
                    f"namespace {context_ns}\n\n{block}\n\nend {context_ns}"
                )
            root = "\n".join(open_root) + "\n\n" if open_root else ""
            if decl.noncomputable_section:
                block = f"noncomputable section\n{root}{block}\n\nend"
            else:
                block = root + block
        parts.append(block)
    return "\n\n".join(parts) + "\n"


def _render_defs(game: Game) -> str:
    """Preamble module only: everything without a level prerequisite."""
    preamble = (
        game.stages[0].definitions if game.stages else game.definitions
    )
    return _render_defs_stage(game, DefsStage(index=0, definitions=preamble))


def _render_tactic_docs(game: Game) -> str:
    parts = ["import Game.Generated.Defs"]
    for tactic in game.tactics:
        doc = _TACTIC_DOCS.get(tactic, f"The `{tactic}` tactic.")
        parts.append(f"/-- {_doc_comment(doc)} -/\nTacticDoc {_tactic_ident(tactic)}")
    return "\n\n".join(parts) + "\n"


def _render_theorem_docs(game: Game) -> str:
    # These are external (e.g. Mathlib) theorems referenced by sample proofs,
    # so there is no local docstring to reuse: link to the mathlib doc page.
    parts = ["import Game.Generated.Defs"]
    legacy = _legacy_doc_syntax(game.toolchain)
    for theorem in game.theorems:
        if legacy:
            parts.append(
                f"/-- [[mathlib_doc]] -/\n"
                f'TheoremDoc {theorem} as "{theorem}" in "Theorems"'
            )
        else:
            parts.append(f'/-- [[mathlib_doc]] -/\nTheoremDoc {theorem} as "{theorem}"')
    return "\n\n".join(parts) + "\n"


_METADATA = """import GameServer
import Game.Generated.Defs
import Game.Generated.TacticDocs
import Game.Generated.TheoremDocs

/-! Things imported here are available in all levels. -/
"""

_LAKEFILE = '''import Lake
open Lake DSL

-- Using this assumes that each dependency has a tag of the form `v4.X.0`.
def leanVersion : String := s!"v{Lean.versionString}"

/--
Use the GameServer from a `lean4game` folder lying next to the game on your local computer.
Activated with `lake update -Klean4game.local`.
-/
def LocalGameServer : Dependency := {
  name := `GameServer
  scope := "hhu-adam"
  src? := DependencySrc.path "../lean4game/server"
  version? := none
  opts := ∅
}

/--
Use the GameServer version from github.
Deactivate local version with `lake update -R`.
-/
def RemoteGameServer : Dependency := {
  name := `GameServer
  scope := "hhu-adam"
  src? := DependencySrc.git "https://github.com/leanprover-community/lean4game.git" leanVersion "server"
  version? := s!"git#{leanVersion}"
  opts := ∅
}

/-
Choose GameServer dependency depending on whether `-Klean4game.local` has been passed to `lake`.
-/
open Lean in
#eval (do
  let gameServerName := if get_config? lean4game.local |>.isSome then
    ``LocalGameServer else ``RemoteGameServer
  modifyEnv (fun env => Lake.packageDepAttr.ext.addEntry env gameServerName)
  : Elab.Command.CommandElabM Unit)

package Game where
  leanOptions := #[
    ⟨`linter.all, false⟩,
    ⟨`pp.showLetValues, true⟩,
    ⟨`tactic.hygienic, false⟩]
  moreLeanArgs := #[
    "-Dtrace.debug=false"]
  moreServerOptions := #[
    ⟨`trace.debug, true⟩]

require "leanprover-community" / mathlib @ git leanVersion

@[default_target]
lean_lib Game
'''

_GITIGNORE = """.lake/
"""


def write_game(game: Game, output_dir: Path) -> list[Path]:
    """Render the game to ``output_dir``; returns the list of files written."""
    stages = game.stages or [DefsStage(index=0, definitions=game.definitions)]
    stage_by_index = {stage.index: stage for stage in stages}
    n_levels = sum(len(world.levels) for world in game.worlds)
    trailing = (
        f"import {stages[-1].module}"
        if n_levels > 0 and stages[-1].index == n_levels and stages[-1].definitions
        else None
    )

    files: list[tuple[str, str]] = [
        ("Game.lean", _render_game_root(game, [trailing] if trailing else None)),
        ("Game/Metadata.lean", _METADATA),
    ]
    for stage in stages:
        files.append(
            (
                f"Game/Generated/{stage.module_stem}.lean",
                _render_defs_stage(game, stage),
            )
        )
    files.append(("Game/Generated/TacticDocs.lean", _render_tactic_docs(game)))
    files.append(("Game/Generated/TheoremDocs.lean", _render_theorem_docs(game)))

    previous: Level | None = None
    position = 0
    for world in game.worlds:
        files.append(
            (f"Game/Levels/{world.world_id}.lean", _render_world(world))
        )
        for level in world.levels:
            position += 1
            stage = stage_by_index.get(position - 1)
            if stage is not None and stage.index == 0:
                stage = None
            files.append(
                (
                    f"Game/Levels/{world.world_id}/{level.file_stem}.lean",
                    _render_level(
                        game,
                        level,
                        previous,
                        staged_module=(
                            stage.module if stage is not None else None
                        ),
                    ),
                )
            )
            previous = level

    files.append(("lakefile.lean", _LAKEFILE))
    files.append(("lean-toolchain", game.toolchain.strip() + "\n"))
    files.append((".gitignore", _GITIGNORE))
    files.append(
        (
            "README.md",
            (
                f"# {game.title}\n\n"
                "This game was generated by [proofquest] from a leanblueprint"
                " project.\n\n"
                "Build it with `lake update -R && lake build`, then host it"
                " locally with\n"
                "`proofquest serve <this-folder>` (no lean4game clone needed).\n"
            ),
        )
    )

    written: list[Path] = []
    for relative, content in files:
        path = output_dir / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        written.append(path)
    return written
