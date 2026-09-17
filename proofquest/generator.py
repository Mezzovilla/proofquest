"""Assemble the game model and render the GameSkeleton file tree."""

from __future__ import annotations

import re
from pathlib import Path

from .dep_graph import topological_order
from .game_model import Blueprint, BlueprintNode, Game, LeanDecl, Level, World
from .latex_to_md import latex_to_markdown, lean_interp_string, lean_string

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
_IDENT_PART = r"[A-Za-z_][A-Za-z0-9_'₀₁₂₃₄₅₆₇₈₉]*"
_IDENT_RE = re.compile(_IDENT_PART + r"(?:\." + _IDENT_PART + r")*")

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

_HAVE_LET_SET_RE = re.compile(r"\b(?:have|let|set|by_contra|by_cases|generalize)\s+([A-Za-z_][A-Za-z0-9_']*)")
_INTRO_RE = re.compile(r"\b(?:intro|intros|rintro)\s+([^\n]*)")
_OBTAIN_RE = re.compile(r"\bobtain\s+([^\n]*?)\s*:=")
_RCASES_WITH_RE = re.compile(r"\brcases\b[^\n]*?\bwith\s+([^\n]*)")
_FUN_RE = re.compile(r"\bfun\s+([^\n]*?)=>")
_FORALL_EXISTS_RE = re.compile(r"[∀∃]\s*([^,]*),")
_CHOOSE_RE = re.compile(r"\bchoose\s+([^\n]*?)\busing\b")
_SET_WITH_RE = re.compile(r"\bwith\s+([A-Za-z_][A-Za-z0-9_']*)")


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
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", token):
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
    for regex in (_INTRO_RE, _OBTAIN_RE, _RCASES_WITH_RE, _FUN_RE, _FORALL_EXISTS_RE, _CHOOSE_RE):
        for match in regex.finditer(proof):
            names.update(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", match.group(1)))
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


def _qualified_candidates(name: str, decl: LeanDecl) -> list[str]:
    """Ways ``name`` (as literally written in ``decl``'s proof) might resolve:
    as-is, qualified by ``decl``'s own namespace, or by one of its ``open``s.
    """
    candidates = [name]
    if decl.namespace:
        candidates.append(f"{decl.namespace}.{name}")
    for open_stmt in decl.opens:
        namespace = open_stmt.removeprefix("open ").strip()
        if namespace:
            candidates.append(f"{namespace}.{name}")
    return candidates


def _resolve_project_decl(
    name: str, decl: LeanDecl, decls: dict[str, LeanDecl]
) -> LeanDecl | None:
    """Look up a proof-referenced identifier among the project's own declarations.

    Project-local theorems become their own level and are unlocked
    automatically by the GameServer once that level is solved, so they must
    not be re-declared with `NewTheorem` (and project-local definitions are
    handled separately, via the blueprint's `\\uses` graph).
    """
    for candidate in _qualified_candidates(name, decl):
        found = decls.get(candidate)
        if found is not None:
            return found
    return None


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
    for candidate in _qualified_candidates(name, decl):
        found = decls.get(candidate)
        if found is not None:
            return found.keyword in ("theorem", "lemma")
    return _looks_like_theorem_name(name)


class GenerationError(Exception):
    pass


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


def build_game(
    blueprint: Blueprint,
    decls: dict[str, LeanDecl],
    toolchain: str,
    title: str,
    languages: str = "en",
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

    definitions: list[tuple[LeanDecl, BlueprintNode | None]] = []
    def_by_label: dict[str, LeanDecl] = {}
    for node in order:
        if node.is_theorem:
            continue
        decl = node_decl(node)
        if decl is None:
            raise GenerationError(
                f"{node.label}: definition has no matching Lean declaration "
                f"(\\lean{{{', '.join(node.lean_names) or '?'}}})"
            )
        definitions.append((decl, node))
        def_by_label[node.label] = decl

    worlds: dict[str, World] = {}
    world_order: list[str] = []
    introduced_defs: set[str] = set()
    introduced_tactics: list[str] = []
    introduced_theorems: list[str] = []

    for node in order:
        if not node.is_theorem:
            continue
        decl = node_decl(node)
        if decl is None:
            raise GenerationError(
                f"{node.label}: theorem has no matching Lean declaration "
                f"(\\lean{{{', '.join(node.lean_names) or '?'}}})"
            )
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

        new_defs: list[LeanDecl] = []
        for use in node.uses:
            used = by_label.get(use)
            if used is not None and not used.is_theorem and use not in introduced_defs:
                introduced_defs.add(use)
                new_defs.append(def_by_label[use])

        new_tactics: list[str] = []
        new_theorems: list[str] = []
        if decl.proof and decl.proof.lstrip().startswith("by"):
            proof_body = decl.proof.lstrip()[2:]
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
                if theorem not in introduced_theorems:
                    introduced_theorems.append(theorem)
                    new_theorems.append(theorem)

        index = len(world.levels) + 1
        world.levels.append(
            Level(
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
        )

    return Game(
        title=title,
        intro_md="Prove the theorems of this project, level by level, following its blueprint.",
        languages=languages,
        worlds=[worlds[wid] for wid in world_order],
        definitions=definitions,
        tactics=introduced_tactics,
        theorems=introduced_theorems,
        toolchain=toolchain,
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


def _statement_proof(level: Level) -> str:
    """Proof block of the Statement: sample solution with the LaTeX hint."""
    lines: list[str] = []
    if level.hint_md:
        lines.append(f'Hint "{lean_interp_string(level.hint_md)}"')
    proof = (level.decl.proof or "").strip()
    if proof.startswith("by"):
        body = _strip_redundant_set(proof[2:].strip("\n"), level.decl.signature)
        raw = [line for line in body.splitlines() if line.strip()]
        indent = min(len(line) - len(line.lstrip()) for line in raw) if raw else 0
        lines.extend(line[indent:] for line in raw)
    else:
        lines.append("sorry")
    return "by\n" + "\n".join(f"  {line}" for line in lines)


def _render_level(game: Game, level: Level, previous: Level | None) -> str:
    decl = level.decl
    # Levels get Mathlib transitively via Game.Metadata -> Game.Generated.Defs,
    # so we do NOT re-import Mathlib modules here (dedup saves load time).
    imports = ["import Game.Metadata"]
    if previous is not None:
        imports.append(f"import Game.Levels.{previous.world_id}.{previous.file_stem}")

    parts = [
        "\n".join(imports),
        f'World "{level.world_id}"\nLevel {level.index}',
        f'Title "{lean_string(level.title)}"',
        f'Introduction "\n{lean_string(level.intro_md)}\n"',
    ]

    world_title = next(w.title for w in game.worlds if w.world_id == level.world_id)
    statement = f"Statement {decl.name} {decl.signature} := {_statement_proof(level)}"
    doc = (
        f"/-- {_doc_comment(level.intro_md)} -/\n"
        f'TheoremDoc {decl.full_name} as "{decl.name}" in "{lean_string(world_title)}"'
    )
    var_block = "\n".join(decl.variables) + "\n\n" if decl.variables else ""
    open_block = "\n".join(decl.opens) + "\n\n" if decl.opens else ""
    if decl.namespace:
        parts.append(
            f"namespace {decl.namespace}\n\n{var_block}{open_block}{doc}\n\n{statement}\n\nend {decl.namespace}"
        )
    else:
        parts.append(f"{var_block}{open_block}{doc}\n\n{statement}")

    parts.append('Conclusion "Level completed! 🎉"')

    footer = []
    if level.new_tactics:
        footer.append("NewTactic " + " ".join(_tactic_ident(t) for t in level.new_tactics))
    if level.new_definitions:
        footer.append("NewDefinition " + " ".join(d.full_name for d in level.new_definitions))
    if level.new_theorems:
        footer.append("NewTheorem " + " ".join(level.new_theorems))
    if footer:
        parts.append("\n".join(footer))
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


def _render_game_root(game: Game) -> str:
    imports = "\n".join(f"import Game.Levels.{world.world_id}" for world in game.worlds)
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

/-! Build the game. Shows warnings if it found a problem with your game. -/
MakeGame
'''


def _render_defs(game: Game) -> str:
    # Collect the union of external imports needed by all definitions.
    all_imports: list[str] = []
    seen: set[str] = set()
    for decl, _ in game.definitions:
        for imp in decl.imports:
            if imp not in seen:
                seen.add(imp)
                all_imports.append(imp)
    import_block = "\n".join(f"import {imp}" for imp in all_imports)
    parts = [f"{import_block}\nimport GameServer.Commands"] if all_imports else ["import GameServer.Commands"]
    # Collect the union of `open` statements needed by all definitions.
    all_opens: list[str] = []
    seen_opens: set[str] = set()
    for decl, _ in game.definitions:
        for op in decl.opens:
            if op not in seen_opens:
                seen_opens.add(op)
                all_opens.append(op)
    if all_opens:
        parts.append("\n".join(all_opens))
    for decl, node in game.definitions:
        doc_md = (
            latex_to_markdown(node.statement_tex) if node else f"Definition `{decl.full_name}`."
        )
        var_block = "\n".join(decl.variables) + "\n\n" if decl.variables else ""
        block = (
            f"{var_block}{decl.source_text}\n\n"
            f"/-- {_doc_comment(doc_md)} -/\n"
            f'DefinitionDoc {decl.full_name} as "{decl.name}"'
        )
        if decl.namespace:
            block = f"namespace {decl.namespace}\n\n{block}\n\nend {decl.namespace}"
        parts.append(block)
    return "\n\n".join(parts) + "\n"


def _render_tactic_docs(game: Game) -> str:
    parts = ["import GameServer.Commands"]
    for tactic in game.tactics:
        doc = _TACTIC_DOCS.get(tactic, f"The `{tactic}` tactic.")
        parts.append(f"/-- {_doc_comment(doc)} -/\nTacticDoc {_tactic_ident(tactic)}")
    return "\n\n".join(parts) + "\n"


def _render_theorem_docs(game: Game) -> str:
    # These are external (e.g. Mathlib) theorems referenced by sample proofs,
    # so there is no local docstring to reuse: link to the mathlib doc page.
    parts = ["import GameServer.Commands"]
    for theorem in game.theorems:
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
    written: list[Path] = []

    def emit(relative: str, content: str) -> None:
        path = output_dir / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        written.append(path)

    emit("Game.lean", _render_game_root(game))
    emit("Game/Metadata.lean", _METADATA)
    emit("Game/Generated/Defs.lean", _render_defs(game))
    emit("Game/Generated/TacticDocs.lean", _render_tactic_docs(game))
    emit("Game/Generated/TheoremDocs.lean", _render_theorem_docs(game))

    previous: Level | None = None
    for world in game.worlds:
        emit(f"Game/Levels/{world.world_id}.lean", _render_world(world))
        for level in world.levels:
            emit(
                f"Game/Levels/{world.world_id}/{level.file_stem}.lean",
                _render_level(game, level, previous),
            )
            previous = level

    emit("lakefile.lean", _LAKEFILE)
    emit("lean-toolchain", game.toolchain.strip() + "\n")
    emit(".gitignore", _GITIGNORE)
    emit(
        "README.md",
        f"# {game.title}\n\n"
        "This game was generated by [proofquest] from a leanblueprint project.\n\n"
        "Build it with `lake update -R && lake build`, then host it locally with\n"
        "`proofquest serve <this-folder>` (no lean4game clone needed).\n",
    )
    return written
