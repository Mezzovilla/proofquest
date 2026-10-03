import pytest

from proofquest.game_model import Blueprint, BlueprintNode, LeanDecl
from proofquest.generator import (
    GenerationError,
    _binder_names,
    _is_declared_theorem,
    _looks_like_theorem_name,
    _resolve_project_decl,
    _strip_accessor_suffix,
    _theorem_refs_in_proof,
    build_game,
)

MAX_GT_MEAN_PROOF = """
  have h1 : max a b ≥ a := le_max_left a b
  have h2 : max a b ≥ b := le_max_right a b
  have h3 : a + b ≤ max a b + max a b := add_le_add h1 h2
  have h4 : (a + b) / 2 ≤ (max a b + max a b) / 2 :=
    div_le_div_of_nonneg_right h3 (by norm_num)
  calc
    (a + b) / 2 ≤ (max a b + max a b) / 2 := h4
    _ = max a b := by ring
"""


def test_theorem_refs_detects_lemmas_used_by_the_proof():
    bound = _binder_names("(a b : ℝ) : max a b ≥ (a+b)/2")
    refs = _theorem_refs_in_proof(MAX_GT_MEAN_PROOF, bound)
    assert "le_max_left" in refs
    assert "le_max_right" in refs


def test_theorem_refs_does_not_include_tactics():
    bound = _binder_names("(a b : ℝ) : max a b ≥ (a+b)/2")
    refs = _theorem_refs_in_proof(MAX_GT_MEAN_PROOF, bound)
    for tactic in ("have", "calc", "ring", "norm_num", "linarith"):
        assert tactic not in refs
    # `linarith` isn't used by this proof at all, tactic or otherwise.
    assert "linarith" not in MAX_GT_MEAN_PROOF


def test_theorem_refs_ignores_bound_names():
    bound = _binder_names("(a b : ℝ) : max a b ≥ (a+b)/2")
    refs = _theorem_refs_in_proof(MAX_GT_MEAN_PROOF, bound)
    # `a`, `b` (signature) and `h1`..`h4` (`have`) are local, not theorems.
    for local in ("a", "b", "h1", "h2", "h3", "h4"):
        assert local not in refs


def test_theorem_refs_ignores_comments():
    proof = """
  -- an auxiliary lemma about convergence, see the tail estimate
  have h :=
    foo_bar baz_qux
  exact h
"""
    refs = _theorem_refs_in_proof(proof, set())
    assert "foo_bar" in refs
    assert "baz_qux" in refs
    for word in ("auxiliary", "lemma", "about", "convergence", "the", "tail", "estimate", "see"):
        assert word not in refs


def test_theorem_refs_ignores_dot_notation_on_compound_terms():
    # `(T (α n)).le_opNorm` is generalized field notation on the *application*
    # `T (α n)`, not a literal `le_opNorm` in scope: there is no way to
    # recover `ContinuousLinearMap.le_opNorm` (the real name) from syntax
    # alone, so the bogus bare `le_opNorm` must not be reported either.
    proof = """
  have h_op_norm : ‖T (α n) (x - x_seq n)‖ ≤ ‖T (α n)‖ * ‖x - x_seq n‖ :=
    (T (α n)).le_opNorm (x - x_seq n)
"""
    refs = _theorem_refs_in_proof(proof, {"T", "α", "n", "x", "x_seq"})
    assert "le_opNorm" not in refs


def test_theorem_refs_ignores_calc_placeholder():
    proof = """
  calc a = b := h1
    _ = c := h2
"""
    refs = _theorem_refs_in_proof(proof, {"a", "b", "c", "h1", "h2"})
    assert "_" not in refs


def test_theorem_refs_strips_generalized_field_notation():
    # `mem_ball_zero_iff.mp` and `inv_pos.mpr` are dot-notation projections on
    # a *result*, not literal declaration names; only `getConstInfo`-safe
    # names (the stripped prefixes) may end up in a `NewTheorem` command.
    proof = """
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  have : r⁻¹ * ‖z‖ < r⁻¹ * r := mul_lt_mul_of_pos_left hzr (inv_pos.mpr h1)
"""
    refs = _theorem_refs_in_proof(proof, {"x", "hx", "hzr", "h1", "r", "z"})
    assert "mem_ball_zero_iff" in refs
    assert "inv_pos" in refs
    assert "mem_ball_zero_iff.mp" not in refs
    assert "inv_pos.mpr" not in refs


def test_strip_accessor_suffix():
    assert _strip_accessor_suffix("mem_ball_zero_iff.mp") == "mem_ball_zero_iff"
    assert _strip_accessor_suffix("inv_pos.mpr") == "inv_pos"
    assert _strip_accessor_suffix("Nat.succ_pos") == "Nat.succ_pos"  # not an accessor
    assert _strip_accessor_suffix("le_max_left") == "le_max_left"


def test_looks_like_theorem_name():
    assert _looks_like_theorem_name("le_max_left")
    assert _looks_like_theorem_name("ContinuousLinearMap.sSup_unit_ball_eq_norm")
    assert not _looks_like_theorem_name("sSup")
    assert not _looks_like_theorem_name("max")
    assert not _looks_like_theorem_name("Nat.rec")


def _decl(**overrides):
    base = {
        "keyword": "theorem",
        "name": "d",
        "full_name": "d",
        "namespace": "",
        "signature": "",
        "proof": None,
        "source_text": "",
    }
    base.update(overrides)
    return LeanDecl(**base)


def test_is_declared_theorem_rejects_names_with_no_underscore():
    # `sSup` is a real Mathlib identifier, but a definition/class field, not
    # a `theorem`/`lemma`, and it isn't declared in the (empty, here) project
    # sources either — the naming-convention fallback must reject it, since
    # a wrong `NewTheorem sSup` would fail `lake build`.
    caller = _decl(name="caller", full_name="caller")
    assert not _is_declared_theorem("sSup", caller, {})
    assert not _is_declared_theorem("max", caller, {})
    # Real (compound-proposition) theorem names always have an underscore
    # somewhere, including Lean *core* library lemmas never fetched by lake
    # (so they can't be cross-checked against any dependency source), e.g.:
    assert _is_declared_theorem("le_max_left", caller, {})
    assert _is_declared_theorem("Nat.succ_pos", caller, {})


def test_is_declared_theorem_uses_project_decls_when_available():
    lemma1 = _decl(
        keyword="theorem", name="lemma1", full_name="Toy.lemma1", namespace="Toy"
    )
    caller_in_toy = _decl(name="caller", full_name="Toy.caller", namespace="Toy")
    assert _is_declared_theorem("lemma1", caller_in_toy, {"Toy.lemma1": lemma1})

    # A project definition by that name must not be treated as a theorem,
    # even though its short name contains no underscore-based hint either way.
    a_def = _decl(keyword="def", name="A", full_name="Toy.A", namespace="Toy")
    assert not _is_declared_theorem("A", caller_in_toy, {"Toy.A": a_def})


def test_resolve_project_decl_finds_namespaced_theorem():
    lemma2 = LeanDecl(
        keyword="theorem",
        name="lemma2",
        full_name="Toy.lemma2",
        namespace="Toy",
        signature="(n : Nat) : A (n + 1)",
        proof="by unfold A; omega",
        source_text="theorem lemma2 ...",
    )
    decls = {"Toy.lemma2": lemma2}
    lemma3 = LeanDecl(
        keyword="theorem",
        name="lemma3",
        full_name="Toy.lemma3",
        namespace="Toy",
        signature="(n : Nat) : A n ∧ B (n + 1)",
        proof="by have h := lemma2 (n + 1); exact h",
        source_text="theorem lemma3 ...",
    )
    assert _resolve_project_decl("lemma2", lemma3, decls) is lemma2
    assert _resolve_project_decl("le_max_left", lemma3, decls) is None


def _node(label, chapter, order):
    return BlueprintNode(
        kind="theorem",
        label=label,
        lean_names=[label],
        title=None,
        statement_tex="",
        proof_tex=None,
        uses=[],
        leanok=True,
        chapter=chapter,
        section=None,
        order=order,
    )


def test_build_game_rejects_distinct_chapters_with_same_world_id():
    blueprint = Blueprint(
        nodes=[_node("first", "A B", 0), _node("second", "A-B", 1)],
        chapters=["A B", "A-B"],
    )
    decls = {
        "first": _decl(name="first", full_name="first"),
        "second": _decl(name="second", full_name="second"),
    }

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.19.0", title="Test")

    message = str(exc_info.value)
    assert "A B" in message
    assert "A-B" in message
    assert "AB" in message


def _def_node(label, lean_names, order, uses=()):
    return BlueprintNode(
        kind="definition",
        label=label,
        lean_names=list(lean_names),
        title=None,
        statement_tex=f"Statement of {label}.",
        proof_tex=None,
        uses=list(uses),
        leanok=True,
        chapter="Ch",
        section=None,
        order=order,
    )


def _theorem_node(label, order, uses=()):
    node = _node(label, "Ch", order)
    node.lean_names = [label.removeprefix("lem:")]
    node.uses = list(uses)
    return node


def test_grouped_definition_copies_all_names_once():
    blueprint = Blueprint(
        nodes=[
            _def_node("def:AB", ["Toy.A", "Toy.B"], 0),
            _theorem_node("lem:t", 1, uses=["def:AB"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Toy.A": _decl(keyword="def", name="A", full_name="Toy.A", namespace="Toy",
                       source_text="def A : Nat :=\n  1"),
        "Toy.B": _decl(keyword="def", name="B", full_name="Toy.B", namespace="Toy",
                       source_text="def B : Nat :=\n  A"),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    copied = [decl.full_name for decl, _ in game.definitions]
    assert copied == ["Toy.A", "Toy.B"]
    assert [node.label for _, node in game.definitions] == ["def:AB", "def:AB"]
    level = game.worlds[0].levels[0]
    assert [d.full_name for d in level.new_definitions] == ["Toy.A", "Toy.B"]


def test_grouped_definition_missing_name_is_error():
    blueprint = Blueprint(
        nodes=[_def_node("def:AB", ["Toy.A", "Toy.nope"], 0)],
        chapters=["Ch"],
    )
    decls = {"Toy.A": _decl(keyword="def", name="A", full_name="Toy.A")}

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    message = str(exc_info.value)
    assert "Toy.nope" in message
    assert "def:AB" in message


def test_definition_without_lean_fails_generation():
    blueprint = Blueprint(nodes=[_def_node("def:none", [], 0)], chapters=["Ch"])
    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, {}, toolchain="v4.31.0", title="T")
    assert "no matching Lean declaration" in str(exc_info.value)


def test_definition_dependencies_are_copied_first():
    """A copied definition's project-local deps land in Defs.lean before it."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            _theorem_node("lem:t", 1, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Toy.A": _decl(keyword="def", name="A", full_name="Toy.A", namespace="Toy",
                       source_text="def A : Nat :=\n  1"),
        "Toy.B": _decl(keyword="def", name="B", full_name="Toy.B", namespace="Toy",
                       source_text="def B : Nat :=\n  A + 1"),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    copied = [decl.full_name for decl, _ in game.definitions]
    assert copied == ["Toy.A", "Toy.B"]
    assert game.definitions[0][1] is None
    level = game.worlds[0].levels[0]
    assert [d.full_name for d in level.new_definitions] == ["Toy.A", "Toy.B"]


def test_definition_depending_on_blueprint_theorem_is_error():
    """A copied def referencing a blueprint theorem would dangle in
    Defs.lean (the theorem becomes a `Statement` level, not a copied decl);
    it must fail loudly, naming the definition label and the theorem."""
    helper = _theorem_node("lem:helper", 1)
    helper.lean_names = ["helper_lemma"]
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            helper,
            _theorem_node("lem:t", 2, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Toy.B": _decl(keyword="def", name="B", full_name="Toy.B", namespace="Toy",
                       source_text="def B : Nat :=\n  if helper_lemma then 1 else 2"),
        "helper_lemma": _decl(name="helper_lemma", full_name="helper_lemma",
                              proof="by trivial"),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    message = str(exc_info.value)
    assert "def:b" in message
    assert "helper_lemma" in message
    assert "Toy.B" in message
    assert "\\uses" not in message


def test_definition_transitive_blueprint_theorem_dep_is_error():
    """The same failure must fire through an intermediate copied decl."""
    helper = _theorem_node("lem:helper", 1)
    helper.lean_names = ["helper_lemma"]
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            helper,
            _theorem_node("lem:t", 2, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Toy.B": _decl(keyword="def", name="B", full_name="Toy.B", namespace="Toy",
                       source_text="def B : Nat :=\n  mid"),
        "Toy.mid": _decl(keyword="def", name="mid", full_name="Toy.mid",
                         namespace="Toy",
                         source_text="def mid : Nat :=\n  helper_lemma"),
        "helper_lemma": _decl(name="helper_lemma", full_name="helper_lemma",
                              proof="by trivial"),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    message = str(exc_info.value)
    assert "def:b" in message
    assert "helper_lemma" in message
    assert "Toy.mid" in message
    assert "\\uses" not in message


def test_source_refs_resolve_root_qualified_names():
    """`_root_.Foo.bar` in source resolves to the `Foo.bar` decl key."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            _theorem_node("lem:t", 1, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Toy.A": _decl(keyword="def", name="A", full_name="Toy.A", namespace="Toy",
                       source_text="def A : Nat :=\n  1"),
        "Toy.B": _decl(keyword="def", name="B", full_name="Toy.B", namespace="Toy",
                       source_text="def B : Nat :=\n  _root_.Toy.A + 1"),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    copied = [decl.full_name for decl, _ in game.definitions]
    assert copied == ["Toy.A", "Toy.B"]


def test_source_refs_ignore_string_literals_and_local_binders():
    """Identifiers inside string literals or bound by let/fun in the body are
    not dependencies, even if a project decl happens to share their name."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            _theorem_node("lem:t", 1, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Toy.B": _decl(
            keyword="def", name="B", full_name="Toy.B", namespace="Toy",
            source_text=(
                'def B : String :=\n'
                '  let msg := "Uses fake_dep and other_dep"\n'
                '  msg'
            ),
        ),
        "Toy.fake_dep": _decl(keyword="def", name="fake_dep",
                              full_name="Toy.fake_dep", namespace="Toy",
                              source_text="def fake_dep : Nat :=\n  0"),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    copied = [decl.full_name for decl, _ in game.definitions]
    assert copied == ["Toy.B"]


_SOLUTION_DECL = _decl(
    keyword="structure", name="Solution", full_name="Solution",
    signature="where\n  (a : Nat)",
    source_text="structure Solution where\n  (a : Nat)",
)


def test_field_notation_dep_on_sibling_def_is_copied_first():
    """`S.y` where `S : Solution` is receiver-type-directed dot notation for
    `Solution.y`; it must land in Defs.lean *before* the declaration that
    uses it, like the source order."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:spec", ["Toy.y_spec"], 0),
            _theorem_node("lem:t", 1, uses=["def:spec"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Solution": _SOLUTION_DECL,
        "Solution.y": _decl(keyword="def", name="y", full_name="Solution.y",
                            namespace="Solution",
                            source_text="def y : Nat :=\n  1"),
        "Toy.y_spec": _decl(
            keyword="def", name="y_spec", full_name="Toy.y_spec", namespace="Toy",
            signature="(S : Solution) : Nat",
            source_text="def y_spec (S : Solution) : Nat :=\n  S.y + 1",
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    copied = [decl.full_name for decl, _ in game.definitions]
    assert copied == ["Solution", "Solution.y", "Toy.y_spec"]


def test_field_notation_shared_suffix_is_not_ambiguous_when_typed():
    """`S.y` with `S : Solution` resolves to `Solution.y` only; unrelated
    declarations sharing the `y` tail neither hijack nor make it ambiguous."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:spec", ["Toy.y_spec"], 0),
            _theorem_node("lem:t", 1, uses=["def:spec"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Solution": _SOLUTION_DECL,
        "Solution.y": _decl(keyword="def", name="y", full_name="Solution.y",
                            namespace="Solution",
                            source_text="def y : Nat :=\n  1"),
        "Other.y": _decl(keyword="def", name="y", full_name="Other.y",
                         namespace="Other",
                         source_text="def y : Nat :=\n  2"),
        "Toy.y_spec": _decl(
            keyword="def", name="y_spec", full_name="Toy.y_spec", namespace="Toy",
            signature="(S : Solution) : Nat",
            source_text="def y_spec (S : Solution) : Nat :=\n  S.y + 1",
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    copied = [decl.full_name for decl, _ in game.definitions]
    assert copied == ["Solution", "Solution.y", "Toy.y_spec"]


def test_field_notation_external_receiver_ignores_project_suffix():
    """`n.succ` with `n : Nat` is `Nat.succ`, not the unrelated project
    declaration `Foo.succ`: no dependency is invented."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            _theorem_node("lem:t", 1, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Foo.succ": _decl(keyword="def", name="succ", full_name="Foo.succ",
                          namespace="Foo",
                          source_text="def succ (n : Nat) : Nat :=\n  n"),
        "Toy.B": _decl(
            keyword="def", name="B", full_name="Toy.B", namespace="Toy",
            signature="(n : Nat) : Nat",
            source_text="def B (n : Nat) : Nat :=\n  n.succ",
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    copied = [decl.full_name for decl, _ in game.definitions]
    assert copied == ["Toy.B"]


def test_field_notation_val_resolves_real_decl_before_accessor_stripping():
    """`S.val` may denote a real declaration `Solution.val`; the generic
    `.val` accessor stripping must not hide it."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:spec", ["Toy.spec"], 0),
            _theorem_node("lem:t", 1, uses=["def:spec"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Solution": _SOLUTION_DECL,
        "Solution.val": _decl(keyword="def", name="val", full_name="Solution.val",
                              namespace="Solution",
                              source_text="def val : Nat :=\n  1"),
        "Toy.spec": _decl(
            keyword="def", name="spec", full_name="Toy.spec", namespace="Toy",
            signature="(S : Solution) : Nat",
            source_text="def spec (S : Solution) : Nat :=\n  S.val",
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    copied = [decl.full_name for decl, _ in game.definitions]
    assert copied == ["Solution", "Solution.val", "Toy.spec"]


def test_field_notation_dep_on_blueprint_theorem_is_error():
    """`S.two_le_multiplicity` (dot notation on `S : Solution`) resolves to
    the blueprint theorem `Solution.two_le_multiplicity`; a copied def
    depending on a level theorem would dangle, so it must fail by name."""
    helper = _theorem_node("lem:mult", 1)
    helper.lean_names = ["Solution.two_le_multiplicity"]
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            helper,
            _theorem_node("lem:t", 2, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Solution": _SOLUTION_DECL,
        "Toy.B": _decl(
            keyword="def", name="B", full_name="Toy.B", namespace="Toy",
            signature="(S : Solution) : Nat",
            source_text="def B (S : Solution) : Nat :=\n"
            "  if S.two_le_multiplicity then 1 else 2",
        ),
        "Solution.two_le_multiplicity": _decl(
            name="two_le_multiplicity",
            full_name="Solution.two_le_multiplicity",
            namespace="Solution",
            proof="by trivial",
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    message = str(exc_info.value)
    assert "def:b" in message
    assert "Toy.B" in message
    assert "Solution.two_le_multiplicity" in message


def test_field_notation_untyped_receiver_is_named_error():
    """When the receiver type cannot be determined (e.g. a `fun`-bound `S`),
    a project declaration sharing the tail is a material but unresolvable
    dependency: named failure, not a guess and not a dangling reference."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:c", ["Toy.C"], 0),
            _theorem_node("lem:t", 1, uses=["def:c"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "A.y": _decl(keyword="def", name="y", full_name="A.y", namespace="A",
                     source_text="def y : Nat :=\n  1"),
        "B.y": _decl(keyword="def", name="y", full_name="B.y", namespace="B",
                     source_text="def y : Nat :=\n  2"),
        "Toy.C": _decl(
            keyword="def", name="C", full_name="Toy.C", namespace="Toy",
            signature=": Nat",
            source_text="def C : Nat :=\n  (fun S => S.y) 0",
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    message = str(exc_info.value)
    assert "S.y" in message
    assert "Toy.C" in message
    assert "A.y" in message
    assert "B.y" in message


def test_field_notation_project_name_under_external_namespace():
    """`n.succ` with `n : Nat` resolves a *project* `Nat.succ` even though
    `Nat` itself has no declaration object: the type-directed name is probed
    literally."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            _theorem_node("lem:t", 1, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Nat.succ": _decl(keyword="def", name="succ", full_name="Nat.succ",
                          namespace="Nat",
                          source_text="def succ (n : Nat) : Nat :=\n  n"),
        "Toy.B": _decl(
            keyword="def", name="B", full_name="Toy.B", namespace="Toy",
            signature="(n : Nat) : Nat",
            source_text="def B (n : Nat) : Nat :=\n  n.succ",
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    copied = [decl.full_name for decl, _ in game.definitions]
    assert copied == ["Nat.succ", "Toy.B"]


def test_field_notation_bare_tail_not_guessed_for_external_type():
    """With `n : Nat`, `n.succ` is `Nat.succ` — an unrelated `Toy.succ` in
    scope is not a fallback dependency."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            _theorem_node("lem:t", 1, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Toy.succ": _decl(keyword="def", name="succ", full_name="Toy.succ",
                          namespace="Toy",
                          source_text="def succ (n : Nat) : Nat :=\n  n"),
        "Toy.B": _decl(
            keyword="def", name="B", full_name="Toy.B", namespace="Toy",
            signature="(n : Nat) : Nat",
            source_text="def B (n : Nat) : Nat :=\n  n.succ",
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    copied = [decl.full_name for decl, _ in game.definitions]
    assert copied == ["Toy.B"]


def test_field_notation_quantifier_binder_types_receiver():
    """`∀ S : Solution, S.y` binds `S` with receiver type `Solution` even
    outside parenthesized binders, so `Solution.y` is copied first; a level
    theorem reached the same way is rejected by name."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:spec", ["Toy.spec"], 0),
            _theorem_node("lem:t", 1, uses=["def:spec"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Solution": _SOLUTION_DECL,
        "Solution.y": _decl(keyword="def", name="y", full_name="Solution.y",
                            namespace="Solution",
                            source_text="def y : Nat :=\n  1"),
        "Toy.spec": _decl(
            keyword="def", name="spec", full_name="Toy.spec", namespace="Toy",
            signature=": Prop",
            source_text="def spec : Prop :=\n  ∀ S : Solution, S.y = 1",
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    copied = [decl.full_name for decl, _ in game.definitions]
    assert copied == ["Solution", "Solution.y", "Toy.spec"]


def test_field_notation_quantifier_binder_blueprint_theorem_is_error():
    """`∃ S : Solution, S.two_le_multiplicity` resolves to the blueprint
    theorem just like a parenthesized binder would."""
    helper = _theorem_node("lem:mult", 1)
    helper.lean_names = ["Solution.two_le_multiplicity"]
    blueprint = Blueprint(
        nodes=[
            _def_node("def:spec", ["Toy.spec"], 0),
            helper,
            _theorem_node("lem:t", 2, uses=["def:spec"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Solution": _SOLUTION_DECL,
        "Toy.spec": _decl(
            keyword="def", name="spec", full_name="Toy.spec", namespace="Toy",
            signature=": Prop",
            source_text="def spec : Prop :=\n"
            "  ∃ S : Solution, S.two_le_multiplicity",
        ),
        "Solution.two_le_multiplicity": _decl(
            name="two_le_multiplicity",
            full_name="Solution.two_le_multiplicity",
            namespace="Solution",
            proof="by trivial",
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    message = str(exc_info.value)
    assert "def:spec" in message
    assert "Solution.two_le_multiplicity" in message


def test_field_notation_project_type_missing_target_is_named_error():
    """`S : Solution` makes `S.y` type-directed; when `Solution.y` does not
    exist but some other project `*.y` might be the intended target, reject
    rather than emit a reference the generated file cannot resolve."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:c", ["Toy.C"], 0),
            _theorem_node("lem:t", 1, uses=["def:c"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Solution": _SOLUTION_DECL,
        "Other.y": _decl(keyword="def", name="y", full_name="Other.y",
                         namespace="Other",
                         source_text="def y : Nat :=\n  2"),
        "Toy.C": _decl(
            keyword="def", name="C", full_name="Toy.C", namespace="Toy",
            signature="(S : Solution) : Nat",
            source_text="def C (S : Solution) : Nat :=\n  S.y + 1",
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    message = str(exc_info.value)
    assert "S.y" in message
    assert "Other.y" in message


def test_copied_decl_with_local_syntax_is_error():
    """A def whose source context defines project-local notation cannot be
    reproduced verbatim in self-contained Defs.lean: reject it by name. The
    diagnostic names the command kinds, never raw syntax (which could carry
    string literals)."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            _theorem_node("lem:t", 1, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Toy.B": _decl(
            keyword="def", name="B", full_name="Toy.B", namespace="Toy",
            module="Basic",
            source_text="def B : η :=\n  1",
            local_syntax=["notation"],
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    message = str(exc_info.value)
    assert "def:b" in message
    assert "Toy.B" in message
    assert "Basic" in message
    assert "notation" in message
    assert "η" not in message


def test_copied_dep_with_local_syntax_is_error():
    """The rejection also fires through a copied *dependency*'s context."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            _theorem_node("lem:t", 1, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Toy.B": _decl(keyword="def", name="B", full_name="Toy.B", namespace="Toy",
                       source_text="def B : Nat :=\n  Other.base + 1"),
        "Other.base": _decl(
            keyword="def", name="base", full_name="Other.base", namespace="Other",
            module="Other",
            source_text="def base : K :=\n  1",
            local_syntax=["notation"],
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    message = str(exc_info.value)
    assert "Other.base" in message
    assert "notation" in message


def test_copied_decl_with_project_open_is_error():
    """`open Ks` where `Ks` is a project namespace cannot be reproduced
    self-contained (only the copied subset would be opened): reject."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            _theorem_node("lem:t", 1, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Ks.k": _decl(keyword="def", name="k", full_name="Ks.k", namespace="Ks",
                      source_text="def k : Nat :=\n  1"),
        "Toy.B": _decl(
            keyword="def", name="B", full_name="Toy.B", namespace="Toy",
            opens=["open Ks"],
            source_text="def B : Nat :=\n  k + 1",
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    message = str(exc_info.value)
    assert "def:b" in message
    assert "Toy.B" in message
    assert "Ks" in message


def test_copied_decl_with_external_open_is_fine():
    """`open` of a namespace that isn't project-local stays supported."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            _theorem_node("lem:t", 1, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Toy.B": _decl(
            keyword="def", name="B", full_name="Toy.B", namespace="Toy",
            opens=["open scoped BigOperators"],
            source_text="def B : Nat :=\n  1",
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    copied = [decl.full_name for decl, _ in game.definitions]
    assert copied == ["Toy.B"]


def test_level_theorem_with_local_syntax_is_error():
    """A level's Statement/sample proof likewise cannot reproduce
    project-local notation; reject before writing the game."""
    blueprint = Blueprint(
        nodes=[_theorem_node("lem:t", 0)],
        chapters=["Ch"],
    )
    decls = {
        "t": _decl(
            name="t", full_name="t", proof="by exact trivial",
            local_syntax=["set_option"],
        ),
    }

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    message = str(exc_info.value)
    assert "lem:t" in message
    assert "t" in message
    assert "set_option" in message


def test_copy_dependency_cycle_is_error():
    """A dependency cycle (impossible in valid Lean, reachable through the
    text-level approximation) is reported, not emitted in arbitrary order."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:a", ["Toy.A"], 0),
            _theorem_node("lem:t", 1, uses=["def:a"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Toy.A": _decl(keyword="def", name="A", full_name="Toy.A", namespace="Toy",
                       source_text="def A : Nat :=\n  B"),
        "Toy.B": _decl(keyword="def", name="B", full_name="Toy.B", namespace="Toy",
                       source_text="def B : Nat :=\n  A"),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    message = str(exc_info.value)
    assert "def:a" in message
    assert "cycle" in message
    assert "Toy.A" in message and "Toy.B" in message


def test_shared_listed_decl_doc_goes_to_first_node_in_order():
    """A decl listed by two definition nodes is documented by the first one
    in topological order, even when copied earlier as a dependency."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:early", ["Toy.early"], 0),
            _def_node("def:shared1", ["Toy.shared"], 1),
            _def_node("def:shared2", ["Toy.shared"], 2),
            _theorem_node("lem:t", 3, uses=["def:early"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "Toy.early": _decl(keyword="def", name="early", full_name="Toy.early",
                           namespace="Toy",
                           source_text="def early : Nat :=\n  shared"),
        "Toy.shared": _decl(keyword="def", name="shared", full_name="Toy.shared",
                            namespace="Toy",
                            source_text="def shared : Nat :=\n  1"),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    by_name = {decl.full_name: node for decl, node in game.definitions}
    assert list(by_name) == ["Toy.shared", "Toy.early"]
    assert by_name["Toy.shared"].label == "def:shared1"


def test_theorem_docs_require_in_category_on_legacy_game_server():
    """v4.7.0 GameServer rejects `TheoremDoc t as "t"` without `in "cat"`."""
    from proofquest.game_model import Game
    from proofquest.generator import _render_theorem_docs

    def game(toolchain):
        return Game(
            title="T", intro_md="", languages="en", worlds=[],
            definitions=[], tactics=[], theorems=["le_max_left"],
            toolchain=toolchain,
        )

    legacy = _render_theorem_docs(game("leanprover/lean4:v4.7.0"))
    assert 'TheoremDoc le_max_left as "le_max_left" in "Theorems"' in legacy
    modern = _render_theorem_docs(game("leanprover/lean4:v4.31.0"))
    assert 'TheoremDoc le_max_left as "le_max_left"' in modern
    assert 'in "Theorems"' not in modern


def test_build_game_reuses_same_chapter_and_keeps_non_conflicting_worlds():
    blueprint = Blueprint(
        nodes=[
            _node("first", "A B", 0),
            _node("second", "A B", 1),
            _node("third", "Different", 2),
        ],
        chapters=["A B", "Different"],
    )
    decls = {
        label: _decl(name=label, full_name=label)
        for label in ("first", "second", "third")
    }

    game = build_game(blueprint, decls, toolchain="v4.19.0", title="Test")

    assert [(world.world_id, world.title) for world in game.worlds] == [
        ("AB", "A B"),
        ("Different", "Different"),
    ]
    assert [len(world.levels) for world in game.worlds] == [2, 1]
