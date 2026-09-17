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
