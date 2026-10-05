import pytest

from proofquest.game_model import (
    Blueprint,
    BlueprintNode,
    LeanContextCommand,
    LeanDecl,
    LeanNotation,
    Level,
)
from proofquest.generator import (
    GenerationError,
    _binder_names,
    _binder_types,
    _context_lines,
    _is_declared_theorem,
    _looks_like_theorem_name,
    _obtain_binder_types,
    _qualify_project_refs,
    _resolve_inventory_name,
    _resolve_project_decl,
    _source_refs,
    _statement_proof,
    _strip_accessor_suffix,
    _theorem_refs_in_proof,
    build_game,
    write_game,
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
        "first": _decl(name="first", full_name="first", proof="by trivial"),
        "second": _decl(name="second", full_name="second", proof="by trivial"),
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


def test_definition_depending_on_blueprint_theorem_is_staged():
    """A copied def referencing a blueprint theorem cannot live in the
    preamble (the theorem only exists once its `Statement` level file is
    imported): it is staged into a ``DefsAfterNNN`` module emitted after
    that level, and introduced to the inventory at the consuming level."""
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

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    assert [stage.index for stage in game.stages] == [0, 1]
    assert [d.full_name for d, _ in game.stages[0].definitions] == []
    assert [d.full_name for d, _ in game.stages[1].definitions] == ["Toy.B"]
    assert game.stages[1].level.file_stem == "L01_helper_lemma"
    level_t = game.worlds[0].levels[1]
    assert level_t.node.label == "lem:t"
    assert [d.full_name for d in level_t.new_definitions] == ["Toy.B"]


def test_definition_transitive_blueprint_theorem_dep_is_staged():
    """The staging works through an intermediate copied decl, with the
    intermediate declaration emitted before its dependent in the stage."""
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

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    assert [stage.index for stage in game.stages] == [0, 1]
    assert [d.full_name for d, _ in game.stages[0].definitions] == []
    assert [d.full_name for d, _ in game.stages[1].definitions] == [
        "Toy.mid",
        "Toy.B",
    ]


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


def test_field_notation_dep_on_blueprint_theorem_is_staged():
    """`S.two_le_multiplicity` (dot notation on `S : Solution`) resolves to
    the blueprint theorem `Solution.two_le_multiplicity`; the copied def is
    staged after that level while the receiver type stays in the preamble."""
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

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    assert [stage.index for stage in game.stages] == [0, 1]
    assert [d.full_name for d, _ in game.stages[0].definitions] == ["Solution"]
    assert [d.full_name for d, _ in game.stages[1].definitions] == ["Toy.B"]
    assert game.stages[1].level.file_stem == "L01_two_le_multiplicity"


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


def test_field_notation_quantifier_binder_blueprint_theorem_is_staged():
    """`∃ S : Solution, S.two_le_multiplicity` resolves to the blueprint
    theorem just like a parenthesized binder would: staged, not rejected."""
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

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    assert [stage.index for stage in game.stages] == [0, 1]
    assert [d.full_name for d, _ in game.stages[0].definitions] == ["Solution"]
    assert [d.full_name for d, _ in game.stages[1].definitions] == ["Toy.spec"]


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
    """A *selective* `open Ks (k)` of a project namespace cannot be
    reproduced self-contained (the generated namespace only holds the
    copied subset): reject. Plain `open Ks` is supported — see
    `test_plain_project_open_resolves_and_scaffolds`."""
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
            opens=["open Ks (k)"],
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


def test_plain_project_open_resolves_through_opened_namespace():
    """`open Ks` of a project namespace resolves `k` to `Ks.k`, and the
    opened namespace gets an empty scaffold in the rendered file."""
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

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    copied = [decl.full_name for decl, _ in game.definitions]
    assert copied == ["Ks.k", "Toy.B"]


def test_relative_project_open_resolves_through_enclosing_namespace():
    """`open Rat` inside `namespace IsCyclotomicExtension` opens
    `IsCyclotomicExtension.Rat` (relative) as well as root `Rat`."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            _theorem_node("lem:t", 1, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "IsCyclotomicExtension.Rat.lemma": _decl(
            keyword="def", name="lemma",
            full_name="IsCyclotomicExtension.Rat.lemma",
            namespace="IsCyclotomicExtension.Rat",
            source_text="def lemma : Nat :=\n  1",
        ),
        "Toy.B": _decl(
            keyword="def", name="B", full_name="Toy.B", namespace="Toy",
            opens=["open Rat"],
            context_namespace="IsCyclotomicExtension",
            source_text="def B : Nat :=\n  lemma + 1",
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    copied = [decl.full_name for decl, _ in game.definitions]
    assert copied == ["IsCyclotomicExtension.Rat.lemma", "Toy.B"]


def test_ambiguous_opened_namespaces_reject():
    """When two opened project namespaces both provide `k`, the reference
    is ambiguous: reject rather than pick one arbitrarily."""
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            _theorem_node("lem:t", 1, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "A.k": _decl(keyword="def", name="k", full_name="A.k", namespace="A",
                     source_text="def k : Nat :=\n  1"),
        "B.k": _decl(keyword="def", name="k", full_name="B.k", namespace="B",
                     source_text="def k : Nat :=\n  2"),
        "Toy.B": _decl(
            keyword="def", name="B", full_name="Toy.B", namespace="Toy",
            opens=["open A", "open B"],
            source_text="def B : Nat :=\n  k + 1",
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    with pytest.raises(GenerationError, match="ambiguous"):
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")


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


def _open_command(source_text, namespace=""):
    return LeanContextCommand(
        module="M",
        source_path="M.lean",
        line=0,
        end_line=0,
        namespace=namespace,
        scope=(),
        kind="open",
        source_text=source_text,
        exported=False,
        supported=True,
    )


def test_suffix_open_resolves_via_original_context_commands():
    """Lean's `open` has suffix semantics: after `open NumberField`, a later
    `open Units` also opens `NumberField.Units`. The canonical render form
    `open _root_.Units` loses that, so lookup must use the original context
    commands (which keep `source_text` and the command's own namespace)."""
    rank = _decl(
        keyword="def", name="rank", full_name="NumberField.Units.rank",
        namespace="NumberField.Units", source_text="def rank : Nat :=\n  1",
    )
    caller = _decl(
        keyword="def", name="mem",
        full_name="IsCyclotomicExtension.Rat.Three.mem",
        namespace="IsCyclotomicExtension.Rat.Three",
        opens=["open _root_.NumberField", "open _root_.Units"],
        context=(
            _open_command("open NumberField"),
            _open_command("open Units"),
        ),
    )
    decls = {rank.full_name: rank}
    assert _resolve_project_decl("rank", caller, decls) is rank


def test_suffix_open_single_command_expands_tokens_in_order():
    rank = _decl(
        keyword="def", name="rank", full_name="NumberField.Units.rank",
        namespace="NumberField.Units", source_text="def rank : Nat :=\n  1",
    )
    caller = _decl(
        keyword="def", name="mem",
        full_name="IsCyclotomicExtension.Rat.Three.mem",
        namespace="IsCyclotomicExtension.Rat.Three",
        opens=["open _root_.NumberField _root_.Units"],
        context=(_open_command("open NumberField Units"),),
    )
    decls = {rank.full_name: rank}
    assert _resolve_project_decl("rank", caller, decls) is rank


def test_open_command_namespace_differs_from_decl_namespace():
    """A command written in `namespace NumberField` opens `NumberField.Sub`
    even for a consumer declared deeper in the tree."""
    lemma = _decl(
        keyword="def", name="lemma", full_name="NumberField.Sub.lemma",
        namespace="NumberField.Sub", source_text="def lemma : Nat :=\n  1",
    )
    caller = _decl(
        keyword="def", name="mem",
        full_name="NumberField.Units.Deep.mem",
        namespace="NumberField.Units.Deep",
        opens=["open _root_.NumberField.Sub"],
        context=(_open_command("open Sub", namespace="NumberField"),),
    )
    decls = {lemma.full_name: lemma}
    assert _resolve_project_decl("lemma", caller, decls) is lemma


def test_scoped_open_command_does_not_resolve_plain_names():
    foo = _decl(
        keyword="def", name="foo", full_name="Sco.foo", namespace="Sco",
        source_text="def foo : Nat :=\n  1",
    )
    caller = _decl(
        name="c", full_name="c",
        opens=["open scoped Sco"],
        context=(_open_command("open scoped Sco"),),
    )
    assert _resolve_project_decl("foo", caller, {foo.full_name: foo}) is None


def test_ambiguous_opened_namespaces_via_commands_reject():
    decls = {
        "A.k": _decl(keyword="def", name="k", full_name="A.k", namespace="A",
                     source_text="def k : Nat :=\n  1"),
        "B.k": _decl(keyword="def", name="k", full_name="B.k", namespace="B",
                     source_text="def k : Nat :=\n  2"),
    }
    caller = _decl(
        name="c", full_name="c",
        opens=["open _root_.A", "open _root_.B"],
        context=(_open_command("open A"), _open_command("open B")),
    )
    with pytest.raises(GenerationError, match="ambiguous"):
        _resolve_project_decl("k", caller, decls)


def test_resolve_inventory_name_namespace_then_root_then_opened():
    caller = _decl(name="c", full_name="A.c", namespace="A")
    index = {"lem": {"A.lem", "B.lem", "lem"}}
    assert _resolve_inventory_name("lem", caller, {}, index) == "A.lem"
    root_caller = _decl(name="c", full_name="c", opens=["open B"])
    assert _resolve_inventory_name("lem", root_caller, {}, index) == "lem"


def test_resolve_inventory_name_ambiguous_opened_is_omitted():
    caller = _decl(name="c", full_name="c", opens=["open A", "open B"])
    index = {"lem": {"A.lem", "B.lem"}}
    assert _resolve_inventory_name("lem", caller, {}, index) is None


def test_resolve_inventory_name_expands_suffix_opens_via_commands():
    other = _decl(
        name="other", full_name="NumberField.Units.other",
        namespace="NumberField.Units",
    )
    caller = _decl(
        name="mem", full_name="IsCyclotomicExtension.Rat.Three.mem",
        namespace="IsCyclotomicExtension.Rat.Three",
        opens=["open _root_.NumberField", "open _root_.Units"],
        context=(
            _open_command("open NumberField"),
            _open_command("open Units"),
        ),
    )
    index = {"rank": {"NumberField.Units.rank"}}
    decls = {other.full_name: other}
    assert (
        _resolve_inventory_name("rank", caller, decls, index)
        == "NumberField.Units.rank"
    )


def test_dotted_decl_prefix_resolves_bare_refs():
    lemma = _decl(
        name="multiplicity_lambda_c_finite",
        full_name="Solution'.multiplicity_lambda_c_finite",
        namespace="", proof="by trivial",
    )
    caller = _decl(
        keyword="def", name="Solution'.multiplicity",
        full_name="Solution'.multiplicity", namespace="",
    )
    decls = {lemma.full_name: lemma}
    assert (
        _resolve_project_decl("multiplicity_lambda_c_finite", caller, decls)
        is lemma
    )


def test_decl_prefix_shadows_enclosing_namespace():
    inner = _decl(
        name="dep", full_name="Outer.Inner.dep", namespace="Outer.Inner"
    )
    outer = _decl(name="dep", full_name="Outer.dep", namespace="Outer")
    caller = _decl(
        name="Inner.uses", full_name="Outer.Inner.uses", namespace="Outer",
        context_namespace="Outer",
    )
    decls = {inner.full_name: inner, outer.full_name: outer}
    assert _resolve_project_decl("dep", caller, decls) is inner


def test_root_decl_prefix_then_enclosing_namespace():
    outer_dep = _decl(name="dep", full_name="Outer.dep", namespace="Outer")
    caller = _decl(
        name="uses", full_name="Inner.uses", namespace="Inner",
        context_namespace="Outer",
    )
    assert (
        _resolve_project_decl("dep", caller, {"Outer.dep": outer_dep})
        is outer_dep
    )


def test_root_qualified_refs_are_never_rewritten():
    decls = {
        "Outer.dep": _decl(name="dep", full_name="Outer.dep",
                           namespace="Outer"),
    }
    caller = _decl(name="uses", full_name="Inner.uses", namespace="Inner")
    out = _qualify_project_refs(
        "def uses := _root_.Outer.dep + dep", set(), caller, decls
    )
    assert "_root_.Outer.dep" in out
    assert "_root_._root_" not in out


def test_external_namespace_tokens_are_not_requalified():
    decls = {
        "Solution.multiplicity": _decl(
            keyword="def", name="multiplicity",
            full_name="Solution.multiplicity", namespace="Solution",
            source_text="def multiplicity : Nat :=\n  1",
        ),
    }
    caller = _decl(
        name="w", full_name="Solution.w", namespace="Solution",
        external_namespaces=frozenset({"multiplicity"}),
    )
    out = _qualify_project_refs(
        "(multiplicity.pow_multiplicity_dvd h).choose", {"h"}, caller, decls
    )
    assert "multiplicity.pow_multiplicity_dvd" in out
    assert "_root_.Solution.multiplicity" not in out


def test_project_extension_of_external_namespace_qualifies_exact():
    decls = {
        "Solution.multiplicity": _decl(
            keyword="def", name="multiplicity",
            full_name="Solution.multiplicity", namespace="Solution",
            source_text="def multiplicity : Nat :=\n  1",
        ),
        "Solution.multiplicity.locallemma": _decl(
            name="locallemma",
            full_name="Solution.multiplicity.locallemma",
            namespace="Solution.multiplicity",
        ),
    }
    caller = _decl(
        name="w", full_name="Solution.w", namespace="Solution",
        external_namespaces=frozenset({"multiplicity"}),
    )
    out = _qualify_project_refs(
        "multiplicity.locallemma", set(), caller, decls
    )
    assert out == "_root_.Solution.multiplicity.locallemma"


def test_free_constant_projection_still_qualified():
    decls = {
        "hζ": _decl(keyword="def", name="hζ", full_name="hζ",
                    source_text="def hζ : Nat :=\n  1"),
    }
    caller = _decl(name="w", full_name="w")
    assert (
        _qualify_project_refs("hζ.toInteger", set(), caller, decls)
        == "_root_.hζ.toInteger"
    )


def test_level_statement_for_root_named_decl_is_emitted_at_root(tmp_path):
    blueprint = Blueprint(
        nodes=[_theorem_node("lem:Inner.uses", 0)],
        chapters=["Ch"],
    )
    decls = {
        "Outer.dep": _decl(
            keyword="def", name="dep", full_name="Outer.dep",
            namespace="Outer", source_text="def dep : Nat :=\n  1",
        ),
        "Inner.uses": _decl(
            name="uses", full_name="Inner.uses", namespace="Inner",
            context_namespace="Outer",
            signature=": Nat",
            proof="by exact Outer.dep.succ_eq_add_one",
            source_text="theorem uses : Nat := by exact Outer.dep.succ_eq_add_one",
        ),
    }
    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    written = write_game(game, tmp_path)
    level_file = tmp_path / "Game/Levels/Ch/L01_uses.lean"
    assert level_file in written
    content = level_file.read_text()
    assert "Statement Inner.uses" in content
    assert "Statement _root_." not in content
    assert "namespace Outer\n\n/-- " not in content.split("Statement")[0]
    assert "open Outer" in content


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
        label: _decl(name=label, full_name=label, proof="by trivial")
        for label in ("first", "second", "third")
    }

    game = build_game(blueprint, decls, toolchain="v4.19.0", title="Test")

    assert [(world.world_id, world.title) for world in game.worlds] == [
        ("AB", "A B"),
        ("Different", "Different"),
    ]
    assert [len(world.levels) for world in game.worlds] == [2, 1]


def _staged_depexample():
    """helper level -> staged def depending on it -> consumer level."""
    helper = _theorem_node("lem:h", 0)
    helper.lean_names = ["helper"]
    blueprint = Blueprint(
        nodes=[
            helper,
            _def_node("def:dv", ["Toy.depval"], 1),
            _theorem_node("lem:t2", 2, uses=["def:dv"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "helper": _decl(name="helper", full_name="helper",
                        proof="by trivial",
                        source_text="theorem helper : True := by\n  trivial"),
        "Toy.depval": _decl(
            keyword="def", name="depval", full_name="Toy.depval",
            namespace="Toy", signature=": True",
            source_text="def depval : True :=\n  helper",
        ),
        "t2": _decl(name="t2", full_name="t2",
                    signature=": Toy.depval = Toy.depval",
                    proof="by rfl",
                    source_text="theorem t2 : Toy.depval = Toy.depval := by\n  rfl"),
    }
    return blueprint, decls


def test_target_signature_depending_aux_is_staged_before_consumer():
    """A theorem whose *signature* mentions a staged definition forces the
    derived ordering: the def's stage must precede the consumer level."""
    blueprint, decls = _staged_depexample()

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    assert [stage.index for stage in game.stages] == [0, 1]
    assert [d.full_name for d, _ in game.stages[1].definitions] == ["Toy.depval"]
    helper_level, t2_level = game.worlds[0].levels
    assert helper_level.node.label == "lem:h"
    assert t2_level.node.label == "lem:t2"
    assert [d.full_name for d in t2_level.new_definitions] == ["Toy.depval"]


def test_staged_write_game_emits_module_imported_by_next_level(tmp_path):
    """The emitted files wire the staged module after its prerequisite
    level: the level right after it imports it, the preamble stays clean
    of the staged declaration, and no theorem proof leaks anywhere."""
    blueprint, decls = _staged_depexample()
    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    written = write_game(game, tmp_path)
    names = {str(p.relative_to(tmp_path)) for p in written}

    assert "Game/Generated/DefsAfter001.lean" in names
    defs = (tmp_path / "Game/Generated/Defs.lean").read_text()
    assert "depval" not in defs
    assert "theorem" not in defs
    stage = (tmp_path / "Game/Generated/DefsAfter001.lean").read_text()
    assert "import Game.Levels.Ch.L01_helper" in stage
    assert "import GameServer.Commands" in stage
    assert "def depval : True :=\n  _root_.helper" in stage
    assert 'DefinitionDoc Toy.depval as "depval"' in stage
    level1 = (tmp_path / "Game/Levels/Ch/L01_helper.lean").read_text()
    assert "Statement helper" in level1
    assert "DefsAfter" not in level1
    level2 = (tmp_path / "Game/Levels/Ch/L02_t2.lean").read_text()
    assert "import Game.Generated.DefsAfter001" in level2
    assert (
        "Statement t2 : _root_.Toy.depval = _root_.Toy.depval" in level2
    )
    assert "NewDefinition Toy.depval" in level2
    for path in written:
        text = path.read_text()
        assert "axiom" not in text
        assert "sorry" not in text
        assert "theorem helper : True := by" not in text.replace(
            "Statement helper", ""
        )


def test_mixed_def_level_cycle_is_diagnosed_before_output(tmp_path):
    """def B references the level theorem `t2` while `t2`'s signature needs
    `B`: a genuine mixed cycle, reported with the full chain and origins —
    before any file is written and without suggesting a def conversion."""
    helper = _theorem_node("lem:t2", 0)
    helper.lean_names = ["t2"]
    blueprint = Blueprint(
        nodes=[helper, _def_node("def:b", ["Toy.B"], 1)],
        chapters=["Ch"],
    )
    decls = {
        "t2": _decl(
            name="t2", full_name="t2",
            signature=": Toy.B = Toy.B", proof="by rfl",
            source_text="theorem t2 : Toy.B = Toy.B := by\n  rfl",
            source_path="Basic.lean", line=6,
        ),
        "Toy.B": _decl(
            keyword="def", name="B", full_name="Toy.B", namespace="Toy",
            signature=": Nat",
            source_text="def B : Nat :=\n  if t2 then 1 else 2",
            source_path="Basic.lean", line=2,
        ),
    }

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    message = str(exc_info.value)
    assert "cycle" in message
    assert "Toy.B" in message
    assert "t2" in message
    assert "Basic.lean" in message
    assert "restate" not in message
    assert not any(tmp_path.iterdir())


def test_target_proof_self_reference_is_not_a_false_cycle():
    """A target whose proof text mentions itself (or a placeholder shaped
    like it) must not constrain its own level ordering."""
    node = _theorem_node("lem:t", 0)
    node.lean_names = ["t"]
    blueprint = Blueprint(nodes=[node], chapters=["Ch"])
    decls = {
        "t": _decl(
            name="t", full_name="t",
            signature=": True", proof="by exact t",
            source_text="theorem t : True := by\n  exact t",
        ),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    assert len(game.worlds[0].levels) == 1


def test_staged_def_after_last_level_stays_reachable(tmp_path):
    """A staged definition consumed by no level still has a reachable
    module: when no later level exists to import the stage, the game root
    imports it so nothing dangles silently."""
    helper = _theorem_node("lem:h", 0)
    helper.lean_names = ["helper"]
    blueprint = Blueprint(
        nodes=[helper, _def_node("def:b", ["Toy.B"], 1)],
        chapters=["Ch"],
    )
    decls = {
        "helper": _decl(name="helper", full_name="helper",
                        proof="by trivial",
                        source_text="theorem helper : True := by\n  trivial"),
        "Toy.B": _decl(keyword="def", name="B", full_name="Toy.B",
                       namespace="Toy",
                       source_text="def B : Nat :=\n  if helper then 1 else 2"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    assert [stage.index for stage in game.stages] == [0, 1]
    assert game.stages[1].level is game.worlds[0].levels[0]
    written = write_game(game, tmp_path)
    names = {str(p.relative_to(tmp_path)) for p in written}
    assert "Game/Generated/DefsAfter001.lean" in names
    root = (tmp_path / "Game.lean").read_text()
    assert "import Game.Generated.DefsAfter001" in root


def test_staged_definition_across_worlds(tmp_path):
    """The dependent def's consumer lives in a different world than the
    prerequisite level: ordering still holds because levels chain across
    worlds, and the consuming level imports the stage directly."""
    helper = _theorem_node("lem:h", 0)
    helper.lean_names = ["helper"]
    helper.chapter = "First"
    consumer = _theorem_node("lem:t2", 2, uses=["def:b"])
    consumer.chapter = "Second"
    blueprint = Blueprint(
        nodes=[helper, _def_node("def:b", ["Toy.B"], 1), consumer],
        chapters=["First", "Second"],
    )
    decls = {
        "helper": _decl(name="helper", full_name="helper",
                        proof="by trivial",
                        source_text="theorem helper : True := by\n  trivial"),
        "Toy.B": _decl(keyword="def", name="B", full_name="Toy.B",
                       namespace="Toy",
                       source_text="def B : Nat :=\n  if helper then 1 else 2"),
        "t2": _decl(name="t2", full_name="t2",
                    signature=": True", proof="by trivial",
                    source_text="theorem t2 : True := by\n  trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    assert [w.world_id for w in game.worlds] == ["First", "Second"]
    write_game(game, tmp_path)
    stage = (tmp_path / "Game/Generated/DefsAfter001.lean").read_text()
    assert "import Game.Levels.First.L01_helper" in stage
    level2 = (
        tmp_path / "Game/Levels/Second/L01_t2.lean"
    ).read_text()
    assert "import Game.Levels.First.L01_helper" in level2
    assert "import Game.Generated.DefsAfter001" in level2
    assert "NewDefinition Toy.B" in level2


def test_staged_generation_is_deterministic(tmp_path):
    blueprint, decls = _staged_depexample()
    out1, out2 = tmp_path / "g1", tmp_path / "g2"
    game1 = build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    write_game(game1, out1)
    game2 = build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    write_game(game2, out2)
    files1 = {str(p.relative_to(out1)) for p in out1.rglob("*") if p.is_file()}
    files2 = {str(p.relative_to(out2)) for p in out2.rglob("*") if p.is_file()}
    assert files1 == files2
    for rel in files1:
        assert (out1 / rel).read_bytes() == (out2 / rel).read_bytes()


def _world_node(label, chapter, order, uses=()):
    node = _theorem_node(label, order, uses=uses)
    node.chapter = chapter
    return node


def _collision_game(marker_source, proofs):
    a1 = _world_node("lem:a1", "First", 1)
    a2 = _world_node("lem:a2", "First", 2)
    b = _world_node("lem:b", "Second", 3, uses=["def:m"])
    blueprint = Blueprint(
        nodes=[a1, a2, _def_node("def:m", ["marker"], 0), b],
        chapters=["First", "Second"],
    )
    decls = {
        "a1": _decl(name="a1", full_name="a1", signature=": True",
                    proof=proofs[0],
                    source_text="theorem a1 : True := by\n  trivial"),
        "marker": _decl(keyword="def", name="marker", full_name="marker",
                        source_text=marker_source),
        "a2": _decl(name="a2", full_name="a2", signature=": True",
                    proof=proofs[1],
                    source_text="theorem a2 : True := by\n  trivial"),
        "b": _decl(name="b", full_name="b", signature=": True",
                   proof=proofs[2],
                   source_text="theorem b : True := by\n  trivial"),
    }
    return build_game(blueprint, decls, toolchain="v4.31.0", title="T")


def test_root_def_intro_moves_to_earlier_bound_name_collision():
    """A root-level copied def whose name is locally bound in an earlier
    level's proof is introduced there instead of at its nominal consumer:
    GameServer's inventory scan resolves bare identifiers against the
    environment regardless of local binders, so the earliest colliding
    level is the honest introduction site."""
    game = _collision_game(
        "def marker : Nat := 0",
        [
            "by\n  have marker := rfl\n  trivial",
            "by trivial",
            "by trivial",
        ],
    )

    first, second = game.worlds
    assert first.world_id == "First" and second.world_id == "Second"
    assert [d.full_name for d in first.levels[0].new_definitions] == ["marker"]
    assert all(
        d.full_name != "marker"
        for level in second.levels
        for d in level.new_definitions
    )
    assert ("Second", "First") not in game.world_dependencies
    assert ("First", "Second") in game.world_dependencies


def test_root_def_shadow_level_must_follow_its_stage():
    """Only a collision level *after* the def's stage qualifies: the
    shadowing level that coincides with the stage is skipped, and the
    tile lands on the next eligible level while the stage is unchanged."""
    game = _collision_game(
        "def marker : Nat :=\n  if a1 then 1 else 0",
        [
            "by\n  have marker := rfl\n  trivial",
            "by\n  have marker := rfl\n  trivial",
            "by trivial",
        ],
    )

    first, second = game.worlds
    stage = next(
        s for s in game.stages
        if any(d.full_name == "marker" for d, _ in s.definitions)
    )
    assert stage.index == 1
    assert [d.full_name for d in first.levels[0].new_definitions] == []
    assert [d.full_name for d in first.levels[1].new_definitions] == ["marker"]
    assert all(
        d.full_name != "marker"
        for level in second.levels
        for d in level.new_definitions
    )


def test_root_def_intro_unchanged_without_earlier_collision():
    """No eligible earlier bound-name collision leaves the nominal
    introduction level untouched."""
    game = _collision_game(
        "def marker : Nat := 0",
        [
            "by trivial",
            "by trivial",
            "by trivial",
        ],
    )

    first, second = game.worlds
    assert all(
        d.full_name != "marker"
        for level in first.levels
        for d in level.new_definitions
    )
    assert [d.full_name for d in second.levels[0].new_definitions] == ["marker"]


def test_independent_interleaved_worlds_regroup_safely(tmp_path):
    """Worlds may reorder when a theorem prerequisite crosses chapter
    boundaries: A:a1, B:b1, A:a2 with a2 needing b1 emits B before A and
    records the world dependency instead of interleaving positions."""
    a1 = _world_node("lem:a1", "A", 0)
    a1.lean_names = ["Toy.a1"]
    b1 = _world_node("lem:b1", "B", 1)
    b1.lean_names = ["Toy.b1"]
    dv = _def_node("def:dv", ["Toy.dv"], 2)
    dv.chapter = "A"
    a2 = _world_node("lem:a2", "A", 3, uses=["def:dv"])
    a2.lean_names = ["Toy.a2"]
    blueprint = Blueprint(nodes=[a1, b1, dv, a2], chapters=["A", "B"])
    decls = {
        "Toy.a1": _decl(
            name="a1", full_name="Toy.a1", namespace="Toy",
            signature=": True", proof="by trivial",
            source_text="theorem a1 : True := by\n  trivial",
        ),
        "Toy.b1": _decl(
            name="b1", full_name="Toy.b1", namespace="Toy",
            signature=": True", proof="by trivial",
            source_text="theorem b1 : True := by\n  trivial",
        ),
        "Toy.dv": _decl(
            keyword="def", name="dv", full_name="Toy.dv", namespace="Toy",
            signature=": True",
            source_text="def dv : True :=\n  b1",
        ),
        "Toy.a2": _decl(
            name="a2", full_name="Toy.a2", namespace="Toy",
            signature=": dv = dv", proof="by rfl",
            source_text="theorem a2 : dv = dv := by\n  rfl",
        ),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    assert [w.world_id for w in game.worlds] == ["B", "A"]
    assert game.world_dependencies == [("B", "A")]
    flat = [level.node.label for w in game.worlds for level in w.levels]
    assert flat == ["lem:b1", "lem:a1", "lem:a2"]

    write_game(game, tmp_path)
    root = (tmp_path / "Game.lean").read_text()
    assert "Dependency B → A" in root
    stage = (tmp_path / "Game/Generated/DefsAfter001.lean").read_text()
    assert "import Game.Levels.B.L01_b1" in stage
    assert "def dv : True :=\n  _root_.Toy.b1" in stage
    level_a1 = (tmp_path / "Game/Levels/A/L01_a1.lean").read_text()
    assert "import Game.Levels.B.L01_b1" in level_a1
    assert "import Game.Generated.DefsAfter001" in level_a1
    level_a2 = (tmp_path / "Game/Levels/A/L02_a2.lean").read_text()
    assert "Statement a2" in level_a2
    assert "NewDefinition Toy.dv" in level_a2


def test_cyclic_world_layout_is_diagnosed_before_output(tmp_path):
    """A:a1 -> B:b1 -> A:a2 through a dependent definition is impossible
    for a grouped layout: the world DAG is cyclic, so generation fails
    with the witnessing chain instead of emitting inconsistent output."""
    a1 = _world_node("lem:a1", "A", 0)
    a1.lean_names = ["Toy.a1"]
    b1 = _world_node("lem:b1", "B", 1)
    b1.lean_names = ["Toy.b1"]
    dv = _def_node("def:dv", ["Toy.dv"], 2)
    dv.chapter = "A"
    a2 = _world_node("lem:a2", "A", 3, uses=["def:dv"])
    a2.lean_names = ["Toy.a2"]
    blueprint = Blueprint(nodes=[a1, b1, dv, a2], chapters=["A", "B"])
    decls = {
        "Toy.a1": _decl(
            name="a1", full_name="Toy.a1", namespace="Toy",
            signature=": True", proof="by trivial",
            source_text="theorem a1 : True := by\n  trivial",
            source_path="Basic.lean", line=1,
        ),
        "Toy.b1": _decl(
            name="b1", full_name="Toy.b1", namespace="Toy",
            signature=": True", proof="by exact a1",
            source_text="theorem b1 : True := by\n  exact a1",
            source_path="Basic.lean", line=4,
        ),
        "Toy.dv": _decl(
            keyword="def", name="dv", full_name="Toy.dv", namespace="Toy",
            signature=": True",
            source_text="def dv : True :=\n  b1",
            source_path="Basic.lean", line=7,
        ),
        "Toy.a2": _decl(
            name="a2", full_name="Toy.a2", namespace="Toy",
            signature=": dv = dv", proof="by rfl",
            source_text="theorem a2 : dv = dv := by\n  rfl",
            source_path="Basic.lean", line=10,
        ),
    }

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    message = str(exc_info.value)
    assert "grouped world" in message
    assert "A -> B -> A" in message
    assert "Toy.b1" in message and "Basic.lean" in message
    assert "def:dv" in message or "lem:a2" in message
    assert not any(tmp_path.iterdir())


def test_cyclic_world_layout_uses_canonical_earliest_witness(tmp_path):
    """When several same-world ancestors could witness a cross-world edge,
    the diagnostic chain names the earliest blueprint prerequisite."""
    a1 = _world_node("lem:a1", "A", 0)
    a1.lean_names = ["Toy.a1"]
    b1 = _world_node("lem:b1", "B", 1)
    b1.lean_names = ["Toy.b1"]
    b2 = _world_node("lem:b2", "B", 2)
    b2.lean_names = ["Toy.b2"]
    dv = _def_node("def:dv", ["Toy.dv"], 3)
    dv.chapter = "A"
    a2 = _world_node("lem:a2", "A", 4, uses=["def:dv"])
    a2.lean_names = ["Toy.a2"]
    blueprint = Blueprint(nodes=[a1, b1, b2, dv, a2], chapters=["A", "B"])
    decls = {
        "Toy.a1": _decl(
            name="a1", full_name="Toy.a1", namespace="Toy",
            signature=": True", proof="by trivial",
            source_text="theorem a1 : True := by\n  trivial",
            source_path="Basic.lean", line=1,
        ),
        "Toy.b1": _decl(
            name="b1", full_name="Toy.b1", namespace="Toy",
            signature=": True", proof="by exact a1",
            source_text="theorem b1 : True := by\n  exact a1",
            source_path="Basic.lean", line=4,
        ),
        "Toy.b2": _decl(
            name="b2", full_name="Toy.b2", namespace="Toy",
            signature=": True", proof="by exact a1",
            source_text="theorem b2 : True := by\n  exact a1",
            source_path="Basic.lean", line=6,
        ),
        "Toy.dv": _decl(
            keyword="def", name="dv", full_name="Toy.dv", namespace="Toy",
            signature=": True",
            source_text="def dv : True :=\n  if b1 then b2 else b2",
            source_path="Basic.lean", line=8,
        ),
        "Toy.a2": _decl(
            name="a2", full_name="Toy.a2", namespace="Toy",
            signature=": dv = dv", proof="by rfl",
            source_text="theorem a2 : dv = dv := by\n  rfl",
            source_path="Basic.lean", line=11,
        ),
    }

    with pytest.raises(GenerationError) as exc_info:
        build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    message = str(exc_info.value)
    assert "A -> B -> A" in message
    assert "[lem:b1] -> Toy.a2" in message
    assert "[lem:b2] -> Toy.a2" not in message


def test_uses_definition_reorders_consumer_after_its_prerequisite(tmp_path):
    """T \\uses a definition whose own closure needs theorem U: U must be
    emitted before T even though T's source never mentions it, and the
    definition is introduced at T's level."""
    consumer = _world_node("lem:t", "Ch", 0, uses=["def:dv"])
    consumer.lean_names = ["Toy.t"]
    dv = _def_node("def:dv", ["Toy.dv"], 1)
    u = _world_node("lem:u", "Ch", 2)
    u.lean_names = ["Toy.u"]
    blueprint = Blueprint(nodes=[consumer, dv, u], chapters=["Ch"])
    decls = {
        "Toy.t": _decl(
            name="t", full_name="Toy.t", namespace="Toy",
            signature=": True", proof="by trivial",
            source_text="theorem t : True := by\n  trivial",
        ),
        "Toy.dv": _decl(
            keyword="def", name="dv", full_name="Toy.dv", namespace="Toy",
            signature=": True",
            source_text="def dv : True :=\n  u",
        ),
        "Toy.u": _decl(
            name="u", full_name="Toy.u", namespace="Toy",
            signature=": True", proof="by trivial",
            source_text="theorem u : True := by\n  trivial",
        ),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    levels = game.worlds[0].levels
    assert [level.node.label for level in levels] == ["lem:u", "lem:t"]
    assert [stage.index for stage in game.stages] == [0, 1]
    assert [d.full_name for d, _ in game.stages[1].definitions] == ["Toy.dv"]
    assert [d.full_name for d in levels[1].new_definitions] == ["Toy.dv"]
    write_game(game, tmp_path)
    consumer_level = (tmp_path / "Game/Levels/Ch/L02_t.lean").read_text()
    assert "import Game.Generated.DefsAfter001" in consumer_level


def test_uses_chain_through_definitions_propagates(tmp_path):
    """T uses def D1, D1 uses def D2, and D2's source needs theorem U:
    the projected graph still yields U -> T and stages both defs."""
    u = _world_node("lem:u", "Ch", 0)
    u.lean_names = ["Toy.u"]
    d2 = _def_node("def:d2", ["Toy.d2"], 1)
    d1 = _def_node("def:d1", ["Toy.d1"], 2, uses=["def:d2"])
    t = _world_node("lem:t", "Ch", 3, uses=["def:d1"])
    t.lean_names = ["Toy.t"]
    blueprint = Blueprint(nodes=[u, d2, d1, t], chapters=["Ch"])
    decls = {
        "Toy.u": _decl(
            name="u", full_name="Toy.u", namespace="Toy",
            signature=": True", proof="by trivial",
            source_text="theorem u : True := by\n  trivial",
        ),
        "Toy.d2": _decl(
            keyword="def", name="d2", full_name="Toy.d2", namespace="Toy",
            signature=": True",
            source_text="def d2 : True :=\n  u",
        ),
        "Toy.d1": _decl(
            keyword="def", name="d1", full_name="Toy.d1", namespace="Toy",
            signature=": True",
            source_text="def d1 : True :=\n  d2",
        ),
        "Toy.t": _decl(
            name="t", full_name="Toy.t", namespace="Toy",
            signature=": d1 = d1", proof="by rfl",
            source_text="theorem t : d1 = d1 := by\n  rfl",
        ),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    assert [level.node.label for level in game.worlds[0].levels] == [
        "lem:u",
        "lem:t",
    ]
    staged = {
        d.full_name for stage in game.stages[1:] for d, _ in stage.definitions
    }
    assert staged == {"Toy.d1", "Toy.d2"}
    write_game(game, tmp_path)
    stage = (tmp_path / "Game/Generated/DefsAfter001.lean").read_text()
    assert stage.index("def d2") < stage.index("def d1")


def test_unique_target_statement_across_generated_files(tmp_path):
    """Each target appears as exactly one `Statement` in exactly one level
    file, and no generated module contains the target proof text or a
    `theorem`/`axiom`/`sorry` substitute."""
    blueprint, decls = _staged_depexample()
    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    write_game(game, tmp_path)

    lean_files = [p for p in tmp_path.rglob("*.lean")]
    joined = {p: p.read_text() for p in lean_files}
    for name in ("helper", "t2"):
        statements = sum(text.count(f"Statement {name}") for text in joined.values())
        assert statements == 1, name
        theorems = sum(
            text.count(f"theorem {name}") for text in joined.values()
        )
        assert theorems == 0, name
    defs_sources = joined[tmp_path / "Game/Generated/Defs.lean"]
    stage_sources = joined[tmp_path / "Game/Generated/DefsAfter001.lean"]
    assert ":= by\n  trivial" not in defs_sources + stage_sources
    assert joined[tmp_path / "Game/Generated/DefsAfter001.lean"].count(
        "def depval"
    ) == 1
    for text in joined.values():
        assert "axiom " not in text
        assert "sorry" not in text


def _level(decl: LeanDecl, hint_md: str | None = None) -> Level:
    node = _theorem_node("lem:t", 0)
    node.lean_names = [decl.full_name]
    return Level(
        index=1,
        world_id="W",
        file_stem="L01_t",
        title="t",
        intro_md="",
        hint_md=hint_md,
        decl=decl,
        node=node,
    )


def test_statement_proof_replays_term_proof():
    decl = _decl(
        name="t", full_name="t",
        signature="(a b : Nat) : a + b = b + a",
        proof="add_comm a b",
    )
    assert _statement_proof(_level(decl), {}) == "by\n  exact add_comm a b"


def test_statement_proof_replays_bound_receiver_term():
    decl = _decl(
        name="t", full_name="t",
        signature="(hζ : IsPrimitiveRoot ζ 3) : Prime λ",
        proof="hζ.lambda_prime",
    )
    out = _statement_proof(_level(decl), {})
    assert out == "by\n  exact hζ.lambda_prime"
    assert "sorry" not in out


def test_statement_proof_replays_multiline_calc_term():
    proof = "calc\n    a = b := h1\n    _ = c := h2"
    decl = _decl(name="t", full_name="t", proof=proof)
    out = _statement_proof(_level(decl), {})
    assert out == (
        "by\n  exact calc\n        a = b := h1\n        _ = c := h2"
    )


def test_statement_proof_wraps_term_containing_by():
    decl = _decl(
        name="t", full_name="t", proof="foo (by simp) (by omega)"
    )
    out = _statement_proof(_level(decl), {})
    assert out == "by\n  exact foo (by simp) (by omega)"


def test_statement_proof_missing_proof_is_error():
    decl = _decl(name="t", full_name="t", proof=None)
    with pytest.raises(GenerationError, match="no proof"):
        _statement_proof(_level(decl), {})


def test_statement_proof_col0_comment_keeps_tactic_indent():
    decl = _decl(
        name="t", full_name="t",
        signature=": 0 = 0",
        proof="by\n  apply foo\n  exact bar\n-- trailing comment",
    )
    out = _statement_proof(_level(decl), {})
    assert out == "by\n  apply foo\n  exact bar\n  -- trailing comment"


def test_statement_proof_block_comment_keeps_tactic_indent():
    decl = _decl(
        name="t", full_name="t",
        signature=": 0 = 0",
        proof="by\n  apply foo\n/- multi\nline -/\n  exact bar",
    )
    out = _statement_proof(_level(decl), {})
    assert out == "by\n  apply foo\n  /- multi\n  line -/\n  exact bar"


def test_term_proof_inventory_uses_normalized_exact():
    """A term proof contributes its references to `new_theorems`/`new_tactics`
    through the same `exact` normalization used for rendering."""
    helper = _theorem_node("lem:helper_lemma", 0)
    blueprint = Blueprint(
        nodes=[helper, _theorem_node("lem:t", 1)],
        chapters=["Ch"],
    )
    decls = {
        "helper_lemma": _decl(
            name="helper_lemma", full_name="helper_lemma",
            signature=": 0 = 0", proof="by rfl",
        ),
        "t": _decl(
            name="t", full_name="t",
            signature="(a : Nat) : a = a",
            proof="helper_lemma.trans le_max_left",
        ),
    }
    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    level_t = game.worlds[0].levels[1]
    assert "le_max_left" in level_t.new_theorems
    assert "helper_lemma" not in level_t.new_theorems


def test_level_inventory_skips_method_projection_tokens():
    blueprint = Blueprint(
        nodes=[_theorem_node("lem:t", 0)], chapters=["Ch"],
    )
    decls = {
        "t": _decl(
            name="t", full_name="t",
            signature=": 0 = 0",
            proof="by\n  exact Int.prime_three.dvd_of_dvd_pow le_max_left",
        ),
    }
    index = {
        "dvd_of_dvd_pow": {"Prime.dvd_of_dvd_pow"},
        "prime_three": {"Int.prime_three"},
        "le_max_left": {"le_max_left"},
    }
    game = build_game(
        blueprint, decls, toolchain="v4.31.0", title="T",
        theorem_index=index,
    )
    level = game.worlds[0].levels[0]
    assert "Int.prime_three.dvd_of_dvd_pow" not in level.new_theorems
    assert "le_max_left" in level.new_theorems


def test_context_replay_registers_instance_before_attribute_disable():
    inst = _decl(
        keyword="instance", name="instX", full_name="instX",
        signature=": C Nat", proof="⟨0⟩",
        source_text="noncomputable\ninstance instX : C Nat := ⟨0⟩",
    )
    decl = _decl(
        name="t", full_name="t", proof="by trivial",
        instances=[inst],
        context=(
            LeanContextCommand(
                module="M", source_path="M.lean", line=0, end_line=0,
                namespace="", scope=(), kind="instance",
                source_text="noncomputable\ninstance instX : C Nat := ⟨0⟩",
                exported=True, supported=True, targets=("instX",),
            ),
            LeanContextCommand(
                module="M", source_path="M.lean", line=1, end_line=1,
                namespace="", scope=(), kind="attribute",
                source_text="attribute [-instance] instX",
                exported=True, supported=True,
                targets=("_root_.instX",), instance_action="disable",
            ),
            LeanContextCommand(
                module="M", source_path="M.lean", line=2, end_line=2,
                namespace="", scope=(), kind="attribute",
                source_text="attribute [instance 80] instX",
                exported=True, supported=True,
                targets=("_root_.instX",), instance_action="enable",
                priority=80,
            ),
        ),
    )
    assert _context_lines(decl, {}) == ([], [
        "attribute [local instance] _root_.instX",
        "attribute [-instance] _root_.instX",
        "attribute [local instance 80] _root_.instX",
    ])


def test_context_replay_emits_expression_notation_verbatim():
    decl = _decl(
        name="t", full_name="t", proof="by trivial",
        notations=[
            LeanNotation(
                module="M", line=1, namespace="Cyclo",
                pattern='"K"', target="", arguments=(),
                expression="CyclotomicField 3 ℚ",
            ),
        ],
        context=(
            LeanContextCommand(
                module="M", source_path="M.lean", line=1, end_line=1,
                namespace="Cyclo", scope=(), kind="notation3",
                source_text='local notation3 "K" => CyclotomicField 3 ℚ',
                exported=False, supported=True,
            ),
        ),
    )
    assert _context_lines(decl, {}) == ([], [
        'local notation "K" => CyclotomicField 3 ℚ'
    ])


def test_context_dependency_on_level_theorem_is_staged_after_it():
    """A context command's dependency (here an attribute target) that is a
    blueprint theorem must be staged *after* that level, never copied early
    into the preamble."""
    helper = _theorem_node("lem:helper_lemma", 1)
    blueprint = Blueprint(
        nodes=[
            _def_node("def:b", ["Toy.B"], 0),
            helper,
            _theorem_node("lem:t", 2, uses=["def:b"]),
        ],
        chapters=["Ch"],
    )
    decls = {
        "helper_lemma": _decl(
            name="helper_lemma", full_name="helper_lemma",
            proof="by trivial",
        ),
        "Toy.B": _decl(
            keyword="def", name="B", full_name="Toy.B", namespace="Toy",
            source_text="def B : Nat :=\n  1",
            context=(
                LeanContextCommand(
                    module="M", source_path="M.lean", line=0, end_line=0,
                    namespace="", scope=(), kind="attribute",
                    source_text="attribute [instance] helper_lemma",
                    exported=True, supported=True,
                    targets=("_root_.helper_lemma",), instance_action="enable",
                ),
            ),
        ),
        "t": _decl(name="t", full_name="t", proof="by exact trivial"),
    }

    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")

    assert [stage.index for stage in game.stages] == [0, 1]
    assert [d.full_name for d, _ in game.stages[0].definitions] == []
    assert [d.full_name for d, _ in game.stages[1].definitions] == ["Toy.B"]
    assert game.stages[1].level.file_stem == "L01_helper_lemma"


def test_context_replay_repeats_identical_events_verbatim():
    """Every supported context event is replayed in order: a disable between
    two identical enables must not dedup the second enable, and repeated
    variable explicitness toggles are all kept."""
    decl = _decl(
        name="t", full_name="t", proof="by trivial",
        context=(
            LeanContextCommand(
                module="M", source_path="M.lean", line=0, end_line=0,
                namespace="", scope=(), kind="attribute",
                source_text="attribute [instance] instX",
                exported=True, supported=True,
                targets=("_root_.instX",), instance_action="enable",
            ),
            LeanContextCommand(
                module="M", source_path="M.lean", line=1, end_line=1,
                namespace="", scope=(), kind="attribute",
                source_text="attribute [-instance] instX",
                exported=True, supported=True,
                targets=("_root_.instX",), instance_action="disable",
            ),
            LeanContextCommand(
                module="M", source_path="M.lean", line=2, end_line=2,
                namespace="", scope=(), kind="attribute",
                source_text="attribute [instance] instX",
                exported=True, supported=True,
                targets=("_root_.instX",), instance_action="enable",
            ),
            LeanContextCommand(
                module="M", source_path="M.lean", line=3, end_line=3,
                namespace="", scope=(), kind="variable",
                source_text="variable (K : Type*)",
                exported=False, supported=True,
            ),
            LeanContextCommand(
                module="M", source_path="M.lean", line=4, end_line=4,
                namespace="", scope=(), kind="variable",
                source_text="variable {K : Type*}",
                exported=False, supported=True,
            ),
            LeanContextCommand(
                module="M", source_path="M.lean", line=5, end_line=5,
                namespace="", scope=(), kind="variable",
                source_text="variable (K : Type*)",
                exported=False, supported=True,
            ),
        ),
    )
    assert _context_lines(decl, {}) == ([], [
        "attribute [local instance] _root_.instX",
        "attribute [-instance] _root_.instX",
        "attribute [local instance] _root_.instX",
        "variable (K : Type*)",
        "variable {K : Type*}",
        "variable (K : Type*)",
    ])


def test_context_replay_registers_instance_at_command_position():
    """A `noncomputable` modifier line before `instance` must not break the
    link between the instance command and its declaration: registration is
    emitted at the command's position, before the later disable."""
    inst = _decl(
        keyword="instance", name="instX", full_name="instX",
        signature=": C Nat", proof="{ tag := 0 }",
        source_text="noncomputable\ninstance instX : C Nat where\n  tag := 0",
        modifiers=("noncomputable",), line=0,
    )
    decl = _decl(
        name="t", full_name="t", proof="by trivial",
        instances=[inst],
        context=(
            LeanContextCommand(
                module="M", source_path="M.lean", line=0, end_line=2,
                namespace="", scope=(), kind="instance",
                source_text="noncomputable\ninstance instX : C Nat where\n  tag := 0",
                exported=True, supported=True, targets=("instX",),
            ),
            LeanContextCommand(
                module="M", source_path="M.lean", line=3, end_line=3,
                namespace="", scope=(), kind="attribute",
                source_text="attribute [-instance] instX",
                exported=True, supported=True,
                targets=("_root_.instX",), instance_action="disable",
            ),
        ),
    )
    assert _context_lines(decl, {}) == ([], [
        "attribute [local instance] _root_.instX",
        "attribute [-instance] _root_.instX",
    ])


def test_obtain_pattern_binder_typed_by_helper_signature():
    """`obtain ⟨S, -⟩ := exists_Solution_of_Solution' S'` types `S` from the
    existential clause of the (prime-named) helper lemma — and a chained
    `S.exists_minimal` is resolved through that type."""
    decls = {
        "Solution'": _decl(
            keyword="def", name="Solution'", full_name="Solution'"
        ),
        "exists_Solution_of_Solution'": _decl(
            name="exists_Solution_of_Solution'",
            full_name="exists_Solution_of_Solution'",
            signature="(S' : Solution') (hS' : 0 < S'.multiplicity) : "
            "∃ (S₁ : Solution'), S₁.multiplicity = S'.multiplicity",
        ),
        "Solution'.exists_minimal": _decl(
            name="exists_minimal", full_name="Solution'.exists_minimal",
            namespace="Solution'",
            signature="(S : Solution') : ∃ (Smin : Solution'), True",
        ),
    }
    decl = _decl(name="t", full_name="t")
    text = (
        "obtain ⟨S, -⟩ := exists_Solution_of_Solution' S'\n"
        "obtain ⟨Smin, hSmin⟩ := S.exists_minimal"
    )
    types = _obtain_binder_types(text, decl, decls, _binder_types(text))
    assert types["S"] == "Solution'"
    assert types["Smin"] == "Solution'"
    assert "hSmin" not in types


def test_obtain_nested_existential_does_not_invent_types():
    """`∃ (a : A), P a ∧ ∃ (b : B), Q b` has one direct witness: a later
    pattern leaf must not pick up the nested `B`."""
    decls = {
        "A": _decl(keyword="def", name="A", full_name="A"),
        "B": _decl(keyword="def", name="B", full_name="B"),
        "nested_exists": _decl(
            name="nested_exists", full_name="nested_exists",
            signature=": ∃ (a : A), P a ∧ ∃ (b : B), Q b",
        ),
    }
    decl = _decl(name="t", full_name="t")
    types = _obtain_binder_types(
        "obtain ⟨x, y⟩ := nested_exists", decl, decls, {}
    )
    assert types["x"] == "A"
    assert "y" not in types


def test_obtain_binder_type_resolves_in_helper_namespace():
    """The existential binder type `Bar` written in `Foo`'s source context
    means `Foo.Bar`, never the caller's `Baz.Bar`."""
    decls = {
        "Foo.Bar": _decl(
            keyword="def", name="Bar", full_name="Foo.Bar", namespace="Foo"
        ),
        "Baz.Bar": _decl(
            keyword="def", name="Bar", full_name="Baz.Bar", namespace="Baz"
        ),
        "Foo.mk_pair": _decl(
            name="mk_pair", full_name="Foo.mk_pair", namespace="Foo",
            signature=": ∃ (b : Bar), P b",
        ),
    }
    caller = _decl(name="t", full_name="Baz.t", namespace="Baz")
    types = _obtain_binder_types(
        "rcases Foo.mk_pair with ⟨b, h⟩", caller, decls, {}
    )
    assert types["b"] == "Foo.Bar"


def test_obtain_later_binder_shadows_earlier():
    decls = {
        "A": _decl(keyword="def", name="A", full_name="A"),
        "B": _decl(keyword="def", name="B", full_name="B"),
        "ex_a": _decl(name="ex_a", full_name="ex_a", signature=": ∃ (x : A), P x"),
        "ex_b": _decl(name="ex_b", full_name="ex_b", signature=": ∃ (x : B), Q x"),
    }
    decl = _decl(name="t", full_name="t")
    types = _obtain_binder_types(
        "obtain ⟨x, -⟩ := ex_a\nobtain ⟨x, -⟩ := ex_b", decl, decls, {}
    )
    assert types["x"] == "B"


def test_qualify_project_refs_roots_project_names():
    helper = _decl(
        keyword="def", name="helper", full_name="Foo.helper", namespace="Foo"
    )
    decl = _decl(
        keyword="def", name="t", full_name="Foo.t", namespace="Foo",
        source_text="def t : Nat := helper",
    )
    decls = {"Foo.helper": helper, "Foo.t": decl}
    assert (
        _qualify_project_refs(decl.source_text, set(), decl, decls)
        == "def t : Nat := _root_.Foo.helper"
    )


def test_qualify_project_refs_keeps_bound_names_strings_and_comments():
    helper = _decl(
        keyword="def", name="helper", full_name="Foo.helper", namespace="Foo"
    )
    decl = _decl(
        keyword="def", name="t", full_name="Foo.t", namespace="Foo",
        source_text="def t : Nat := 0",
    )
    decls = {"Foo.helper": helper, "Foo.t": decl}
    text = (
        'def t (helper : Nat) : Nat := -- helper stays a variable\n'
        '  helper + 0  /- helper -/\n'
        '  where_lt "helper"'
    )
    assert _qualify_project_refs(text, {"helper"}, decl, decls) == text


def test_qualify_project_refs_detects_ambiguity():
    decls = {
        "N1.x": _decl(
            keyword="def", name="x", full_name="N1.x", namespace="N1"
        ),
        "N2.x": _decl(
            keyword="def", name="x", full_name="N2.x", namespace="N2"
        ),
    }
    decl = _decl(name="t", full_name="t", opens=["open N1", "open N2"])
    with pytest.raises(GenerationError, match="ambiguous"):
        _qualify_project_refs("def t : Nat := x", set(), decl, decls)


def test_source_refs_root_open_is_not_shadowed_by_relative_namespace():
    decls = {
        "Ks.k": _decl(
            keyword="def", name="k", full_name="Ks.k", namespace="Ks"
        ),
        "Outer.Ks.k": _decl(
            keyword="def", name="k", full_name="Outer.Ks.k",
            namespace="Outer.Ks",
        ),
        "Outer.t": _decl(
            keyword="def", name="t", full_name="Outer.t", namespace="Outer",
            source_text="def t : Nat := k",
            opens=["open _root_.Ks"],
        ),
    }
    refs = _source_refs(decls["Outer.t"], decls)
    assert [r.full_name for r in refs] == ["Ks.k"]


def test_source_refs_open_matching_two_namespaces_is_ambiguous():
    """`open Ks` inside `Outer` may denote both `Outer.Ks` and root `Ks`;
    when both provide `k` the reference is ambiguous and must fail."""
    decls = {
        "Ks.k": _decl(
            keyword="def", name="k", full_name="Ks.k", namespace="Ks"
        ),
        "Outer.Ks.k": _decl(
            keyword="def", name="k", full_name="Outer.Ks.k",
            namespace="Outer.Ks",
        ),
        "Outer.t": _decl(
            keyword="def", name="t", full_name="Outer.t", namespace="Outer",
            source_text="def t : Nat := k",
            opens=["open Ks"],
        ),
    }
    with pytest.raises(GenerationError, match="ambiguous"):
        _source_refs(decls["Outer.t"], decls)


def test_source_refs_follow_extends_projection_chain():
    decls = {
        "Base": _decl(
            keyword="structure", name="Base", full_name="Base",
            source_text="structure Base where\n  (a : Nat)",
            signature="where\n  (a : Nat)",
        ),
        "Base.field": _decl(
            keyword="theorem", name="Base.field", full_name="Base.field",
            namespace="Base",
            source_text="theorem field (b : Base) : Nat :=\n  b.a",
            signature="(b : Base) : Nat",
        ),
        "Child": _decl(
            keyword="structure", name="Child", full_name="Child",
            source_text="structure Child extends Base where\n  (h : Nat)",
            signature="extends Base where\n  (h : Nat)",
        ),
        "use": _decl(
            keyword="def", name="use", full_name="use",
            source_text="def use (c : Child) : Nat :=\n  c.toBase.field",
            signature="(c : Child) : Nat",
        ),
    }
    refs = _source_refs(decls["use"], decls)
    names = [r.full_name for r in refs]
    assert "Base.field" in names


def test_resolve_inventory_name_drops_method_projection_syntax():
    index = {
        "dvd_of_dvd_pow": {"Prime.dvd_of_dvd_pow"},
        "prime_three": {"Int.prime_three"},
        "coe_nat_dvd": {"Int.coe_nat_dvd"},
        "dvd_gcd": {"Finset.dvd_gcd", "Int.dvd_gcd"},
    }
    decl = _decl(name="t", full_name="t")
    assert (
        _resolve_inventory_name(
            "Int.prime_three.dvd_of_dvd_pow", decl, {}, index
        )
        is None
    )
    assert (
        _resolve_inventory_name("Prime.dvd_of_dvd_pow", decl, {}, index)
        == "Prime.dvd_of_dvd_pow"
    )
    assert (
        _resolve_inventory_name("Int.coe_nat_dvd", decl, {}, index)
        == "Int.coe_nat_dvd"
    )
    assert _resolve_inventory_name("Int.dvd_gcd", decl, {}, index) == "Int.dvd_gcd"


def test_resolve_inventory_name_root_marker_is_stripped():
    index = {"dvd_of_dvd_pow": {"Prime.dvd_of_dvd_pow"}}
    decl = _decl(name="t", full_name="t")
    assert (
        _resolve_inventory_name("_root_.Prime.dvd_of_dvd_pow", decl, {}, index)
        == "Prime.dvd_of_dvd_pow"
    )
    assert _resolve_inventory_name("_root_.Missing.foo", decl, {}, index) is None


def test_resolve_inventory_name_dotted_through_namespace_chain():
    index = {"bar": {"Outer.Inner.bar"}}
    decl = _decl(name="t", full_name="Outer.t", namespace="Outer")
    assert (
        _resolve_inventory_name("Inner.bar", decl, {}, index)
        == "Outer.Inner.bar"
    )
    assert _resolve_inventory_name("Inner.bar", decl, {}, index) is not None
    root_decl = _decl(name="t", full_name="t")
    assert _resolve_inventory_name("Inner.bar", root_decl, {}, index) is None


def test_resolve_inventory_name_unindexed_short_is_omitted():
    index = {"other": {"A.other"}}
    decl = _decl(name="t", full_name="t", opens=["open Int"])
    assert _resolve_inventory_name("coe_nat_dvd", decl, {}, index) is None


def test_resolve_inventory_name_no_index_compatibility():
    decl = _decl(name="t", full_name="t")
    assert (
        _resolve_inventory_name("Int.prime_three.dvd_of_dvd_pow", decl, {}, None)
        == "Int.prime_three.dvd_of_dvd_pow"
    )


def test_qualify_project_refs_never_rewrites_header_name():
    decls = {
        "Foo.pair": _decl(
            keyword="def", name="pair", full_name="Foo.pair", namespace="Foo"
        ),
    }
    decl = _decl(
        keyword="def", name="pair.probe", full_name="pair.probe",
        source_text="def pair.probe : Nat := pair",
        opens=["open Foo"],
    )
    decls["pair.probe"] = decl
    assert _qualify_project_refs(
        decl.source_text, set(), decl, decls
    ) == "def pair.probe : Nat := _root_.Foo.pair"


def test_qualify_project_refs_keeps_compound_receiver_suffix():
    decls = {
        "adjoin": _decl(keyword="def", name="adjoin", full_name="adjoin"),
    }
    decl = _decl(name="t", full_name="t", source_text="def t : Nat := 0")
    decls["t"] = decl
    text = "def t (f : Nat → Nat) (x : Nat) : Nat := (f x).adjoin + x.adjoin"
    assert _qualify_project_refs(text, {"f", "x"}, decl, decls) == text


def test_qualify_project_refs_keeps_char_literals_and_nested_comments():
    decls = {"c": _decl(keyword="def", name="c", full_name="c")}
    decl = _decl(name="t", full_name="t", source_text="def t : Nat := 0")
    decls["t"] = decl
    text = (
        "def t : Char × Nat := ('c', 0) /- outer /- c -/ still comment -/"
    )
    assert _qualify_project_refs(text, set(), decl, decls) == text


def test_qualify_project_refs_qualifies_free_constant_projection():
    decls = {"hζ": _decl(keyword="def", name="hζ", full_name="hζ")}
    decl = _decl(name="t", full_name="t", source_text="def t : Nat := 0")
    decls["t"] = decl
    assert (
        _qualify_project_refs("def t : Nat := hζ.toNat", set(), decl, decls)
        == "def t : Nat := _root_.hζ.toNat"
    )


def test_context_variable_command_uses_its_own_variable_scope():
    decl = _decl(
        name="t", full_name="t",
        context=(
            LeanContextCommand(
                module="M", source_path="M.lean", line=0, end_line=0,
                namespace="", scope=(), kind="variable",
                source_text="variable (K : Type*)",
                exported=False, supported=True,
                variables=("variable (K : Type*)",),
            ),
            LeanContextCommand(
                module="M", source_path="M.lean", line=1, end_line=1,
                namespace="", scope=(), kind="variable",
                source_text="variable (x : K)",
                exported=False, supported=True,
                variables=("variable (K : Type*)", "variable (x : K)"),
            ),
        ),
    )
    decls = {
        "K": _decl(keyword="def", name="K", full_name="K"),
        "t": decl,
    }
    assert _context_lines(decl, decls) == ([], [
        "variable (K : Type*)",
        "variable (x : K)",
    ])


def test_context_variable_resolution_uses_command_opens_not_later_ones():
    decl = _decl(
        name="t", full_name="t",
        opens=["open Foo", "open Bar"],
        context=(
            LeanContextCommand(
                module="M", source_path="M.lean", line=0, end_line=0,
                namespace="", scope=(), kind="open",
                source_text="open Foo",
                exported=False, supported=True,
                opens=("open Foo",),
            ),
            LeanContextCommand(
                module="M", source_path="M.lean", line=1, end_line=1,
                namespace="", scope=(), kind="variable",
                source_text="variable (v : x)",
                exported=False, supported=True,
                variables=("variable (v : x)",),
                opens=("open Foo",),
            ),
            LeanContextCommand(
                module="M", source_path="M.lean", line=2, end_line=2,
                namespace="", scope=(), kind="open",
                source_text="open Bar",
                exported=False, supported=True,
                opens=("open Foo", "open Bar"),
            ),
        ),
    )
    decls = {
        "Foo.x": _decl(keyword="def", name="x", full_name="Foo.x", namespace="Foo"),
        "Bar.x": _decl(keyword="def", name="x", full_name="Bar.x", namespace="Bar"),
        "t": decl,
    }
    _root_lines, lines = _context_lines(decl, decls)
    assert "variable (v : _root_.Foo.x)" in lines


def test_noncomputable_section_wraps_generated_definitions(tmp_path):
    blueprint = Blueprint(
        nodes=[_def_node("def:d", ["d"], 0)], chapters=["Ch"]
    )
    decls = {
        "d": _decl(
            keyword="def", name="d", full_name="d",
            source_text="def d : Nat := 0",
            noncomputable_section=True,
        ),
        "e": _decl(
            keyword="def", name="e", full_name="e",
            source_text="def e : Nat := 0",
        ),
    }
    game = build_game(blueprint, decls, toolchain="v4.31.0", title="T")
    write_game(game, tmp_path)
    defs = (tmp_path / "Game" / "Generated" / "Defs.lean").read_text()
    assert "noncomputable section\n" in defs
    block = defs.index("noncomputable section")
    assert defs.index("def d : Nat := 0") > block
    assert "noncomputable section\n\ndef e" not in defs
