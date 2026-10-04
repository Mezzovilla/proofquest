import pytest

from proofquest.game_model import Game
from proofquest.generator import _render_defs
from proofquest.lean_parser import LeanParseError, _parse_file, parse_project

SOURCE = """namespace Toy

def hello : String := "World"

def A (n : Nat) : Prop :=
  n + 1 ≤ n + 2

theorem lemma1 (n : Nat) : A n := by
  unfold A
  omega

theorem main (n : Nat) : A n ∧ A (n + 1) := by
  constructor
  · exact lemma1 n
  · exact lemma1 (n + 1)

end Toy
"""


def write_source(tmp_path):
    path = tmp_path / "Basic.lean"
    path.write_text(SOURCE, encoding="utf-8")
    return path


def test_namespaces_and_names(tmp_path):
    decls = {d.full_name: d for d in _parse_file(write_source(tmp_path))}
    assert set(decls) == {"Toy.hello", "Toy.A", "Toy.lemma1", "Toy.main"}
    assert decls["Toy.A"].namespace == "Toy"
    assert decls["Toy.A"].is_definition
    assert not decls["Toy.lemma1"].is_definition


def test_signature_and_proof_split(tmp_path):
    decls = {d.full_name: d for d in _parse_file(write_source(tmp_path))}
    lemma1 = decls["Toy.lemma1"]
    assert lemma1.signature == "(n : Nat) : A n"
    assert lemma1.proof.startswith("by")
    assert "omega" in lemma1.proof

    main = decls["Toy.main"]
    assert main.signature == "(n : Nat) : A n ∧ A (n + 1)"
    assert "exact lemma1 (n + 1)" in main.proof


def test_def_source_text_is_verbatim(tmp_path):
    decls = {d.full_name: d for d in _parse_file(write_source(tmp_path))}
    assert decls["Toy.A"].source_text == "def A (n : Nat) : Prop :=\n  n + 1 ≤ n + 2"
    # `:=` inside the string literal of `hello` must not confuse the splitter
    assert decls["Toy.hello"].signature == ": String"


def test_parse_project_skips_excluded_dirs(tmp_path):
    write_source(tmp_path)
    hidden = tmp_path / ".lake" / "Other.lean"
    hidden.parent.mkdir()
    hidden.write_text("def ghost : Nat := 0\n", encoding="utf-8")
    output = tmp_path / "out" / "Generated.lean"
    output.parent.mkdir()
    output.write_text("def generated : Nat := 0\n", encoding="utf-8")
    decls = parse_project(tmp_path, (output.parent,))
    assert "ghost" not in decls
    assert "generated" not in decls
    assert "Toy.lemma1" in decls


def test_active_variables_are_attached_to_declarations(tmp_path):
    path = tmp_path / "Variables.lean"
    path.write_text(
        "namespace Toy\n\nvariable {α : Type*} [Inhabited α]\n\ndef value (x : α) := x\n\nend Toy\n",
        encoding="utf-8",
    )
    decl = _parse_file(path)[0]
    assert decl.variables == ["variable {α : Type*} [Inhabited α]"]


def test_local_import_is_filtered(tmp_path):
    local_dir = tmp_path / "QuasarProject"
    local_dir.mkdir()
    (local_dir / "Local.lean").write_text(
        "namespace QuasarProject\n\ndef local_value : Nat := 42\n\nend QuasarProject\n",
        encoding="utf-8",
    )
    consumer = tmp_path / "Consumer.lean"
    consumer.write_text(
        "import QuasarProject.Local\n"
        "import Mathlib.Data.Nat.Basic\n"
        "\n"
        "def consumer_value : Nat := local_value + 1\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    consumer_decl = decls["consumer_value"]
    assert "Mathlib.Data.Nat.Basic" in consumer_decl.imports
    assert "QuasarProject.Local" not in consumer_decl.imports


def test_render_defs_omits_local_import(tmp_path):
    local_dir = tmp_path / "QuasarProject"
    local_dir.mkdir()
    (local_dir / "Local.lean").write_text(
        "namespace QuasarProject\n\ndef local_value : Nat := 42\n\nend QuasarProject\n",
        encoding="utf-8",
    )
    consumer = tmp_path / "Consumer.lean"
    consumer.write_text(
        "import QuasarProject.Local\n"
        "import Mathlib.Data.Nat.Basic\n"
        "\n"
        "def consumer_value : Nat := local_value + 1\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    decl = decls["consumer_value"]
    game = Game(
        title="Test Game",
        intro_md="",
        languages="English",
        worlds=[],
        definitions=[(decl, None)],
        tactics=[],
        theorems=[],
        toolchain="",
    )
    rendered = _render_defs(game)
    assert "import Mathlib.Data.Nat.Basic" in rendered
    assert "import QuasarProject.Local" not in rendered


def test_dir_names_atlas_game_proofquest_are_scanned(tmp_path):
    for name in ("atlas", "game", "proofquest"):
        sub = tmp_path / name
        sub.mkdir()
        (sub / f"{name.capitalize()}.lean").write_text(
            f"def {name}_value : Nat := 0\n",
            encoding="utf-8",
        )
    decls = parse_project(tmp_path)
    assert "atlas_value" in decls
    assert "game_value" in decls
    assert "proofquest_value" in decls


ROOT_SOURCE = """namespace IsCyclotomicExtension.Rat.Three

lemma helper : True := trivial

lemma _root_.IsPrimitiveRoot.lambda_prime : True := trivial

end IsCyclotomicExtension.Rat.Three

namespace Solution

noncomputable
def _root_.Solution'_final : Nat where
  a := 1
  b := 2

lemma _root_.Solution'_final_multiplicity : Solution'_final = Solution'_final := rfl

end Solution
"""


def test_root_qualified_declarations(tmp_path):
    path = tmp_path / "Root.lean"
    path.write_text(ROOT_SOURCE, encoding="utf-8")
    decls = {d.full_name: d for d in _parse_file(path)}
    assert set(decls) == {
        "IsCyclotomicExtension.Rat.Three.helper",
        "IsPrimitiveRoot.lambda_prime",
        "Solution'_final",
        "Solution'_final_multiplicity",
    }
    prime = decls["IsPrimitiveRoot.lambda_prime"]
    assert prime.namespace == "IsPrimitiveRoot"
    assert prime.name == "lambda_prime"
    assert "_root_" not in prime.full_name
    final = decls["Solution'_final"]
    assert final.namespace == ""
    assert final.name == "Solution'_final"
    assert "_root_" not in final.full_name
    mult = decls["Solution'_final_multiplicity"]
    assert mult.namespace == ""
    assert "_root_" not in mult.full_name


def test_standalone_modifier_is_part_of_source_text(tmp_path):
    path = tmp_path / "Root.lean"
    path.write_text(ROOT_SOURCE, encoding="utf-8")
    decls = {d.full_name: d for d in _parse_file(path)}
    final = decls["Solution'_final"]
    assert final.source_text.startswith("noncomputable\ndef _root_.Solution'_final")
    assert "b := 2" in final.source_text
    helper = decls["IsCyclotomicExtension.Rat.Three.helper"]
    assert helper.source_text == "lemma helper : True := trivial"


def test_structures_in_section(tmp_path):
    path = tmp_path / "Structures.lean"
    path.write_text(
        "namespace Toy\n\nsection Solution'\n\n"
        "lemma before : True := trivial\n\n"
        "structure Solution' where\n"
        "  (a : Nat)\n"
        "  (b : Nat)\n"
        "  (H : a + b = 3)\n\n"
        "structure Solution extends Solution' where\n"
        "  (hab : a ≤ b)\n\n"
        "lemma after : True := trivial\n\n"
        "end Solution'\n\nend Toy\n",
        encoding="utf-8",
    )
    decls = {d.full_name: d for d in _parse_file(path)}
    assert decls["Toy.Solution'"].keyword == "structure"
    assert decls["Toy.Solution'"].is_definition
    assert decls["Toy.Solution'"].proof is None
    assert "(H : a + b = 3)" in decls["Toy.Solution'"].signature
    assert "before" not in decls["Toy.Solution'"].source_text
    assert decls["Toy.Solution"].keyword == "structure"
    assert "extends Solution' where" in decls["Toy.Solution"].signature
    assert "(hab : a ≤ b)" in decls["Toy.Solution"].signature
    assert decls["Toy.before"].proof == "trivial"
    assert decls["Toy.after"].proof == "trivial"


def test_render_defs_root_qualified(tmp_path):
    path = tmp_path / "Root.lean"
    path.write_text(ROOT_SOURCE, encoding="utf-8")
    decls = {d.full_name: d for d in _parse_file(path)}
    game = Game(
        title="Test Game",
        intro_md="",
        languages="English",
        worlds=[],
        definitions=[(decls["Solution'_final"], None)],
        tactics=[],
        theorems=[],
        toolchain="",
    )
    rendered = _render_defs(game)
    assert "noncomputable\ndef _root_.Solution'_final" in rendered
    assert 'DefinitionDoc Solution\'_final as "Solution\'_final"' in rendered
    assert "namespace Solution" not in rendered


def test_notation_command_ends_declaration_block(tmp_path):
    """A `notation` command is a file-level command, never part of the
    preceding declaration's `source_text`."""
    path = tmp_path / "Notation.lean"
    path.write_text(
        'def a : Nat := 1\nnotation "K" => Nat\ndef b : Nat := 2\n',
        encoding="utf-8",
    )
    decls = {d.full_name: d for d in _parse_file(path)}
    assert decls["a"].source_text == "def a : Nat := 1"
    assert decls["b"].source_text == "def b : Nat := 2"


def test_local_syntax_commands_are_recorded(tmp_path):
    path = tmp_path / "Basic.lean"
    path.write_text(
        'local notation "η" => Nat\n\n'
        "namespace Toy\n\n"
        "def base : η := 1\n\n"
        "end Toy\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    base = decls["Toy.base"]
    assert base.module == "Basic"
    assert base.local_syntax == ["notation"]


def test_local_syntax_follows_project_imports(tmp_path):
    """Notation defined in an imported *project* module shapes the importing
    file's context even though the import itself is not copied."""
    (tmp_path / "Notation.lean").write_text(
        'notation "K" => Nat\n', encoding="utf-8"
    )
    (tmp_path / "Use.lean").write_text(
        "import Notation\nimport Mathlib.Data.Nat.Basic\n\n"
        "def uses_k : K := 1\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    uses_k = decls["uses_k"]
    assert "notation" in uses_k.local_syntax
    assert "Mathlib.Data.Nat.Basic" in uses_k.imports


def test_local_syntax_only_applies_after_its_position(tmp_path):
    """A command cannot affect declarations earlier in the same file."""
    (tmp_path / "Basic.lean").write_text(
        "def early : Nat := 1\n"
        'notation "K" => Nat\n'
        "def late : Nat := 2\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    assert decls["early"].local_syntax == []
    assert decls["late"].local_syntax == ["notation"]


def test_local_syntax_ignores_comments_and_scoped_set_option(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "/- notation \"fake\" => Nat -/\n"
        "-- set_option maxHeartbeats 0\n"
        "set_option pp.all true in\n"
        "def a : Nat := 1\n"
        "def b : Nat := 2\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    assert decls["a"].local_syntax == []
    assert decls["b"].local_syntax == []


def test_local_syntax_includes_private_and_macro_forms(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        'private notation "K" => Nat\n'
        'macro "m" : term => `(1)\n'
        "def a : Nat := 1\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    assert decls["a"].local_syntax == ["notation", "macro"]


def test_file_wide_set_option_is_file_context(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "set_option maxHeartbeats 0\n"
        "def a : Nat := 1\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    assert decls["a"].local_syntax == ["set_option"]


def test_local_syntax_ignores_nested_block_comments(tmp_path):
    """Lean block comments nest: a `-/` inside only closes the inner one,
    so a trailing `notation` after the outer `-/` must not be scanned."""
    (tmp_path / "Basic.lean").write_text(
        "/- outer /- inner -/ notation \"fake\" => Nat -/\n"
        "def s : String := \"-- notation \\\"s\\\" => Nat\"\n"
        "def a : Nat := 1\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    assert decls["a"].local_syntax == []
    assert decls["s"].local_syntax == []


def test_no_local_syntax_in_plain_files(tmp_path):
    decls = parse_project(write_source(tmp_path).parent)
    assert decls["Toy.A"].local_syntax == []


def test_no_special_case_for_fixture_project_names(tmp_path):
    consumer = tmp_path / "Consumer.lean"
    consumer.write_text(
        "import BanachSteinhausSokalProof.Local\n"
        "import LeanAtlas\n"
        "import Mathlib.Data.Nat.Basic\n"
        "\n"
        "def consumer_value : Nat := 0\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    consumer_decl = decls["consumer_value"]
    assert "BanachSteinhausSokalProof.Local" in consumer_decl.imports
    assert "LeanAtlas" in consumer_decl.imports
    assert "Mathlib.Data.Nat.Basic" in consumer_decl.imports


def test_plain_global_notation_is_transported(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "namespace Toy\n\n"
        "abbrev NormMap (T : Type*) := T\n\n"
        'notation "‖" T "·‖" => NormMap T\n\n'
        "theorem uses_norm (T : Type*) (x : ‖T·‖) : ‖T ·‖ := by\n"
        "  exact x\n\n"
        "end Toy\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    target = decls["Toy.NormMap"]
    theorem = decls["Toy.uses_norm"]
    assert target.local_syntax == []
    assert target.notations == []
    assert theorem.local_syntax == []
    assert len(theorem.notations) == 1
    notation = theorem.notations[0]
    assert notation.module == "Basic"
    assert notation.namespace == "Toy"
    assert notation.pattern == '"‖" T "·‖"'
    assert notation.target == "Toy.NormMap"
    assert notation.arguments == ("T",)


def test_generated_game_root_is_excluded_by_structure(tmp_path):
    original = tmp_path / "Original.lean"
    original.write_text("def original_value : Nat := 1\n", encoding="utf-8")
    generated = tmp_path / "archive"
    (generated / "Game" / "Generated").mkdir(parents=True)
    (generated / "Game.lean").write_text("MakeGame\n", encoding="utf-8")
    (generated / "Game" / "Metadata.lean").write_text("", encoding="utf-8")
    (generated / "Game" / "Generated" / "Defs.lean").write_text(
        "def original_value : String := \"wrong\"\n", encoding="utf-8"
    )
    (generated / "lakefile.lean").write_text("", encoding="utf-8")
    (generated / "lean-toolchain").write_text("", encoding="utf-8")
    ordinary = tmp_path / "ordinary"
    ordinary.mkdir()
    (ordinary / "Game.lean").write_text(
        "def ordinary_value : Nat := 2\n", encoding="utf-8"
    )
    decls = parse_project(tmp_path)
    assert decls["original_value"].module == "Original"
    assert decls["original_value"].signature == ": Nat"
    assert decls["ordinary_value"].module == "ordinary.Game"


def test_project_import_closure_supplies_notation_and_external_imports(tmp_path):
    (tmp_path / "Base.lean").write_text(
        "import Mathlib.Topology.Basic\n"
        "namespace Toy\n"
        "abbrev NormMap (T : Type*) := T\n"
        'notation "‖" T "·‖" => NormMap T\n'
        "end Toy\n",
        encoding="utf-8",
    )
    (tmp_path / "Middle.lean").write_text("import Base\n", encoding="utf-8")
    (tmp_path / "Use.lean").write_text(
        "import Middle\n"
        "namespace Toy\n"
        "theorem uses_norm (T : Type*) (x : ‖T·‖) : True := by\n"
        "  trivial\n"
        "end Toy\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    theorem = decls["Toy.uses_norm"]
    assert theorem.notations[0].module == "Base"
    assert theorem.notations[0].target == "Toy.NormMap"
    assert theorem.imports == ["Mathlib.Topology.Basic"]


def test_supported_and_unsupported_notation_still_reject(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "namespace Toy\n"
        "abbrev NormMap (T : Type*) := T\n"
        'notation "‖" T "·‖" => NormMap T\n'
        'local notation "N" => NormMap Nat\n'
        "theorem uses_norm (T : Type*) (x : ‖T·‖) : True := by\n"
        "  trivial\n"
        "end Toy\n",
        encoding="utf-8",
    )
    theorem = parse_project(tmp_path)["Toy.uses_norm"]
    assert "notation" in theorem.local_syntax
    assert theorem.notations


def test_unsupported_notation_forms_remain_context(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "namespace Toy\n"
        "abbrev NormMap (T : Type*) := T\n"
        'scoped notation "S" => NormMap Nat\n'
        'notation3 "M" => NormMap Nat\n'
        'notation "L" =>\n'
        "  NormMap Nat\n"
        'notation "T" => missing\n'
        'notation "H" => theorem_target\n'
        "theorem theorem_target : True := by\n  trivial\n"
        "theorem late : True := by\n  trivial\n"
        "end Toy\n",
        encoding="utf-8",
    )
    late = parse_project(tmp_path)["Toy.late"]
    assert late.local_syntax == ["notation", "notation3"]


def test_ambiguous_same_pattern_rejects(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "namespace Toy\n"
        "abbrev A (T : Type*) := T\n"
        "abbrev B (T : Type*) := T\n"
        'notation "X" T => A T\n'
        'notation "X" T => B T\n'
        "theorem late : True := by\n  trivial\n"
        "end Toy\n",
        encoding="utf-8",
    )
    assert parse_project(tmp_path)["Toy.late"].local_syntax == ["notation"]


def test_root_qualified_notation_target_is_not_shadowed(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "abbrev TopA (T : Type*) := T\n"
        "namespace Toy\n"
        "abbrev TopA (T : Type*) := T\n"
        'notation "R" T => _root_.TopA T\n'
        "theorem uses_root (T : Type*) (x : R T) : True := by\n"
        "  trivial\n"
        "end Toy\n",
        encoding="utf-8",
    )
    theorem = parse_project(tmp_path)["Toy.uses_root"]
    assert theorem.notations[0].target == "TopA"


def test_ambiguous_visible_pattern_across_imports_rejects(tmp_path):
    (tmp_path / "N1.lean").write_text(
        "namespace One\n"
        "abbrev F (T : Type*) := T\n"
        'notation "X" T => F T\n'
        "end One\n",
        encoding="utf-8",
    )
    (tmp_path / "N2.lean").write_text(
        "namespace Two\n"
        "abbrev G (T : Type*) := T\n"
        'notation  "X"   X   => G X\n'
        "end Two\n",
        encoding="utf-8",
    )
    (tmp_path / "Use.lean").write_text(
        "import N1\nimport N2\n"
        "theorem late : True := by\n  trivial\n",
        encoding="utf-8",
    )
    assert parse_project(tmp_path)["late"].local_syntax == ["notation"]


def test_notation_with_indented_continuation_is_unsupported(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "abbrev F (T : Type*) := T\n"
        'notation "X" T => F T\n'
        "  T\n"
        "theorem late : True := by\n  trivial\n",
        encoding="utf-8",
    )
    late = parse_project(tmp_path)["late"]
    assert late.local_syntax == ["notation"]
    assert late.notations == []


def test_closed_scope_context_does_not_leak(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "namespace Hidden\n"
        "def secret : Nat := 1\n"
        "end Hidden\n"
        "section\n"
        "open Hidden\n"
        "variable (n : Nat)\n"
        'local notation "Q" => Nat\n'
        "local instance : Inhabited Nat := ⟨0⟩\n"
        "def inside : Nat := n\n"
        "end\n"
        "theorem early : True := by\n  trivial\n"
        "namespace Ns\n"
        "instance : Nonempty Nat := ⟨0⟩\n"
        'notation "W" => Nat\n'
        "end Ns\n"
        "def late : Nat := 0\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    late = decls["late"]
    assert late.opens == []
    assert late.variables == []
    assert not any(n.pattern == '"Q"' for n in late.notations)
    assert not [i for i in late.instances if "Inhabited" in i.signature]
    assert [i for i in late.instances if "Nonempty" in i.signature]
    assert any(
        i.full_name.startswith("Ns.") for i in late.instances
    )
    early = decls["early"]
    assert early.instances == []


def test_local_notation_dies_at_scope_end(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "abbrev F (T : Type*) := T\n"
        "section\n"
        'local notation "X" T => F T\n'
        "theorem inside : True := by\n  trivial\n"
        "end\n"
        "theorem outside : True := by\n  trivial\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    assert len(decls["inside"].notations) == 1
    assert decls["outside"].notations == []


def test_exported_instance_imported_without_open(tmp_path):
    (tmp_path / "Base.lean").write_text(
        "class Tagged (α : Type) where\n"
        "namespace Bs\n"
        "instance : Tagged Nat := ⟨⟩\n"
        "end Bs\n"
        "local instance : Tagged Bool := ⟨⟩\n",
        encoding="utf-8",
    )
    (tmp_path / "Use.lean").write_text(
        "import Base\n"
        "def pick : Nat := default\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    pick = decls["pick"]
    names = {i.full_name for i in pick.instances}
    (only,) = names
    assert only.startswith(f"Bs._instance_m{b'Base'.hex()}_")


def test_instance_forms_parse_and_reject_correctly(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "class C (α : Type) where\n"
        "instance (α : Type) [C α] : C (List α) := ⟨⟩\n"
        "local instance named : C Nat := ⟨⟩\n"
        "instance viaWhere : C Bool where\n"
        "section\n"
        "attribute [simp] Nat.add_comm\n"
        "instance attrFree : C Char := ⟨⟩\n"
        "end\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    (anon,) = [d for d in decls.values() if d.name.startswith("_instance_")]
    assert anon.signature == "(α : Type) [C α] : C (List α)"
    assert decls["named"].modifiers == ("local",)
    assert "viaWhere" not in decls
    assert decls["attrFree"].local_syntax == ["instance", "attribute"]


def test_anonymous_instance_names_are_module_scoped(tmp_path):
    for mod in ("A/B", "C/B"):
        (tmp_path / mod.split("/")[0]).mkdir(exist_ok=True)
        (tmp_path / f"{mod}.lean").write_text(
            "class C (α : Type) where\n"
            "instance : C Nat := ⟨⟩\n",
            encoding="utf-8",
        )
    decls = parse_project(tmp_path)
    assert f"_instance_m{b'A.B'.hex()}_l1" in decls
    assert f"_instance_m{b'C.B'.hex()}_l1" in decls


def test_anonymous_instance_names_distinguish_slug_colliding_modules(tmp_path):
    for mod in ("A/B", "A_B"):
        parent = tmp_path / mod.split("/")[0]
        if "/" in mod:
            parent.mkdir(exist_ok=True)
        (tmp_path / f"{mod}.lean").write_text(
            "class C (α : Type) where\n"
            "instance : C Nat := ⟨⟩\n",
            encoding="utf-8",
        )
    decls = parse_project(tmp_path)
    assert f"_instance_m{b'A.B'.hex()}_l1" in decls
    assert f"_instance_m{b'A_B'.hex()}_l1" in decls


def test_anonymous_instance_names_cover_same_basename_and_root(tmp_path):
    (tmp_path / "Sub").mkdir()
    (tmp_path / "B.lean").write_text(
        "class C (α : Type) where\n"
        "instance : C Nat := ⟨⟩\n",
        encoding="utf-8",
    )
    (tmp_path / "Sub" / "B.lean").write_text(
        "instance : C Nat := ⟨⟩\n"
        "namespace Ns\n"
        "instance : C Bool := ⟨⟩\n"
        "end Ns\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    assert f"_instance_m{b'B'.hex()}_l1" in decls
    assert f"_instance_m{b'Sub.B'.hex()}_l0" in decls
    assert f"Ns._instance_m{b'Sub.B'.hex()}_l2" in decls


def test_anonymous_instance_name_collision_fails_closed(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "class C (α : Type) where\n"
        "instance : C Nat := ⟨⟩\n"
        f"def _instance_m{b'Basic'.hex()}_l1 : Nat := 0\n",
        encoding="utf-8",
    )
    with pytest.raises(LeanParseError, match="collides"):
        parse_project(tmp_path)


def test_scoped_commands_need_line_order_and_open_scoped(tmp_path):
    (tmp_path / "Base.lean").write_text(
        "namespace Ns\n"
        "def marker : Nat := 0\n"
        "end Ns\n"
        "namespace Ns\n"
        'scoped notation "LATE" => Nat\n'
        "end Ns\n",
        encoding="utf-8",
    )
    (tmp_path / "Use.lean").write_text(
        "import Base\n"
        "open Ns\n"
        "def early : Nat := marker\n"
        "namespace Ns\n"
        "def mid : Nat := 1\n"
        "end Ns\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    assert decls["early"].local_syntax == []
    assert decls["Ns.mid"].local_syntax == ["notation"]


def test_later_scoped_commands_do_not_taint_earlier_same_namespace(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "namespace Ns\n"
        "def early : Nat := 1\n"
        'scoped notation "LATE" => Nat\n'
        "def late : Nat := 2\n"
        "end Ns\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    assert decls["Ns.early"].local_syntax == []
    assert decls["Ns.late"].local_syntax == ["notation"]


def test_imported_scoped_activation_requires_open_scoped(tmp_path):
    (tmp_path / "Base.lean").write_text(
        "namespace Ns\n"
        'scoped notation "S" => Nat\n'
        "end Ns\n",
        encoding="utf-8",
    )
    (tmp_path / "Plain.lean").write_text(
        "import Base\n"
        "open Ns\n"
        "def plain : Nat := 1\n",
        encoding="utf-8",
    )
    (tmp_path / "Scoped.lean").write_text(
        "import Base\n"
        "open scoped Ns\n"
        "def sc : Nat := 1\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    assert decls["plain"].local_syntax == []
    scoped = decls["sc"]
    assert scoped.local_syntax == ["notation"]
    origin = next(
        c for c in scoped.context if not c.supported and c.kind == "notation"
    )
    assert origin.source_path == "Base.lean"
    assert origin.line == 1


def test_private_instance_is_file_scoped_not_section_scoped(tmp_path):
    (tmp_path / "Base.lean").write_text(
        "class C (α : Type) where\n"
        "section\n"
        "private instance : C Nat := ⟨⟩\n"
        "end\n"
        "def after : Nat := 0\n",
        encoding="utf-8",
    )
    (tmp_path / "Use.lean").write_text(
        "import Base\n"
        "def importer : Nat := 0\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    expected = f"_instance_m{b'Base'.hex()}_l2"
    assert [i.name for i in decls["after"].instances] == [expected]
    assert [i.name for i in decls["importer"].instances] == [expected]


def test_duplicate_same_target_notation_is_supported(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "abbrev A (T : Type*) := T\n"
        'notation "X" T => A T\n'
        'notation "X" T => A T\n'
        "theorem late : True := by\n  trivial\n",
        encoding="utf-8",
    )
    late = parse_project(tmp_path)["late"]
    assert late.local_syntax == []
    assert len(late.notations) == 1


def _no_command_local_in(decl):
    return all("in" not in c.source_text.split() for c in decl.context)


def test_command_local_open_binds_only_next_declaration(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "open Nat in\n"
        "theorem target : Nat.succ 0 = 1 := rfl\n\n"
        "theorem follow : Nat.succ 0 = 1 := rfl\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    target, follow = decls["target"], decls["follow"]
    assert target.local_syntax == ["open"]
    assert target.opens == []
    origin = next(c for c in target.context if c.kind == "open")
    assert not origin.supported
    assert origin.source_path == "Basic.lean"
    assert origin.line == 0
    assert follow.local_syntax == []
    assert follow.opens == []
    assert _no_command_local_in(follow)


def test_command_local_open_skips_blank_comments_modifiers_and_attrs(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "section\n\n"
        "open Nat in\n\n"
        "-- a comment between open and target\n\n"
        "private\n"
        "theorem target : Nat.succ 0 = 1 := rfl\n\n"
        "end\n\n"
        "open Nat in\n"
        "@[simp] theorem attrTarget : Nat.succ 0 = 1 := rfl\n\n"
        "open Nat in\n\n"
        "@[simp]\n"
        "theorem attrLine : Nat.succ 0 = 1 := rfl\n\n"
        "theorem follow : Nat.succ 0 = 1 := rfl\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    assert decls["target"].local_syntax == ["open"]
    assert decls["attrTarget"].local_syntax == ["open"]
    assert decls["attrLine"].local_syntax == ["open"]
    follow = decls["follow"]
    assert follow.local_syntax == []
    assert follow.opens == []
    assert _no_command_local_in(follow)


def test_command_local_open_inside_namespace(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "namespace Ns\n\n"
        "open Nat in\n"
        "theorem target : Nat.succ 0 = 1 := rfl\n\n"
        "theorem follow : Nat.succ 0 = 1 := rfl\n\n"
        "end Ns\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    assert decls["Ns.target"].local_syntax == ["open"]
    assert decls["Ns.follow"].local_syntax == []
    assert _no_command_local_in(decls["Ns.follow"])


def test_command_local_variable_is_conservatively_unsupported(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "variable (n : Nat) in\n"
        "theorem target : Nat.succ 0 = 1 := rfl\n\n"
        "theorem follow : Nat.succ 0 = 1 := rfl\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    assert decls["target"].local_syntax == ["variable"]
    assert decls["target"].variables == []
    follow = decls["follow"]
    assert follow.local_syntax == []
    assert follow.variables == []
    assert _no_command_local_in(follow)


def test_same_line_command_local_open_misses_decl_without_leaking(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "open Nat in theorem target : Nat.succ 0 = 1 := rfl\n\n"
        "theorem follow : Nat.succ 0 = 1 := rfl\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    assert "target" not in decls
    follow = decls["follow"]
    assert follow.local_syntax == []
    assert follow.opens == []
    assert _no_command_local_in(follow)


def test_command_local_open_without_identifiable_target_fails_closed(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "theorem keep : Nat.succ 0 = 1 := rfl\n\n"
        "open Nat in\n\n"
        "-- nothing follows\n",
        encoding="utf-8",
    )
    with pytest.raises(LeanParseError, match="Basic.lean"):
        parse_project(tmp_path)


def test_ordinary_open_still_applies_normally(tmp_path):
    (tmp_path / "Basic.lean").write_text(
        "open Nat\n\n"
        "theorem target : succ 0 = 1 := rfl\n\n"
        "theorem follow : succ 0 = 1 := rfl\n",
        encoding="utf-8",
    )
    decls = parse_project(tmp_path)
    assert decls["target"].opens == ["open Nat"]
    assert decls["follow"].opens == ["open Nat"]
    assert decls["follow"].local_syntax == []
