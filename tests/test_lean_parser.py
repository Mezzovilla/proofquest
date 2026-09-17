from proofquest.game_model import Game
from proofquest.generator import _render_defs
from proofquest.lean_parser import _parse_file, parse_project

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
