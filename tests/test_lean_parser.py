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
    output = tmp_path / "game" / "Generated.lean"
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
