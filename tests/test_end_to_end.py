"""End-to-end test: generate the game for the toy_example project."""

import filecmp
from pathlib import Path

import pytest

from proofquest.cli import main

PROJECT = Path(__file__).parent / "toy_example"  # self-contained test fixture


@pytest.fixture(scope="module")
def generated(tmp_path_factory):
    out = tmp_path_factory.mktemp("game")
    assert main(["generate", str(PROJECT), "-o", str(out), "--title", "Toy Game"]) == 0
    return out


def test_check_command():
    assert main(["check", str(PROJECT)]) == 0


def test_expected_files(generated):
    for relative in [
        "Game.lean",
        "Game/Metadata.lean",
        "Game/Generated/Defs.lean",
        "Game/Generated/TacticDocs.lean",
        "Game/Generated/TheoremDocs.lean",
        "Game/Levels/AToyExample.lean",
        "Game/Levels/AToyExample/L01_lemma1.lean",
        "Game/Levels/AToyExample/L02_lemma2.lean",
        "Game/Levels/AToyExample/L03_lemma3.lean",
        "Game/Levels/AToyExample/L04_main.lean",
        "lakefile.lean",
        "lean-toolchain",
    ]:
        assert (generated / relative).exists(), relative


def test_level_content(generated):
    level1 = (generated / "Game/Levels/AToyExample/L01_lemma1.lean").read_text()
    assert 'World "AToyExample"' in level1
    assert "Level 1" in level1
    assert "Statement lemma1 (n : Nat) : A n := by" in level1
    assert "namespace Toy" in level1
    assert "NewDefinition Toy.A" in level1
    assert "NewTactic unfold omega" in level1

    level3 = (generated / "Game/Levels/AToyExample/L03_lemma3.lean").read_text()
    assert "import Game.Levels.AToyExample.L02_lemma2" in level3
    assert "have h := lemma2 (n + 1)" in level3  # sample solution embedded
    assert "Hint " in level3  # LaTeX proof became a hint
    assert "NewTactic «have» exact" in level3  # keyword tactics are quoted
    # `lemma2` is a project-local theorem (its own level); it must not be
    # re-declared with `NewTheorem`, since the GameServer unlocks it
    # automatically once its level is solved.
    assert "NewTheorem" not in level3

    main_level = (generated / "Game/Levels/AToyExample/L04_main.lean").read_text()
    assert "Statement main (n : Nat) : A n ∧ B (n + 1) := by" in main_level


def test_defs_are_copied_verbatim(generated):
    defs = (generated / "Game/Generated/Defs.lean").read_text()
    assert "def A (n : Nat) : Prop :=\n  n + 1 ≤ n + 2" in defs
    assert 'DefinitionDoc Toy.A as "A"' in defs
    assert "theorem" not in defs  # theorems must NOT leak into the game


def test_legacy_toolchain_emits_v4_7_doc_syntax(tmp_path):
    """GameServer < v4.23.0: `DefinitionDoc` takes no `in` clause and
    `TheoremDoc` mandates `in "category"` (verified against v4.7.0 sources;
    a docstring plus a trailing content string is rejected, so the docstring
    is kept and no content string is emitted)."""
    out = tmp_path / "game_legacy"
    assert main(
        ["generate", str(PROJECT), "-o", str(out),
         "--toolchain", "leanprover/lean4:v4.7.0"]
    ) == 0
    defs = (out / "Game/Generated/Defs.lean").read_text()
    assert 'DefinitionDoc Toy.A as "A"' in defs
    assert 'DefinitionDoc Toy.A as "A" in' not in defs
    level1 = (out / "Game/Levels/AToyExample/L01_lemma1.lean").read_text()
    assert 'TheoremDoc Toy.lemma1 as "lemma1" in "A toy example"' in level1


def _write_rejection_project(project: Path, lean_source: str) -> None:
    (project / "blueprint" / "src").mkdir(parents=True)
    (project / "blueprint" / "src" / "content.tex").write_text(
        "\\chapter{C}\n"
        "\\begin{definition}\\label{def:A}\\lean{Toy.A}\n"
        "  A.\n"
        "\\end{definition}\n"
        "\\begin{lemma}\\label{lem:t}\\lean{Toy.t}\\leanok\n"
        "  T. \\uses{def:A}\n"
        "\\end{lemma}\n",
        encoding="utf-8",
    )
    (project / "Basic.lean").write_text(lean_source, encoding="utf-8")
    (project / "lean-toolchain").write_text(
        "leanprover/lean4:v4.31.0\n", encoding="utf-8"
    )


def test_generate_rejects_project_local_syntax_without_writing(tmp_path, capsys):
    """A copied def relying on project-local notation cannot be reproduced
    in self-contained Defs.lean: `generate` must fail with an actionable
    diagnostic and write no game files (issue #17)."""
    project = tmp_path / "proj"
    _write_rejection_project(
        project,
        'local notation "η" => Nat\n\n'
        "namespace Toy\n\n"
        "def A : η :=\n  1\n\n"
        "theorem t : A = A := by\n  rfl\n\n"
        "end Toy\n",
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 1
    assert not out.exists() or not any(out.rglob("*"))
    err = capsys.readouterr().err
    assert "Toy.A" in err
    assert "notation" in err


def test_generate_rejects_project_open_without_writing(tmp_path, capsys):
    """`open Ks` of a project-local namespace cannot be reproduced
    self-contained in the generated files: reject before writing."""
    project = tmp_path / "proj"
    _write_rejection_project(
        project,
        "open Ks\n\n"
        "namespace Toy\n\n"
        "def A : Nat :=\n  k + 1\n\n"
        "theorem t : A = A := by\n  rfl\n\n"
        "end Toy\n",
    )
    (project / "Ks.lean").write_text(
        "namespace Ks\n\ndef k : Nat := 1\n\nend Ks\n", encoding="utf-8"
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 1
    assert not out.exists() or not any(out.rglob("*"))
    err = capsys.readouterr().err
    assert "Toy.A" in err
    assert "Ks" in err


def test_deterministic_output(generated, tmp_path):
    again = tmp_path / "game2"
    assert main(["generate", str(PROJECT), "-o", str(again), "--title", "Toy Game"]) == 0
    comparison = filecmp.dircmp(generated, again)

    def assert_equal(cmp):
        assert not cmp.diff_files, cmp.diff_files
        assert not cmp.left_only and not cmp.right_only
        for sub in cmp.subdirs.values():
            assert_equal(sub)

    assert_equal(comparison)
