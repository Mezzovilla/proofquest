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
