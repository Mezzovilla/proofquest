"""End-to-end test: generate the game for the toy_example project."""

import filecmp
import re
import shutil
import subprocess
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
    assert "Statement lemma1 (n : Nat) : _root_.Toy.A n := by" in level1
    assert "namespace Toy" in level1
    assert "NewDefinition Toy.A" in level1
    assert "NewTactic unfold omega" in level1

    level2 = (generated / "Game/Levels/AToyExample/L02_lemma2.lean").read_text()
    assert "Statement lemma2 (n : Nat) : _root_.Toy.A (n + 1) := by" in level2

    level3 = (generated / "Game/Levels/AToyExample/L03_lemma3.lean").read_text()
    assert "import Game.Levels.AToyExample.L02_lemma2" in level3
    assert (
        "Statement lemma3 (n : Nat) : _root_.Toy.A n ∧ _root_.Toy.B (n + 1) := by"
        in level3
    )
    assert "have h := _root_.Toy.lemma2 (n + 1)" in level3  # sample solution embedded
    assert "constructor" in level3
    assert "exact h" in level3
    assert 'Hint "Just use lemma2."' in level3  # LaTeX proof became a hint
    assert "NewTactic «have» constructor exact" in level3  # keyword tactics are quoted
    # `lemma2` is a project-local theorem (its own level); it must not be
    # re-declared with `NewTheorem`, since the GameServer unlocks it
    # automatically once its level is solved.
    assert "NewTheorem" not in level3

    main_level = (generated / "Game/Levels/AToyExample/L04_main.lean").read_text()
    assert "import Game.Levels.AToyExample.L03_lemma3" in main_level
    assert (
        "Statement main (n : Nat) : _root_.Toy.A n ∧ _root_.Toy.B (n + 1) := by"
        in main_level
    )
    assert "exact _root_.Toy.lemma1 n" in main_level
    assert "exact (_root_.Toy.lemma3 n).2" in main_level
    assert 'Hint "Easy from lemma1 and lemma3."' in main_level
    assert "NewTheorem" not in main_level


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
        'local notation "η" x => Nat\n\n'
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
    """A selective `open Ks (k)` of a project-local namespace cannot be
    reproduced self-contained in the generated files: reject before
    writing. (Plain `open Ks` is supported: it is replayed verbatim with a
    namespace scaffold.)"""
    project = tmp_path / "proj"
    _write_rejection_project(
        project,
        "open Ks (k)\n\n"
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
    assert "open" in err
    assert "Basic.lean:1" in err


def test_generate_replays_project_open_with_scaffold(tmp_path):
    """A plain `open Ks` of a project-local namespace is replayed verbatim
    inside the declaration's section, preceded by an empty namespace
    scaffold when the opened namespace has no copied declarations."""
    project = tmp_path / "proj"
    _write_rejection_project(
        project,
        "import Ks\n"
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

    assert main(["generate", str(project), "-o", str(out)]) == 0

    defs = (out / "Game" / "Generated" / "Defs.lean").read_text()
    assert "open Ks" in defs
    assert "namespace Ks\n" in defs
    assert "def k : Nat := 1" in defs


def test_generate_replays_plain_global_notation_locally(tmp_path):
    project = tmp_path / "proj"
    _write_rejection_project(
        project,
        "import Mathlib.Topology.Basic\n\n"
        "namespace Toy\n\n"
        "abbrev A : Nat :=\n  1\n\n"
        "abbrev NormMap (T : Type*) := T\n\n"
        'notation "‖" T "·‖" => NormMap T\n\n'
        "theorem t (T : Type*) (x : ‖T·‖) : ‖T ·‖ := by\n"
        "  exact x\n\n"
        "end Toy\n",
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 0

    defs = (out / "Game" / "Generated" / "Defs.lean").read_text()
    assert "import Mathlib.Topology.Basic" in defs
    assert "abbrev NormMap (T : Type*) := T" in defs
    assert "local notation" not in defs
    level = (out / "Game" / "Levels" / "C" / "L01_t.lean").read_text()
    assert "local notation \"‖\" T \"·‖\" => _root_.Toy.NormMap T" in level
    assert "Statement t (T : Type*) (x : ‖T·‖) : ‖T ·‖ := by" in level
    assert "NewDefinition Toy.NormMap Toy.A" in level
    assert (out / "Game" / "Generated" / "TacticDocs.lean").read_text().startswith(
        "import Game.Generated.Defs\n"
    )
    assert (out / "Game" / "Generated" / "TheoremDocs.lean").read_text().startswith(
        "import Game.Generated.Defs\n"
    )


def test_generate_rejects_ambiguous_imported_notation_before_writing(tmp_path, capsys):
    project = tmp_path / "proj"
    _write_rejection_project(
        project,
        "import N1\nimport N2\n\n"
        "namespace Toy\n\n"
        "abbrev A : Nat :=\n  1\n\n"
        "theorem t : True := by\n  trivial\n\n"
        "end Toy\n",
    )
    (project / "N1.lean").write_text(
        "namespace One\nabbrev F (T : Type*) := T\n"
        'notation "X" T => F T\nend One\n',
        encoding="utf-8",
    )
    (project / "N2.lean").write_text(
        "namespace Two\nabbrev G (T : Type*) := T\n"
        'notation "X" X => G X\nend Two\n',
        encoding="utf-8",
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 1
    assert not out.exists() or not any(out.rglob("*"))
    assert "notation" in capsys.readouterr().err


def test_generate_rejects_notation_continuation_before_writing(tmp_path, capsys):
    project = tmp_path / "proj"
    _write_rejection_project(
        project,
        "namespace Toy\n\n"
        "abbrev A : Nat :=\n  1\n\n"
        "abbrev F (T : Type*) := T\n\n"
        'notation "X" T => F T\n'
        "  T\n\n"
        "theorem t : True := by\n  trivial\n\n"
        "end Toy\n",
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 1
    assert not out.exists() or not any(out.rglob("*"))
    assert "notation" in capsys.readouterr().err


def test_generate_root_qualified_notation_uses_root_target(tmp_path):
    project = tmp_path / "proj"
    _write_rejection_project(
        project,
        "abbrev TopA (T : Type*) := T\n\n"
        "namespace Toy\n\n"
        "abbrev A : Nat :=\n  1\n\n"
        "abbrev TopA : Nat :=\n  0\n\n"
        'notation "R" T => _root_.TopA T\n\n'
        "theorem t (T : Type*) (x : R T) : True := by\n"
        "  trivial\n\n"
        "end Toy\n",
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 0
    defs = (out / "Game" / "Generated" / "Defs.lean").read_text()
    assert "abbrev TopA (T : Type*) := T" in defs
    assert "abbrev TopA : Nat :=\n  0" not in defs
    level = (out / "Game" / "Levels" / "C" / "L01_t.lean").read_text()
    assert 'local notation "R" T => _root_.TopA T' in level
    assert "_root_.Toy.TopA" not in level


def test_generate_stages_notation_target_using_playable_theorem(tmp_path):
    """A notation target chain that mentions a level theorem can no more
    live in the preamble than the theorem itself: the copied abbreviations
    are staged into a ``DefsAfter`` module emitted after that level."""
    project = tmp_path / "proj"
    (project / "blueprint" / "src").mkdir(parents=True)
    (project / "blueprint" / "src" / "content.tex").write_text(
        "\\chapter{C}\n"
        "\\begin{lemma}\\label{lem:t}\\lean{Toy.t}\\leanok\n"
        "  T. \\end{lemma}\n"
        "\\begin{lemma}\\label{lem:u}\\lean{Toy.u}\\leanok\n"
        "  U. \\uses{lem:t}\n"
        "\\end{lemma}\n",
        encoding="utf-8",
    )
    (project / "Basic.lean").write_text(
        "namespace Toy\n\n"
        "theorem t : True := by\n  trivial\n\n"
        "abbrev G : True :=\n  t\n\n"
        "abbrev F : True :=\n  G\n\n"
        'notation "X" => F\n\n'
        "theorem u : X := by\n  trivial\n\n"
        "end Toy\n",
        encoding="utf-8",
    )
    (project / "lean-toolchain").write_text(
        "leanprover/lean4:v4.31.0\n", encoding="utf-8"
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 0

    defs = (out / "Game/Generated/Defs.lean").read_text()
    assert "abbrev G" not in defs and "abbrev F" not in defs
    stage = (out / "Game/Generated/DefsAfter001.lean").read_text()
    assert "import Game.Levels.C.L01_t" in stage
    assert "abbrev G : True :=\n  _root_.Toy.t" in stage
    assert "abbrev F : True :=\n  _root_.Toy.G" in stage
    level = (out / "Game/Levels/C/L02_u.lean").read_text()
    assert "import Game.Generated.DefsAfter001" in level
    assert 'local notation "X" => _root_.Toy.F' in level
    assert "NewDefinition Toy.G Toy.F" in level or (
        "NewDefinition Toy.F Toy.G" in level
    )


def test_generate_threads_theorem_only_external_imports(tmp_path):
    project = tmp_path / "proj"
    _write_rejection_project(
        project,
        "namespace Toy\n\n"
        "abbrev A : Nat :=\n  1\n\n"
        "end Toy\n",
    )
    (project / "Ext.lean").write_text(
        "import Mathlib.Topology.Basic\n", encoding="utf-8"
    )
    (project / "Use.lean").write_text(
        "import Ext\n\n"
        "namespace Toy\n\n"
        "theorem t : True := by\n  trivial\n\n"
        "end Toy\n",
        encoding="utf-8",
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 0
    defs = (out / "Game" / "Generated" / "Defs.lean").read_text()
    assert "import Mathlib.Topology.Basic" in defs
    assert "import Ext" not in defs
    assert "import Use" not in defs


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


def _write_scoped_context_project(project: Path, base_body: str | None = None) -> None:
    (project / "blueprint" / "src").mkdir(parents=True)
    (project / "blueprint" / "src" / "content.tex").write_text(
        "\\chapter{C}\n"
        "\\begin{definition}\\label{def:d}\\lean{Toy.d}\n  D.\n\\end{definition}\n"
        "\\begin{definition}\\label{def:pick}\\lean{Toy.pick}\n  P.\n\\end{definition}\n"
        "\\begin{definition}\\label{def:pickL}\\lean{Toy.pickL}\n  L.\n\\end{definition}\n"
        "\\begin{definition}\\label{def:c}\\lean{Toy.c}\n  C.\n\\end{definition}\n"
        "\\begin{definition}\\label{def:aliasUse}\\lean{Toy.aliasUse}\n  A.\n\\end{definition}\n"
        "\\begin{lemma}\\label{lem:t}\\lean{Toy.t}\\leanok\n"
        "  T. \\uses{def:d,def:pick,def:pickL}\n\\end{lemma}\n"
        "\\begin{lemma}\\label{lem:t2}\\lean{Toy.t2}\\leanok\n  T2.\n\\end{lemma}\n"
        "\\begin{lemma}\\label{lem:tc}\\lean{Toy.tc}\\leanok\n"
        "  TC. \\uses{def:c}\n\\end{lemma}\n"
        "\\begin{lemma}\\label{lem:t3}\\lean{Toy.t3}\\leanok\n"
        "  T3. \\uses{def:aliasUse}\n\\end{lemma}\n",
        encoding="utf-8",
    )
    (project / "Base.lean").write_text(
        "import Mathlib.Tactic\n\n"
        "class Tagged (α : Type) where\n"
        "  tag : α\n\n"
        "namespace Bs\n"
        "instance : Tagged Nat := ⟨1⟩\n"
        "end Bs\n\n"
        "local instance : Tagged Bool := ⟨true⟩\n\n"
        "namespace Ctx\n"
        "def double (n : Nat) : Nat := n + n\n"
        'notation "!!" x => double x\n'
        "end Ctx\n"
        + (base_body or ""),
        encoding="utf-8",
    )
    (project / "Middle.lean").write_text(
        "import Base\n\n"
        "namespace Mid\n"
        "instance (α : Type) [Tagged α] : Tagged (List α) := ⟨[]⟩\n"
        "end Mid\n",
        encoding="utf-8",
    )
    (project / "Use.lean").write_text(
        "import Middle\n\n"
        "namespace Toy\n\n"
        "def d : Nat := !! 3\n\n"
        "def pick : Nat := (inferInstance : Tagged Nat).tag\n\n"
        "def pickL : List Nat := (inferInstance : Tagged (List Nat)).tag\n\n"
        "section\n"
        "local instance : Tagged Char := ⟨'c'⟩\n\n"
        "def c : Char := (inferInstance : Tagged Char).tag\n\n"
        "theorem tc : (inferInstance : Tagged Char).tag = 'c' := rfl\n"
        "end\n\n"
        'local notation "##" x => Ctx.double x\n\n'
        "def aliasUse : Nat := ## 5\n\n"
        "theorem t : pick = 1 ∧ d = 6 := by\n"
        "  exact ⟨rfl, rfl⟩\n\n"
        "theorem t2 : (inferInstance : Tagged Nat).tag = 1 := rfl\n\n"
        "theorem t3 : pick + pick = ## (1) := by\n"
        "  change pick + pick = ## (1)\n"
        "  rfl\n\n"
        "end Toy\n",
        encoding="utf-8",
    )
    (project / "lean-toolchain").write_text(
        "leanprover/lean4:v4.31.0\n", encoding="utf-8"
    )


def test_generate_transports_instances_and_notation(tmp_path):
    project = tmp_path / "proj"
    _write_scoped_context_project(project)
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 0

    defs = (out / "Game" / "Generated" / "Defs.lean").read_text()
    assert "import Base" not in defs and "import Middle" not in defs
    assert re.search(r"^(local |scoped )?instance ", defs, re.MULTILINE) is None
    bs_def = re.search(
        r"namespace Bs\n\ndef (_instance_m[0-9a-f]+_l\d+) : _root_.Tagged Nat := ⟨1⟩",
        defs,
    )
    assert bs_def, defs
    mid_def = re.search(
        r"def (_instance_m[0-9a-f]+_l\d+) "
        r"\(α : Type\) \[_root_.Tagged α\] : _root_.Tagged \(List α\) := ⟨\[\]⟩",
        defs,
    )
    assert mid_def, defs
    assert "namespace Mid\n" in defs
    bool_def = re.search(
        r"def (_instance_m[0-9a-f]+_l\d+) : _root_.Tagged Bool := ⟨true⟩", defs
    )
    assert bool_def, defs
    char_def = re.search(
        r"def (_instance_m[0-9a-f]+_l\d+) : _root_.Tagged Char := ⟨'c'⟩", defs
    )
    assert char_def, defs
    assert (
        "namespace Ctx\n\n"
        f"attribute [local instance] _root_.Bs.{bs_def.group(1)}\n"
        f"attribute [local instance] _root_.{bool_def.group(1)}\n\n"
        "def double" in defs
    )
    assert (
        "namespace Toy\n\n"
        f"attribute [local instance] _root_.Bs.{bs_def.group(1)}\n"
        'local notation "!!" x => _root_.Ctx.double x\n'
        f"attribute [local instance] _root_.Mid.{mid_def.group(1)}" in defs
    )
    assert "def pick : Nat := (inferInstance : _root_.Tagged Nat).tag" in defs
    assert 'local notation "##" x => _root_.Ctx.double x' in defs
    assert "def aliasUse : Nat := ## 5" in defs
    assert "def c : Char := (inferInstance : _root_.Tagged Char).tag" in defs
    assert (
        f"attribute [local instance] _root_.Toy.{char_def.group(1)}" in defs
    )
    assert "open scoped" not in defs
    assert "section\n" in defs

    if shutil.which("lean") is not None:
        probe = tmp_path / "Emitted.lean"
        probe.write_text(
            "class C (α : Type) where\n"
            "  val : α\n"
            "namespace Ns\n"
            "def inst : C Nat := ⟨1⟩\n"
            "end Ns\n"
            "section\n"
            "attribute [local instance] _root_.Ns.inst\n"
            "def use : Nat := (inferInstance : C Nat).val\n"
            "end\n"
            "def laterRef : Nat := Ns.inst.val\n",
            encoding="utf-8",
        )
        ok = subprocess.run(
            ["lean", str(probe)], capture_output=True, text=True, timeout=120, check=False
        )
        assert ok.returncode == 0, ok.stderr
        probe.write_text(probe.read_text() + "def leak : Nat := (inferInstance : C Nat).val\n")
        bad = subprocess.run(
            ["lean", str(probe)], capture_output=True, text=True, timeout=120, check=False
        )
        assert bad.returncode != 0
        assert "synthesize" in bad.stderr + bad.stdout
        probe.write_text(
            "class C (α : Type) where\n"
            "  val : α\n"
            "def early : Nat := (inferInstance : C Nat).val\n"
            "def inst : C Nat := ⟨1⟩\n",
            encoding="utf-8",
        )
        early = subprocess.run(
            ["lean", str(probe)], capture_output=True, text=True, timeout=120, check=False
        )
        assert early.returncode != 0

    level = (out / "Game" / "Levels" / "C" / "L02_t2.lean").read_text()
    assert "open scoped" not in level
    assert f"attribute [local instance] _root_.Bs.{bs_def.group(1)}" in level
    assert (
        "Statement t2 : (inferInstance : _root_.Tagged Nat).tag = 1 := by"
        in level
    )

    level_tc = (out / "Game" / "Levels" / "C" / "L03_tc.lean").read_text()
    assert f"attribute [local instance] _root_.Toy.{char_def.group(1)}" in level_tc
    assert (
        "Statement tc : (inferInstance : _root_.Tagged Char).tag = 'c' := by"
        in level_tc
    )

    level_t3 = (out / "Game" / "Levels" / "C" / "L04_t3.lean").read_text()
    assert 'local notation "##" x => _root_.Ctx.double x' in level_t3
    assert (
        "Statement t3 : _root_.Toy.pick + _root_.Toy.pick = ## (1) := by"
        in level_t3
    )
    assert "change _root_.Toy.pick + _root_.Toy.pick = ## (1)" in level_t3


def test_generate_rejects_unsupported_instance_context(tmp_path, capsys):
    project = tmp_path / "proj"
    _write_scoped_context_project(
        project,
        base_body="\nprotected instance viaWhere : Tagged Int where\n",
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 1
    assert not out.exists() or not any(out.rglob("*"))
    err = capsys.readouterr().err
    assert "instance" in err
    assert "Base.lean:" in err


def test_generate_transports_where_instance(tmp_path):
    project = tmp_path / "proj"
    _write_scoped_context_project(
        project,
        base_body="\ninstance viaWhere : Tagged Int where\n  tag := 3\n",
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 0

    defs = (out / "Game" / "Generated" / "Defs.lean").read_text()
    assert "def viaWhere : _root_.Tagged Int := {\n  tag := 3\n}" in defs
    assert "attribute [local instance] _root_.viaWhere" in defs


def _write_command_local_project(project: Path, lean_decls: str, lean_names: str) -> None:
    (project / "blueprint" / "src").mkdir(parents=True)
    (project / "blueprint" / "src" / "content.tex").write_text(
        "\\chapter{C}\n" + lean_names, encoding="utf-8"
    )
    (project / "Basic.lean").write_text(lean_decls, encoding="utf-8")
    (project / "lean-toolchain").write_text(
        "leanprover/lean4:v4.31.0\n", encoding="utf-8"
    )


def test_generate_rejects_command_local_open_target(tmp_path, capsys):
    project = tmp_path / "proj"
    _write_command_local_project(
        project,
        "namespace Toy\n\n"
        "open Toy (A) in\n"
        "def A : Nat := succ 0\n\n"
        "theorem t : A = A := by\n  rfl\n\n"
        "end Toy\n",
        "\\begin{definition}\\label{def:A}\\lean{Toy.A}\n  A.\n\\end{definition}\n"
        "\\begin{lemma}\\label{lem:t}\\lean{Toy.t}\\leanok\n"
        "  T. \\uses{def:A}\n\\end{lemma}\n",
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 1
    assert not out.exists() or not any(out.rglob("*"))
    err = capsys.readouterr().err
    assert "Toy.A" in err
    assert "open" in err
    assert "Basic.lean:3" in err


def test_generate_replays_command_local_open_on_target(tmp_path):
    """`open Nat in` before a declaration replays as a section-local
    `open Nat` on that declaration only."""
    project = tmp_path / "proj"
    _write_command_local_project(
        project,
        "namespace Toy\n\n"
        "open Nat in\n"
        "def A : Nat := succ 0\n\n"
        "theorem t : A = A := by\n  rfl\n\n"
        "end Toy\n",
        "\\begin{definition}\\label{def:A}\\lean{Toy.A}\n  A.\n\\end{definition}\n"
        "\\begin{lemma}\\label{lem:t}\\lean{Toy.t}\\leanok\n"
        "  T. \\uses{def:A}\n\\end{lemma}\n",
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 0

    defs = (out / "Game" / "Generated" / "Defs.lean").read_text()
    assert "open Nat" in defs
    assert "open Nat in" not in defs
    assert "def A : Nat := succ 0" in defs


def test_generate_command_local_open_leaves_following_decl_clean(tmp_path):
    project = tmp_path / "proj"
    _write_command_local_project(
        project,
        "namespace Toy\n\n"
        "open Nat in\n"
        "theorem target : Nat.succ 0 = 1 := rfl\n\n"
        "theorem follow : Nat.succ 0 = 1 := by\n  rfl\n\n"
        "end Toy\n",
        "\\begin{lemma}\\label{lem:f}\\lean{Toy.follow}\\leanok\n  F.\n\\end{lemma}\n",
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 0

    defs = (out / "Game" / "Generated" / "Defs.lean").read_text()
    level = (out / "Game" / "Levels" / "C" / "L01_follow.lean").read_text()
    for text in (defs, level):
        assert "open Nat in" not in text
        assert "open\n" not in text
    assert "Statement follow : Nat.succ 0 = 1 := by" in level


def test_generate_rejects_same_line_command_local_open_without_leaking(
    tmp_path, capsys
):
    project = tmp_path / "proj"
    _write_command_local_project(
        project,
        "namespace Toy\n\n"
        "open Nat in theorem target : Nat.succ 0 = 1 := rfl\n\n"
        "theorem follow : Nat.succ 0 = 1 := by\n  rfl\n\n"
        "end Toy\n",
        "\\begin{lemma}\\label{lem:t}\\lean{Toy.target}\\leanok\n"
        "  T.\n\\end{lemma}\n"
        "\\begin{lemma}\\label{lem:f}\\lean{Toy.follow}\\leanok\n"
        "  F.\n\\end{lemma}\n",
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 1
    assert not out.exists() or not any(out.rglob("*"))
    err = capsys.readouterr().err
    assert "Toy.target" in err
    assert "not found in the Lean sources" in err


def test_generate_rejects_command_local_variable_target(tmp_path, capsys):
    project = tmp_path / "proj"
    _write_command_local_project(
        project,
        "namespace Toy\n\n"
        "variable (n : Nat) in\n"
        "def A : Nat := succ 0\n\n"
        "theorem t : A = A := by\n  rfl\n\n"
        "end Toy\n",
        "\\begin{definition}\\label{def:A}\\lean{Toy.A}\n  A.\n\\end{definition}\n"
        "\\begin{lemma}\\label{lem:t}\\lean{Toy.t}\\leanok\n"
        "  T. \\uses{def:A}\n\\end{lemma}\n",
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 1
    assert not out.exists() or not any(out.rglob("*"))
    err = capsys.readouterr().err
    assert "Toy.A" in err
    assert "variable" in err
    assert "Basic.lean:3" in err


def test_generate_rejects_mixed_def_level_cycle_before_writing(tmp_path, capsys):
    """A definition depending on a target theorem while the target's
    signature needs that definition is a real mixed cycle: `generate`
    fails with the declaration, file:line origins and the full chain,
    and writes nothing."""
    project = tmp_path / "proj"
    (project / "blueprint" / "src").mkdir(parents=True)
    (project / "blueprint" / "src" / "content.tex").write_text(
        "\\chapter{C}\n"
        "\\begin{lemma}\\label{lem:t2}\\lean{Toy.t2}\\leanok\n"
        "  T2.\n"
        "\\end{lemma}\n"
        "\\begin{definition}\\label{def:B}\\lean{Toy.B}\n"
        "  B.\n"
        "\\end{definition}\n",
        encoding="utf-8",
    )
    (project / "Basic.lean").write_text(
        "namespace Toy\n\n"
        "def B : Nat :=\n  if t2 then 1 else 2\n\n"
        "theorem t2 : B = B := by\n  rfl\n\n"
        "end Toy\n",
        encoding="utf-8",
    )
    (project / "lean-toolchain").write_text(
        "leanprover/lean4:v4.31.0\n", encoding="utf-8"
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 1
    assert not out.exists() or not any(out.rglob("*"))
    err = capsys.readouterr().err
    assert "cycle" in err
    assert "Toy.B" in err and "Toy.t2" in err
    assert "Basic.lean:" in err
    assert "->" in err


def test_generate_rejects_impossible_world_layout_before_writing(
    tmp_path, capsys
):
    """Chapter A target -> chapter B target -> chapter A target (through a
    dependent definition) cannot be laid out in grouped worlds: `generate`
    fails with the world cycle and witness chain, and writes nothing."""
    project = tmp_path / "proj"
    (project / "blueprint" / "src").mkdir(parents=True)
    (project / "blueprint" / "src" / "content.tex").write_text(
        "\\chapter{A}\n"
        "\\begin{lemma}\\label{lem:a1}\\lean{Toy.a1}\\leanok\n"
        "  A1.\n"
        "\\end{lemma}\n"
        "\\chapter{B}\n"
        "\\begin{lemma}\\label{lem:b1}\\lean{Toy.b1}\\leanok\n"
        "  B1.\n"
        "\\end{lemma}\n"
        "\\begin{definition}\\label{def:dv}\\lean{Toy.dv}\n"
        "  D.\n"
        "\\end{definition}\n"
        "\\chapter{A}\n"
        "\\begin{lemma}\\label{lem:a2}\\lean{Toy.a2}\\leanok\n"
        "  A2. \\uses{def:dv}\n"
        "\\end{lemma}\n",
        encoding="utf-8",
    )
    (project / "Basic.lean").write_text(
        "namespace Toy\n\n"
        "theorem a1 : True := by\n  trivial\n\n"
        "theorem b1 : True := by\n  exact a1\n\n"
        "def dv : True :=\n  b1\n\n"
        "theorem a2 : dv = dv := by\n  rfl\n\n"
        "end Toy\n",
        encoding="utf-8",
    )
    (project / "lean-toolchain").write_text(
        "leanprover/lean4:v4.31.0\n", encoding="utf-8"
    )
    out = tmp_path / "game"

    assert main(["generate", str(project), "-o", str(out)]) == 1
    assert not out.exists() or not any(out.rglob("*"))
    err = capsys.readouterr().err
    assert "world" in err
    assert "Basic.lean:" in err
    assert "Toy.dv" in err or "Toy.b1" in err


def test_generate_renders_root_qualified_decl_in_source_namespace(tmp_path):
    """`_root_.Inner.uses` declared inside `namespace Outer` keeps its
    source context (Outer.resolution, relative opens) and its root header.
    The level's Statement is emitted at root under the real full name —
    `namespace Outer` + `Statement _root_.Inner.t` would make the
    GameServer record a bogus `Outer._root_.Inner.t` statement name."""
    project = tmp_path / "proj"
    (project / "blueprint" / "src").mkdir(parents=True)
    (project / "blueprint" / "src" / "content.tex").write_text(
        "\\chapter{C}\n"
        "\\begin{definition}\\label{def:uses}\\lean{Inner.uses}\n"
        "  U.\n"
        "\\end{definition}\n"
        "\\begin{lemma}\\label{lem:t}\\lean{Inner.t}\\leanok\n"
        "  T. \\uses{def:uses}\n"
        "\\end{lemma}\n",
        encoding="utf-8",
    )
    (project / "Basic.lean").write_text(
        "namespace Outer\n"
        "def dep : Nat := 1\n"
        "def _root_.Inner.uses : Nat := dep + 1\n"
        "theorem _root_.Inner.t : Inner.uses = Inner.uses := by\n  rfl\n"
        "end Outer\n",
        encoding="utf-8",
    )
    (project / "lean-toolchain").write_text("leanprover/lean4:v4.31.0\n")
    out = tmp_path / "game"
    assert main(["generate", str(project), "-o", str(out)]) == 0
    defs = (out / "Game/Generated/Defs.lean").read_text()
    assert "namespace Outer" in defs
    assert "def dep : Nat := 1" in defs
    assert "def _root_.Inner.uses : Nat := _root_.Outer.dep + 1" in defs
    level = (out / "Game/Levels/C/L01_t.lean").read_text()
    assert "namespace Outer" not in level
    assert "open Outer" in level
    assert "Statement Inner.t" in level
    assert "_root_.Inner.uses = _root_.Inner.uses" in level


def test_generate_split_definition_group_breaks_member_cycle(tmp_path):
    """FLT3 grouping: members defined *from* level theorems live in their
    own blueprint node so the def <-> level edge no longer cycles."""
    project = tmp_path / "proj"
    (project / "blueprint" / "src").mkdir(parents=True)
    (project / "blueprint" / "src" / "content.tex").write_text(
        "\\chapter{C}\n"
        "\\begin{definition}\\label{def:yzw}\\lean{Toy.y, Toy.z, Toy.w}\n"
        "  YZW.\n"
        "\\end{definition}\n"
        "\\begin{lemma}\\label{lmm:l}\\lean{Toy.l}\\leanok\n"
        "  L. \\uses{def:yzw}\n"
        "\\end{lemma}\n"
        "\\begin{definition}\\label{def:x}\\lean{Toy.x}\n"
        "  X. \\uses{lmm:l}\n"
        "\\end{definition}\n"
        "\\begin{lemma}\\label{lem:t}\\lean{Toy.t}\\leanok\n"
        "  T. \\uses{def:x}\n"
        "\\end{lemma}\n",
        encoding="utf-8",
    )
    (project / "Basic.lean").write_text(
        "namespace Toy\n"
        "def y : Nat := 1\n"
        "def z : Nat := 2\n"
        "def w : Nat := 3\n"
        "theorem l (n : Nat) : y = y := by\n  rfl\n"
        "def x : Nat := by\n  have _ := l y\n  exact 1\n"
        "theorem t : x = x := by\n  rfl\n"
        "end Toy\n",
        encoding="utf-8",
    )
    (project / "lean-toolchain").write_text("leanprover/lean4:v4.31.0\n")
    out = tmp_path / "game"
    assert main(["generate", str(project), "-o", str(out)]) == 0
    defs = (out / "Game/Generated/Defs.lean").read_text()
    staged = (out / "Game/Generated/DefsAfter001.lean").read_text()
    assert "def y" in defs
    assert "def z" in defs
    assert "def w" in defs
    assert "def x" in staged
    assert "import Game.Levels.C.L01_l" in staged
