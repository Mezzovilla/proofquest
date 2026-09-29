"""Tests for the ``check``/``generate`` commands' shared input resolution."""

from pathlib import Path

from proofquest.cli import main

CONTENT = r"""
\chapter{A toy example}

\begin{lemma}\label{lem:foo}\lean{foo}\leanok
  Foo holds.
\end{lemma}
"""


def make_project(tmp_path: Path, entry: str = "src/content.tex") -> Path:
    """Create a minimal Lean project whose blueprint entry point is `entry`."""
    project = tmp_path / "proj"
    (project / "blueprint" / "src").mkdir(parents=True)
    (project / "blueprint" / entry).write_text(CONTENT, encoding="utf-8")
    (project / "Basic.lean").write_text(
        "theorem foo : True :=\n  trivial\n", encoding="utf-8"
    )
    return project


def test_check_warns_on_definition_without_lean(tmp_path, capsys):
    """A definition with no \\lean{} warns (like a theorem), exit stays 0."""
    project = make_project(tmp_path)
    src = project / "blueprint" / "src"
    (src / "content.tex").write_text(
        CONTENT
        + "\\begin{definition}\\label{def:missing}\\leanok\n"
        "  A definition with a commented-out \\lean.\n\\end{definition}\n",
        encoding="utf-8",
    )
    assert main(["check", str(project)]) == 0
    err = capsys.readouterr().err
    assert "def:missing" in err
    assert "definition has no \\lean{} declaration" in err


def test_generate_fails_on_definition_without_lean(tmp_path, capsys):
    """The same project must fail `generate` with an actionable error."""
    project = make_project(tmp_path)
    src = project / "blueprint" / "src"
    (src / "content.tex").write_text(
        CONTENT
        + "\\begin{definition}\\label{def:missing}\\leanok\n"
        "  A definition with a commented-out \\lean.\n\\end{definition}\n",
        encoding="utf-8",
    )
    assert main(["generate", str(project), "-o", str(tmp_path / "game")]) == 1
    err = capsys.readouterr().err
    assert "def:missing" in err
    assert "no matching Lean declaration" in err


def test_check_project_root_content_tex(tmp_path):
    project = make_project(tmp_path)
    assert main(["check", str(project)]) == 0


def test_check_blueprint_directory(tmp_path):
    project = make_project(tmp_path)
    assert main(["check", str(project / "blueprint")]) == 0


def test_check_explicit_tex_entry_point(tmp_path):
    project = make_project(tmp_path, entry="src/print.tex")
    assert main(["check", str(project / "blueprint" / "src" / "print.tex")]) == 0


def test_check_explicit_tex_follows_input_chain(tmp_path):
    project = make_project(tmp_path, entry="src/print.tex")
    src = project / "blueprint" / "src"
    (src / "print.tex").write_text(
        "\\chapter{A toy example}\n\\input{main}\n", encoding="utf-8"
    )
    (src / "main.tex").write_text(
        "\\begin{lemma}\\label{lem:foo}\\lean{foo}\\leanok\n  Foo holds.\n"
        "\\end{lemma}\n",
        encoding="utf-8",
    )
    assert main(["check", str(src / "print.tex")]) == 0


def test_check_flt3_layout_prefers_web(tmp_path, capsys):
    """web.tex + print.tex (both input-ing main.tex, no content.tex): web wins."""
    project = make_project(tmp_path, entry="src/web.tex")
    src = project / "blueprint" / "src"
    (src / "web.tex").write_text(
        "\\chapter{A toy example}\n"
        "\\begin{lemma}\\label{lem:web}\\lean{foo}\\leanok\n  Web only.\n"
        "\\end{lemma}\n"
        "\\input{main}\n",
        encoding="utf-8",
    )
    (src / "print.tex").write_text("\\input{main}\n", encoding="utf-8")
    (src / "main.tex").write_text(
        "\\begin{lemma}\\label{lem:foo}\\lean{foo}\\leanok\n  Foo holds.\n"
        "\\end{lemma}\n",
        encoding="utf-8",
    )
    assert main(["check", str(project)]) == 0
    out = capsys.readouterr().out
    assert "lem:web" in out
    assert "lem:foo" in out


def test_check_missing_entry_point_is_actionable(tmp_path, capsys):
    project = make_project(tmp_path)
    (project / "blueprint" / "src" / "content.tex").unlink()
    assert main(["check", str(project)]) == 1
    err = capsys.readouterr().err
    assert "no blueprint entry point" in err
    assert "explicitly" in err


def test_check_ambiguous_same_name_candidates(tmp_path, capsys):
    project = make_project(tmp_path, entry="src/web.tex")
    (project / "blueprint" / "web.tex").write_text(CONTENT, encoding="utf-8")
    assert main(["check", str(project)]) == 1
    err = capsys.readouterr().err
    assert "ambiguous" in err
    assert "explicitly" in err


def test_check_explicit_tex_outside_blueprint(tmp_path, capsys):
    stray = tmp_path / "stray.tex"
    stray.write_text(CONTENT, encoding="utf-8")
    assert main(["check", str(stray)]) == 1
    assert "blueprint/" in capsys.readouterr().err


def test_check_nonexistent_path(tmp_path, capsys):
    assert main(["check", str(tmp_path / "nope")]) == 1
    assert "not found" in capsys.readouterr().err


def test_check_lean_scanning_rooted_at_project(tmp_path):
    """Decls referenced via \\lean resolve from the enclosing project root."""
    project = make_project(tmp_path)
    (project / "Other.lean").write_text(
        "theorem bar : True :=\n  trivial\n", encoding="utf-8"
    )
    src = project / "blueprint" / "src"
    (src / "content.tex").write_text(
        CONTENT + "\\begin{lemma}\\label{lem:bar}\\lean{bar}\\leanok\n"
        "  Bar holds.\n\\end{lemma}\n",
        encoding="utf-8",
    )
    assert main(["check", str(src / "content.tex")]) == 0


def test_check_validation_artifacts_rooted_at_project(tmp_path, capsys):
    """blueprint/lean_decls and blueprint/web are looked up at the project."""
    project = make_project(tmp_path)
    (project / "blueprint" / "lean_decls").write_text("foo\n", encoding="utf-8")
    (project / "blueprint" / "web").mkdir()
    (project / "blueprint" / "web" / "index.html").write_text("", encoding="utf-8")
    assert main(["check", str(project / "blueprint")]) == 0
    err = capsys.readouterr().err
    assert "lean_decls not found" not in err
    assert "web not built" not in err


def make_flt3_project(tmp_path: Path) -> Path:
    """FLT3-style project: web.tex + print.tex -> main.tex -> chapters/chapter.tex."""
    project = tmp_path / "proj"
    src = project / "blueprint" / "src"
    (src / "chapters").mkdir(parents=True)
    (project / "lean-toolchain").write_text(
        "leanprover/lean4:v4.31.0\n", encoding="utf-8"
    )
    (project / "Basic.lean").write_text(
        "theorem foo : True :=\n  trivial\n"
        "theorem web_mark : True :=\n  trivial\n"
        "theorem print_mark : True :=\n  trivial\n",
        encoding="utf-8",
    )
    (src / "web.tex").write_text(
        "\\chapter{A toy example}\n"
        "\\begin{lemma}\\label{lem:web}\\lean{web_mark}\\leanok\n  Web only.\n"
        "\\end{lemma}\n"
        "\\begin{proof}\n  By trivial.\n\\end{proof}\n"
        "\\input{main}\n",
        encoding="utf-8",
    )
    (src / "print.tex").write_text(
        "\\input{main}\n"
        "\\begin{lemma}\\label{lem:print}\\lean{print_mark}\\leanok\n  Print only.\n"
        "\\end{lemma}\n"
        "\\begin{proof}\n  By trivial.\n\\end{proof}\n",
        encoding="utf-8",
    )
    (src / "main.tex").write_text("\\input{chapters/chapter}\n", encoding="utf-8")
    (src / "chapters" / "chapter.tex").write_text(
        "\\begin{lemma}\\label{lem:foo}\\lean{foo}\\leanok\n  Foo holds.\n"
        "\\end{lemma}\n"
        "\\begin{proof}\n  By trivial.\n\\end{proof}\n",
        encoding="utf-8",
    )
    (project / "blueprint" / "lean_decls").write_text("foo\n", encoding="utf-8")
    (project / "blueprint" / "web").mkdir()
    (project / "blueprint" / "web" / "index.html").write_text("", encoding="utf-8")
    return project


def _level_stems(game_dir: Path) -> set[str]:
    return {
        path.name for path in (game_dir / "Game" / "Levels").glob("*/L*_*.lean")
    }


def _assert_root_anchored_game(game_dir: Path) -> None:
    game_lean = (game_dir / "Game.lean").read_text(encoding="utf-8")
    assert 'Title "proj"' in game_lean
    toolchain = (game_dir / "lean-toolchain").read_text(encoding="utf-8").strip()
    assert toolchain == "leanprover/lean4:v4.31.0"


def test_generate_project_root_prefers_web(tmp_path):
    project = make_flt3_project(tmp_path)
    game = tmp_path / "game_root"
    assert main(["generate", str(project), "-o", str(game)]) == 0
    stems = _level_stems(game)
    assert "L01_web_mark.lean" in stems
    assert any(stem.endswith("_foo.lean") for stem in stems)
    assert not any("print_mark" in stem for stem in stems)
    _assert_root_anchored_game(game)


def test_generate_blueprint_directory(tmp_path, capsys):
    project = make_flt3_project(tmp_path)
    game = tmp_path / "game_blueprint"
    assert main(["generate", str(project / "blueprint"), "-o", str(game)]) == 0
    stems = _level_stems(game)
    assert "L01_web_mark.lean" in stems
    assert not any("print_mark" in stem for stem in stems)
    _assert_root_anchored_game(game)
    err = capsys.readouterr().err
    assert "lean_decls not found" not in err
    assert "web not built" not in err


def test_generate_explicit_print_tex(tmp_path, capsys):
    project = make_flt3_project(tmp_path)
    game = tmp_path / "game_print"
    print_tex = project / "blueprint" / "src" / "print.tex"
    assert main(["generate", str(print_tex), "-o", str(game)]) == 0
    stems = _level_stems(game)
    assert any(stem.endswith("_print_mark.lean") for stem in stems)
    assert any(stem.endswith("_foo.lean") for stem in stems)
    assert not any("web_mark" in stem for stem in stems)
    _assert_root_anchored_game(game)
    err = capsys.readouterr().err
    assert "lean_decls not found" not in err
    assert "web not built" not in err


def test_generate_missing_entry_point_is_actionable(tmp_path, capsys):
    project = make_flt3_project(tmp_path)
    src = project / "blueprint" / "src"
    (src / "web.tex").unlink()
    (src / "print.tex").unlink()
    (src / "main.tex").unlink()
    assert main(["generate", str(project), "-o", str(tmp_path / "game")]) == 1
    err = capsys.readouterr().err
    assert "no blueprint entry point" in err
    assert "explicitly" in err


def test_generate_ambiguous_directory_entry(tmp_path, capsys):
    project = make_flt3_project(tmp_path)
    (project / "blueprint" / "web.tex").write_text(CONTENT, encoding="utf-8")
    assert main(["generate", str(project), "-o", str(tmp_path / "game")]) == 1
    err = capsys.readouterr().err
    assert "ambiguous" in err
    assert "explicitly" in err


def test_generate_explicit_tex_outside_blueprint(tmp_path, capsys):
    stray = tmp_path / "stray.tex"
    stray.write_text(CONTENT, encoding="utf-8")
    assert main(["generate", str(stray), "-o", str(tmp_path / "game")]) == 1
    assert "blueprint/" in capsys.readouterr().err


def test_generate_root_content_tex_still_works(tmp_path):
    project = make_project(tmp_path)
    game = tmp_path / "game"
    assert main(["generate", str(project), "-o", str(game)]) == 0
    assert (game / "Game.lean").exists()
    assert any(stem.endswith("_foo.lean") for stem in _level_stems(game))
