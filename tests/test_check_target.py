"""Tests for the ``check`` command's flexible input resolution."""

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


def test_generate_still_requires_content_tex(tmp_path, capsys):
    """`generate` keeps its project-root + src/content.tex interface."""
    project = make_project(tmp_path, entry="src/web.tex")
    assert main(["generate", str(project), "-o", str(tmp_path / "game")]) == 1
    assert "not found" in capsys.readouterr().err
