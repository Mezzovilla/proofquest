from pathlib import Path

import pytest

from proofquest.blueprint_parser import BlueprintError, parse_blueprint

CONTENT = r"""
\chapter{A toy example}

Intro text of the chapter.

\section{Definitions}

\begin{definition}[Property $A$]\label{def:A}\lean{Toy.A}
  For every $n$, $A(n)$ states that $n + 1 \le n + 2$.
\end{definition}

\section{Lemmas}

\begin{lemma}[Property $A$ holds]\label{lem:lemma1}\lean{Toy.lemma1}\leanok
  For every $n$, $A(n)$ holds.
  \uses{def:A}
  \begin{proof}
    Trivial by arithmetic.
  \end{proof}
\end{lemma}
"""


def write_content(tmp_path: Path, text: str) -> Path:
    path = tmp_path / "content.tex"
    path.write_text(text, encoding="utf-8")
    return path


def test_parses_environments(tmp_path):
    blueprint = parse_blueprint(write_content(tmp_path, CONTENT))
    assert [n.label for n in blueprint.nodes] == ["def:A", "lem:lemma1"]

    definition, lemma = blueprint.nodes
    assert definition.kind == "definition"
    assert definition.lean_names == ["Toy.A"]
    assert definition.title == "Property $A$"
    assert not definition.leanok
    assert definition.chapter == "A toy example"
    assert definition.section == "Definitions"

    assert lemma.is_theorem
    assert lemma.leanok
    assert lemma.uses == ["def:A"]
    assert lemma.proof_tex == "Trivial by arithmetic."
    assert "Trivial" not in lemma.statement_tex
    assert lemma.section == "Lemmas"


def test_chapter_intro(tmp_path):
    blueprint = parse_blueprint(write_content(tmp_path, CONTENT))
    assert blueprint.chapter_intros["A toy example"] == "Intro text of the chapter."


def test_missing_label_is_error(tmp_path):
    text = "\\begin{lemma}\\lean{X}\n stuff \n\\end{lemma}\n"
    with pytest.raises(BlueprintError, match="no \\\\label"):
        parse_blueprint(write_content(tmp_path, text))


def test_duplicate_label_is_error(tmp_path):
    text = (
        "\\begin{lemma}\\label{l}\na\n\\end{lemma}\n"
        "\\begin{lemma}\\label{l}\nb\n\\end{lemma}\n"
    )
    with pytest.raises(BlueprintError, match="duplicate"):
        parse_blueprint(write_content(tmp_path, text))


def test_comments_are_ignored(tmp_path):
    text = "% \\begin{lemma}\\label{ghost}\n\\begin{lemma}\\label{real}\nx\n\\end{lemma}\n"
    blueprint = parse_blueprint(write_content(tmp_path, text))
    assert [n.label for n in blueprint.nodes] == ["real"]


def test_input_resolution(tmp_path):
    (tmp_path / "part.tex").write_text(
        "\\begin{lemma}\\label{lem:sub}\ny\n\\end{lemma}\n", encoding="utf-8"
    )
    blueprint = parse_blueprint(write_content(tmp_path, "\\chapter{C}\n\\input{part}\n"))
    assert [n.label for n in blueprint.nodes] == ["lem:sub"]
