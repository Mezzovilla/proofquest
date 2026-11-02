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


def test_nested_proof_belongs_only_to_its_own_node(tmp_path):
    text = r"""
\chapter{Example}
\begin{lemma}\label{lem:a}\lean{a}
  A.
\end{lemma}
\begin{lemma}\label{lem:b}\lean{b}
  B.
  \begin{proof}\uses{lem:a}
    Proof of B.
  \end{proof}
\end{lemma}
"""
    blueprint = parse_blueprint(write_content(tmp_path, text))
    first, second = blueprint.nodes
    assert first.proof_tex is None
    assert first.uses == []
    assert second.proof_tex == "\\uses{lem:a}\n    Proof of B."
    assert second.uses == ["lem:a"]
    assert blueprint.parse_issues == []


def test_successive_nested_proofs_do_not_leak(tmp_path):
    text = r"""
\begin{lemma}\label{a}A.\begin{proof}Proof A.\end{proof}\end{lemma}
\begin{lemma}\label{b}B.\begin{proof}\uses{a}Proof B.\end{proof}\end{lemma}
"""
    blueprint = parse_blueprint(write_content(tmp_path, text))
    assert [node.proof_tex for node in blueprint.nodes] == ["Proof A.", "\\uses{a}Proof B."]
    assert [node.uses for node in blueprint.nodes] == [[], ["a"]]


def test_sibling_proof_must_be_adjacent(tmp_path):
    text = r"""
\begin{lemma}\label{a}A.\end{lemma}
Editorial text.
\begin{proof}Detached proof.\end{proof}
"""
    blueprint = parse_blueprint(write_content(tmp_path, text))
    assert blueprint.nodes[0].proof_tex is None
    assert any("not adjacent" in issue for issue in blueprint.parse_issues)


def test_unconsumed_binding_in_unsupported_environment_is_reported(tmp_path):
    text = r"""
\chapter{Example}
\begin{claim}\label{custom}\lean{target}
  A custom claim.
\end{claim}
"""
    blueprint = parse_blueprint(write_content(tmp_path, text))
    assert blueprint.nodes == []
    assert any("unsupported claim" in issue for issue in blueprint.parse_issues)
    assert any("no supported formal nodes" in issue for issue in blueprint.parse_issues)


def test_unconsumed_binding_is_reported_in_mixed_blueprint(tmp_path):
    text = r"""
\begin{lemma}\label{supported}\lean{one}One.\end{lemma}
\begin{claim}\label{custom}\lean{two}Two.\end{claim}
"""
    blueprint = parse_blueprint(write_content(tmp_path, text))
    assert [node.label for node in blueprint.nodes] == ["supported"]
    assert any("\\lean{two}" in issue for issue in blueprint.parse_issues)


def test_proof_before_first_node_is_reported(tmp_path):
    text = r"""
\begin{proof}Orphan.\end{proof}
\begin{lemma}\label{later}Later.\end{lemma}
"""
    blueprint = parse_blueprint(write_content(tmp_path, text))
    assert blueprint.nodes[0].proof_tex is None
    assert any("no preceding" in issue for issue in blueprint.parse_issues)


def test_commented_binding_is_not_a_coverage_issue(tmp_path):
    blueprint = parse_blueprint(
        write_content(tmp_path, "% \\lean{ghost}\nSome editorial text.\n")
    )
    assert not any("ghost" in issue for issue in blueprint.parse_issues)
