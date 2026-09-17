import pytest

from proofquest.dep_graph import DependencyError, topological_order
from proofquest.game_model import Blueprint, BlueprintNode


def node(label, uses, order, kind="lemma"):
    return BlueprintNode(
        kind=kind,
        label=label,
        lean_names=[],
        title=None,
        statement_tex="",
        proof_tex=None,
        uses=uses,
        leanok=True,
        chapter="C",
        section=None,
        order=order,
    )


def test_stable_topological_order():
    blueprint = Blueprint(
        nodes=[
            node("main", ["a", "b"], 0),
            node("b", [], 1),
            node("a", [], 2),
        ],
        chapters=["C"],
    )
    assert [n.label for n in topological_order(blueprint)] == ["b", "a", "main"]


def test_tex_order_breaks_ties():
    blueprint = Blueprint(nodes=[node("x", [], 0), node("y", [], 1)], chapters=["C"])
    assert [n.label for n in topological_order(blueprint)] == ["x", "y"]


def test_missing_reference():
    blueprint = Blueprint(nodes=[node("a", ["nope"], 0)], chapters=["C"])
    with pytest.raises(DependencyError, match="unknown labels"):
        topological_order(blueprint)


def test_cycle_detection():
    blueprint = Blueprint(nodes=[node("a", ["b"], 0), node("b", ["a"], 1)], chapters=["C"])
    with pytest.raises(DependencyError, match="cycle"):
        topological_order(blueprint)
