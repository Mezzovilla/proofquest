"""Dependency graph over blueprint nodes, from ``\\uses`` edges."""

from __future__ import annotations

from .game_model import Blueprint, BlueprintNode


class DependencyError(Exception):
    pass


def topological_order(blueprint: Blueprint) -> list[BlueprintNode]:
    """Stable topological order of the blueprint nodes.

    Kahn's algorithm; ties are broken by position in the ``.tex`` source so
    the output is deterministic. Raises :class:`DependencyError` on missing
    labels or cycles.
    """
    by_label = blueprint.by_label()

    missing = [
        (node.label, use)
        for node in blueprint.nodes
        for use in node.uses
        if use not in by_label
    ]
    if missing:
        details = ", ".join(f"{label} -> {use}" for label, use in missing)
        raise DependencyError(f"\\uses references unknown labels: {details}")

    indegree = {node.label: 0 for node in blueprint.nodes}
    dependents: dict[str, list[str]] = {node.label: [] for node in blueprint.nodes}
    for node in blueprint.nodes:
        for use in node.uses:
            indegree[node.label] += 1
            dependents[use].append(node.label)

    ready = sorted(
        (label for label, deg in indegree.items() if deg == 0),
        key=lambda label: by_label[label].order,
    )
    result: list[BlueprintNode] = []
    while ready:
        label = ready.pop(0)
        result.append(by_label[label])
        changed = False
        for dep in dependents[label]:
            indegree[dep] -= 1
            if indegree[dep] == 0:
                ready.append(dep)
                changed = True
        if changed:
            ready.sort(key=lambda lbl: by_label[lbl].order)

    if len(result) != len(blueprint.nodes):
        cyclic = sorted(set(indegree) - {node.label for node in result})
        raise DependencyError(f"cycle detected in \\uses graph involving: {', '.join(cyclic)}")
    return result
