"""Cross-checks between the blueprint, the Lean sources and build artifacts."""

from __future__ import annotations

from pathlib import Path

from .game_model import Blueprint, LeanDecl


def validate(
    project_dir: Path,
    blueprint: Blueprint,
    decls: dict[str, LeanDecl],
    entry_point: Path | None = None,
    for_game: bool = False,
) -> tuple[list[str], list[str]]:
    """Return ``(errors, warnings)`` for the given project."""
    errors: list[str] = []
    warnings: list[str] = []

    if for_game:
        errors.extend(blueprint.parse_issues)
    else:
        warnings.extend(blueprint.parse_issues)

    if blueprint.nodes and not any(node.is_theorem for node in blueprint.nodes):
        message = (
            "blueprint contains definitions but no theorem-like nodes; "
            "it cannot produce game levels"
        )
        (errors if for_game else warnings).append(message)

    referenced: set[str] = set()
    for node in blueprint.nodes:
        for lean_name in node.lean_names:
            referenced.add(lean_name)
            if lean_name not in decls:
                errors.append(
                    f"{node.label}: \\lean{{{lean_name}}} not found in the Lean sources"
                )
        if not node.lean_names:
            warnings.append(f"{node.label}: {node.kind} has no \\lean{{}} declaration")

    lean_decls_file = project_dir / "blueprint" / "lean_decls"
    if entry_point is None:
        entry_name = "the selected blueprint"
    else:
        try:
            entry_name = str(entry_point.resolve().relative_to(project_dir.resolve()))
        except ValueError:
            entry_name = str(entry_point)
    if lean_decls_file.exists():
        listed = {
            line.strip()
            for line in lean_decls_file.read_text(encoding="utf-8").splitlines()
            if line.strip()
        }
        for name in sorted(referenced - listed):
            warnings.append(f"{name}: referenced in the blueprint but missing from lean_decls")
        for name in sorted(listed - referenced):
            warnings.append(
                f"{name}: listed in lean_decls but not referenced in {entry_name}"
            )
    else:
        warnings.append(
            "blueprint/lean_decls not found; skipping optional registry consistency "
            "check (explicit \\lean{} links were still checked against local sources)"
        )

    return errors, warnings
