"""Cross-checks between the blueprint, the Lean sources and build artifacts."""

from __future__ import annotations

from pathlib import Path

from .game_model import Blueprint, LeanDecl


def validate(
    project_dir: Path, blueprint: Blueprint, decls: dict[str, LeanDecl]
) -> tuple[list[str], list[str]]:
    """Return ``(errors, warnings)`` for the given project."""
    errors: list[str] = []
    warnings: list[str] = []

    referenced: set[str] = set()
    for node in blueprint.nodes:
        for lean_name in node.lean_names:
            referenced.add(lean_name)
            if lean_name not in decls:
                errors.append(
                    f"{node.label}: \\lean{{{lean_name}}} not found in the Lean sources"
                )
        if node.is_theorem and not node.lean_names:
            warnings.append(f"{node.label}: {node.kind} has no \\lean{{}} declaration")

    lean_decls_file = project_dir / "blueprint" / "lean_decls"
    if lean_decls_file.exists():
        listed = {
            line.strip()
            for line in lean_decls_file.read_text(encoding="utf-8").splitlines()
            if line.strip()
        }
        for name in sorted(referenced - listed):
            warnings.append(f"{name}: referenced in the blueprint but missing from lean_decls")
        for name in sorted(listed - referenced):
            warnings.append(f"{name}: listed in lean_decls but not referenced in content.tex")
    else:
        warnings.append("blueprint/lean_decls not found; skipping declaration cross-check")

    if not (project_dir / "blueprint" / "web" / "index.html").exists():
        warnings.append("blueprint/web not built; run `leanblueprint web` to enable full checks")

    return errors, warnings
