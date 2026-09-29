"""Command-line interface: ``proofquest generate``, ``check`` and ``serve``."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from .blueprint_parser import BlueprintError, parse_blueprint
from .dep_graph import DependencyError, topological_order
from .generator import GenerationError, build_game, write_game
from .lean_parser import parse_project
from .serve import ServeError, cmd_serve
from .toolchain import game_toolchain
from .validate import validate


def _load(project_dir: Path, exclude: tuple[Path, ...] = (), source: Path | None = None):
    content_tex = (
        source
        if source is not None
        else project_dir / "blueprint" / "src" / "content.tex"
    )
    blueprint = parse_blueprint(content_tex)
    decls = parse_project(project_dir, exclude)
    return blueprint, decls


_ENTRY_POINT_NAMES = ("content.tex", "web.tex", "print.tex", "main.tex")


def _find_entry_point(blueprint_dir: Path) -> Path:
    """Pick the conventional ``.tex`` entry point inside a blueprint directory.

    Candidates are looked up under ``blueprint/src`` and ``blueprint`` itself,
    trying each name of :data:`_ENTRY_POINT_NAMES` in order. ``src/content.tex``
    wins unconditionally (existing behaviour); for any other name, finding it
    in *both* locations is ambiguous and raises a :class:`BlueprintError`
    instead of picking one arbitrarily.
    """
    for name in _ENTRY_POINT_NAMES:
        candidates = [
            path
            for path in (blueprint_dir / "src" / name, blueprint_dir / name)
            if path.is_file()
        ]
        if not candidates:
            continue
        if name != "content.tex" and len(candidates) > 1:
            raise BlueprintError(
                f"ambiguous blueprint entry point {name}: found both "
                f"{candidates[0]} and {candidates[1]}; "
                "pass the intended .tex file explicitly"
            )
        return candidates[0]
    raise BlueprintError(
        f"no blueprint entry point found in {blueprint_dir}: looked for "
        + ", ".join(f"src/{name} or {name}" for name in _ENTRY_POINT_NAMES)
        + "; pass the .tex entry point explicitly"
    )


def _resolve_check_target(path: Path) -> tuple[Path, Path]:
    """Resolve a ``check`` argument to ``(project_root, entry_point.tex)``.

    Accepted forms: the Lean project root (containing ``blueprint/``), the
    ``blueprint/`` directory itself, or an explicit ``.tex`` file located
    inside a ``blueprint/`` directory. In every case the enclosing Lean
    project root is what gets scanned for Lean declarations.
    """
    if path.is_file():
        entry = path.resolve()
        if entry.suffix != ".tex":
            raise BlueprintError(
                f"not a .tex entry point: {path}; pass the blueprint's .tex file"
            )
        for ancestor in entry.parents:
            if ancestor.name == "blueprint":
                return ancestor.parent, entry
        raise BlueprintError(
            f"{path} is not inside a blueprint/ directory; "
            "pass a .tex entry point within the project's blueprint/"
        )
    if path.is_dir():
        if (path / "blueprint").is_dir():
            return path, _find_entry_point(path / "blueprint")
        if path.name == "blueprint":
            return path.parent, _find_entry_point(path)
        raise BlueprintError(
            f"{path} is not a Lean project (no blueprint/ subdirectory) "
            "nor a blueprint/ directory; pass the project root, its "
            "blueprint/ directory, or an explicit .tex entry point"
        )
    raise BlueprintError(f"project path not found: {path}")


def _report(errors: list[str], warnings: list[str]) -> None:
    for warning in warnings:
        print(f"warning: {warning}", file=sys.stderr)
    for error in errors:
        print(f"error: {error}", file=sys.stderr)


def _default_title(project_dir: Path) -> str:
    return project_dir.resolve().name


def cmd_check(args: argparse.Namespace) -> int:
    project_dir, source = _resolve_check_target(Path(args.project))
    blueprint, decls = _load(project_dir, source=source)
    errors, warnings = validate(project_dir, blueprint, decls)
    try:
        order = topological_order(blueprint)
    except DependencyError as exc:
        errors.append(str(exc))
        order = []
    _report(errors, warnings)
    if errors:
        return 1
    print(f"ok: {len(blueprint.nodes)} blueprint nodes, {len(decls)} Lean declarations")
    print("topological order: " + " -> ".join(node.label for node in order))
    return 0


def cmd_generate(args: argparse.Namespace) -> int:
    project_dir = Path(args.project)
    output_dir = Path(args.output)
    blueprint, decls = _load(project_dir, (output_dir,))
    errors, warnings = validate(project_dir, blueprint, decls)

    toolchain_file = project_dir / "lean-toolchain"
    project_toolchain = (
        toolchain_file.read_text(encoding="utf-8").strip()
        if toolchain_file.exists()
        else None
    )
    if args.toolchain:
        toolchain = args.toolchain
    else:
        toolchain, toolchain_warning = game_toolchain(project_toolchain)
        if toolchain_warning:
            warnings.append(toolchain_warning)

    _report(errors, warnings)
    if errors:
        return 1

    game = build_game(
        blueprint,
        decls,
        toolchain=toolchain,
        title=args.title or _default_title(project_dir),
        languages=args.lang,
    )
    written = write_game(game, output_dir)
    print(f"generated {len(written)} files in {args.output}")
    for path in written:
        print(f"  {path.relative_to(args.output)}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="proofquest",
        description="Generate a lean4game (GameSkeleton) project from a leanblueprint project.",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    gen = sub.add_parser("generate", help="generate the game from a blueprint project")
    gen.add_argument("project", help="path to the Lean project containing blueprint/")
    gen.add_argument("-o", "--output", required=True, help="output directory for the game")
    gen.add_argument("--title", default=None, help="game title (default: project folder name)")
    gen.add_argument("--lang", default="en", help="game language code (default: en)")
    gen.add_argument("--toolchain", default=None, help="override lean-toolchain (e.g. leanprover/lean4:v4.31.0)")
    gen.set_defaults(func=cmd_generate)

    chk = sub.add_parser("check", help="validate blueprint against the Lean sources")
    chk.add_argument(
        "project",
        help="path to the Lean project, its blueprint/ directory, or an "
        "explicit blueprint .tex entry point",
    )
    chk.set_defaults(func=cmd_check)

    srv = sub.add_parser(
        "serve",
        help="host a generated game locally (no lean4game clone needed)",
    )
    srv.add_argument(
        "game",
        nargs="?",
        default="game",
        help="path to the generated game directory (default: ./game)",
    )
    srv.add_argument(
        "-p", "--port", type=int, default=3000, help="port to listen on (default: 3000)"
    )
    srv.add_argument(
        "--lean4game",
        default=None,
        metavar="DIR",
        help="copy client/relay sources from this lean4game checkout into the "
        "cache (default: the game's GameServer lake package, else a pinned "
        "download)",
    )
    srv.add_argument(
        "--rebuild",
        action="store_true",
        help="re-run the pinned npm install/build even if the cache is warm",
    )
    srv.add_argument(
        "--build",
        action="store_true",
        help="run `lake build` in the game directory first when gamedata is missing",
    )
    srv.set_defaults(func=cmd_serve)

    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except (BlueprintError, DependencyError, GenerationError, ServeError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
