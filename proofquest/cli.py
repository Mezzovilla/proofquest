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


def _load(project_dir: Path, exclude: tuple[Path, ...] = ()):
    content_tex = project_dir / "blueprint" / "src" / "content.tex"
    blueprint = parse_blueprint(content_tex)
    decls = parse_project(project_dir, exclude)
    return blueprint, decls


def _report(errors: list[str], warnings: list[str]) -> None:
    for warning in warnings:
        print(f"warning: {warning}", file=sys.stderr)
    for error in errors:
        print(f"error: {error}", file=sys.stderr)


def _default_title(project_dir: Path) -> str:
    return project_dir.resolve().name


def cmd_check(args: argparse.Namespace) -> int:
    project_dir = Path(args.project)
    blueprint, decls = _load(project_dir)
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
    chk.add_argument("project", help="path to the Lean project containing blueprint/")
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
