# proofquest

Deterministic generator of [lean4game](https://github.com/leanprover-community/lean4game)
projects (following the [GameSkeleton](https://github.com/hhu-adam/GameSkeleton)
template) from [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
projects.

Given a Lean project with a `blueprint/` folder, proofquest reads the
dependency graph of the blueprint (`\uses{...}`) and produces a game where the
player proves the theorems of the project, guided by hints extracted from the
LaTeX write-up.

> **New to proofquest?** The end-to-end guide for any leanblueprint project —
> check, generate, build, serve — lives in
> [`proofquest-guide.md`](documents/proofquest-guide.md).

## How it works

1. **Blueprint parsing** — the blueprint entry point (`blueprint/src/content.tex`
   by default; `check` and `generate` also accept the `blueprint/` directory or
   an explicit `.tex` file — see below) is parsed following `\input` for
   `definition`/`lemma`/`theorem`/`proposition`/`corollary`
   environments with their `\label`, `\lean{}`, `\uses{}` and `proof` blocks.
2. **Lean parsing** — the project's `.lean` sources are scanned: `def`s are
   copied verbatim into the game, `theorem` signatures are extracted and the
   original proofs become sample solutions. The generated game is
   self-contained (it does not depend on the original project).
3. **Dependency graph** — `\uses` edges are checked (missing labels, cycles)
   and topologically sorted with ties broken by position in the `.tex` file,
   so the output is fully deterministic.
4. **Generation** — each `\chapter` becomes a World, each theorem becomes a
   Level: the LaTeX statement becomes the level `Introduction`, the LaTeX
   proof becomes a `Hint`, and tactics/definitions are introduced in the first
   level that needs them.

## Usage

Validate the blueprint against the Lean sources. The `check` and `generate`
target may be the project root, its `blueprint/` directory, or an explicit
`.tex` entry point inside `blueprint/`:

```bash
uv sync

# Validate the blueprint against the Lean sources
uv run proofquest check /path/to/project
uv run proofquest check /path/to/project/blueprint
uv run proofquest check /path/to/project/blueprint/src/print.tex

# Generate the game
uv run proofquest generate /path/to/project -o /path/to/game --title "My Game"
uv run proofquest generate /path/to/project/blueprint -o /path/to/game
uv run proofquest generate /path/to/project/blueprint/src/print.tex -o /path/to/game
```

When `check` or `generate` is given a project root or a `blueprint/`
directory, it picks the entry point deterministically: `content.tex`,
`web.tex`, `print.tex`, `main.tex` — in that order — under `blueprint/src/`
first, then `blueprint/` itself (`src/content.tex` always wins). If no
conventional name exists, or the same non-`content.tex` name exists in both
places, the command fails and asks for an explicit `.tex` file. Whatever the
form, the Lean scan, the `blueprint/lean_decls` / `blueprint/web` checks, the
default game title and the `lean-toolchain` are all read from the enclosing
project root. `serve` takes a generated game directory instead and performs
no blueprint resolution.

Then build the game (requires a lean4game-compatible toolchain, tags `v4.X.0`):

```bash
cd /path/to/game
lake update -R
lake build
```

## Serving the game

Host the built game on localhost without cloning lean4game and without running
`npm` yourself:

```bash
uv run proofquest serve /path/to/game
# game ready: http://localhost:3000/#/g/local/game
```

The client and relay artifacts are **pinned to the lean4game release tag
derived from the game's toolchain** (`v4.X.0`, the same rule as `generate`) —
never `latest`. The pinned tree is reused from the `GameServer` dependency that
`lake` already fetched into `game/.lake/packages/GameServer` (lake checks out
the whole lean4game repository for that dependency); if it is absent, the
matching GitHub tag tarball is downloaded once. Either way nothing is cloned
and no version can drift: the first run installs the pinned npm dependencies
(opting in to lean4game's single pinned git dependency with
`npm ci --allow-git=root`, since npm 12 blocks git deps by default) and builds
the client (vite) and relay (tsc) inside `~/.cache/proofquest/`, later runs
reuse them.

Opening a level in the browser starts the game's Lean server (`lake serve` in
the game folder), so `lake`/`elan` must be on `PATH`. `Ctrl+C` stops hosting.

| Option           | Effect                                                        |
|------------------|---------------------------------------------------------------|
| `-p, --port`     | port to listen on (default 3000)                              |
| `--build`        | run `lake build` first when `.lake/gamedata` is missing       |
| `--rebuild`      | re-run the pinned npm install/build even if the cache is warm |
| `--lean4game DIR`| copy client/relay sources from this checkout into the cache  |

## Development

```bash
uv run pytest                   # unit + end-to-end tests; real integrations explicitly skip
uv run pytest --run-integration # additionally clone/build the pinned real repositories
uv run ruff check               # lint
```

## Known limitations

- Lean sources are parsed textually: only regular declarations are supported
  (no `where` clauses, mutual blocks, or exotic notation in signatures).
- The LaTeX → markdown conversion covers a documented subset (math mode is
  passed through to KaTeX; `\emph`, `\textbf`, `\texttt`, `\nameref`/`\ref`
  are translated; other macros are left as-is).
- Two theorems with the same short name in different namespaces would collide
  in level file names.
- If the input project's `lean-toolchain` has no matching lean4game tag
  (e.g. `-rc` versions), adjust the generated `lean-toolchain` manually.
