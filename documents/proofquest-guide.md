# proofquest guide — from a leanblueprint project to a playable Lean 4 game

proofquest turns any [leanblueprint](https://github.com/PatrickMassot/leanblueprint/)
project into a [lean4game](https://github.com/leanprover-community/lean4game)
game: every theorem of your blueprint becomes a level, each `\chapter` becomes a
world, and your LaTeX proofs become the hints. This guide covers the whole
workflow for any Lean project. For a concrete minimal project, read the
[worked example](toy_example.md); fine details live in the
[package README](proofquest/README.md) and in `proofquest <command> --help`.

The three commands, in order:

| Command    | What it does                                                        |
|------------|---------------------------------------------------------------------|
| `check`    | validates the blueprint against the Lean sources (fast, no build)   |
| `generate` | writes a self-contained [GameSkeleton](https://github.com/hhu-adam/GameSkeleton) game from the blueprint |
| `serve`    | hosts the built game on localhost — no lean4game clone, no manual npm |

## What your project needs to look like

proofquest reads a [leanblueprint](https://github.com/PatrickMassot/leanblueprint/)
project:

- `blueprint/src/content.tex` — the write-up. Each claim is an environment
  (`definition`, `lemma`, `theorem`, `proposition`, `corollary`) with:
  - `\label{...}` — the blueprint-wide identifier;
  - `\lean{Name}` — the matching Lean declaration. Every environment needs one
    that resolves before `generate` can run (`check` only warns for
    theorem-like environments without one);
  - `\uses{a, b}` — dependency edges (they become the level ordering);
  - a `proof` environment — its LaTeX becomes the in-game hint.
  `\chapter{...}` becomes a game world; `\input{...}` is followed recursively.
- Lean sources with plain top-level `def` / `theorem` / `lemma` / `abbrev` /
  `instance` declarations whose names appear in `\lean{}`. Declarations are
  parsed textually: no `where` clauses, mutual blocks or exotic notation in
  signatures (see "Known limitations" in the package README).
- Optional: `blueprint/lean_decls` (one declaration name per line) for a
  cross-check, and `blueprint/web/` (from `leanblueprint web`).

`proofquest check` reports **errors** (a `\lean{X}` with no matching Lean
declaration; `\uses` referencing unknown labels; cycles in the `\uses` graph)
and **warnings** (theorem-like environments without `\lean{}`, names listed in
`blueprint/lean_decls` but not referenced — or vice versa, missing
`blueprint/web`). `generate` refuses to run while errors remain.

## Prerequisites

| Step         | Needs                                                                 |
|--------------|-----------------------------------------------------------------------|
| `check`      | Python ≥ 3.12 + [uv](https://docs.astral.sh/uv/)                       |
| `generate`   | same (no Lean needed — the game is generated textually)                |
| `lake build` | [elan](https://github.com/leanprover/elan) (fetches the pinned game toolchain automatically) |
| `serve`      | Node.js + npm (first run only), plus `lake`/`elan` on `PATH`           |

### Get proofquest

proofquest is not published yet — neither on PyPI nor in a public repository.
For now the package lives in the `proofquest/` subdirectory of this
repository: run `uv sync` inside `proofquest/` and use it from there
(`uv run proofquest ...`). A public release is planned.

## Workflow

```bash
# 1. validate blueprint x Lean sources
uv run proofquest check /path/to/project

# 2. generate the game
uv run proofquest generate /path/to/project -o /path/to/game --title "My Game"

# 3. build the game (its own toolchain, pinned by generate)
cd /path/to/game
lake update -R
lake exe cache get   # fetch the Mathlib cache so Mathlib is NOT rebuilt
lake build

# 4. host it locally
cd /path/to/proofquest
uv run proofquest serve /path/to/game
```

The game is then playable at the URL `serve` prints, by default
`http://localhost:3000/#/g/local/<game-folder-name>`. Opening a level starts
the game's Lean server (`lake serve` in the game folder); `Ctrl+C` stops
hosting.

After editing the blueprint or the Lean sources, re-run `check` + `generate`
and `lake build` again; then reload the browser.

## Version pinning (why there is no "latest")

lean4game publishes release tags `v4.X.0`. A generated game is pinned to the
newest release at or below the **project's** toolchain minor version: a project
on `v4.32.2` gets its game pinned to `v4.31.0`, and `generate` prints a warning
saying so. The project itself keeps its own toolchain — only the generated game
is downgraded. If the project's toolchain cannot be parsed (or is missing), the
newest known release is used, also with a warning. The generated game's
toolchain is therefore always a release tag — never a moving branch — so the
generated game and its built GameServer match. `serve` reads the exact ref the
game was built against from the game's `lake-manifest.json` (`GameServer`
entry — normally that same tag) and pins the served client/relay to it, so
client and server cannot drift.

## Command options

### `proofquest check PROJECT`

Validates and prints the topological order of the blueprint graph. Exit code 1
on errors.

### `proofquest generate PROJECT -o GAME_DIR`

| Option         | Effect                                              |
|----------------|-----------------------------------------------------|
| `-o, --output` | output directory for the game (required)            |
| `--title`      | game title (default: project folder name)           |
| `--lang`       | game language code (default `en`)                   |
| `--toolchain`  | override the pinned game toolchain                  |

### `proofquest serve [GAME_DIR]`

| Option            | Effect                                                        |
|-------------------|---------------------------------------------------------------|
| `GAME_DIR`        | the generated game directory (default `./game`)               |
| `-p, --port`      | port to listen on (default 3000)                              |
| `--build`         | run `lake build` first when `.lake/gamedata` is missing       |
| `--rebuild`       | re-run the pinned npm install/build even if the cache is warm |
| `--lean4game DIR` | copy client/relay sources from this checkout into the cache   |

`serve` never rebuilds Mathlib and never clones lean4game: the client/relay
sources pinned to the game's toolchain tag are reused from the `GameServer`
dependency `lake` already fetched into `game/.lake/packages/GameServer` (or
downloaded once from the pinned GitHub tag), and the first run installs the
pinned npm dependencies and builds the client inside `~/.cache/proofquest/`
(override with `PROOFQUEST_CACHE`). Later runs reuse the cache.

## Troubleshooting

- **`\lean{X} not found in the Lean sources`** — the declaration must exist
  verbatim as a top-level `def`/`theorem`/`lemma`/`abbrev`/`instance` in the
  project. Textual parsing does not handle `where` clauses, mutual blocks or
  exotic notation in signatures.
- **`... has no matching Lean declaration`** — every environment (definition
  or theorem-like) needs a `\lean{}` that resolves for `generate` to run;
  `check` only warns for theorem-like ones, so run `check` and read the
  warnings too.
- **`\uses references unknown labels` / `cycle detected`** — fix the labels in
  `content.tex`; the level order is the topological order of this graph.
- **`lake build` starts rebuilding Mathlib** — abort and fetch the cache
  first: `lake exe cache get` (use `lake exe cache get!` only if the cache is
  in a bad state). proofquest itself never rebuilds Mathlib.
- **Toolchain downgrade warning from `generate`** — expected when the project
  uses a newer Lean than the newest lean4game release; the game is pinned to
  the newest compatible `v4.X.0` tag. Pass `--toolchain` to override.
- **`port ... is already in use`** — choose another with `--port`; the check
  runs before anything is downloaded or built.
- **First `serve` run is slow** — it downloads the pinned npm dependencies and
  builds the client (vite) and relay (tsc) once into `~/.cache/proofquest/`;
  this is a versioned download, not a clone. Later runs reuse it. On npm >= 12
  proofquest passes `--allow-git=root` automatically for lean4game's pinned
  git dependency.
- **Game folder named `lean4game-...`** — rejected: it would collide with
  proofquest's runtime cache entries; rename the folder (the URL name follows
  the folder name).

## Worked example

[toy_example.md](toy_example.md) walks the whole flow on a minimal project —
blueprint, sources, toolchain fix, build and play — with the concrete commands
and expected output.
