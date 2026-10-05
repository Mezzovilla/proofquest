# proofquest guide — from a leanblueprint project to a playable Lean 4 game

proofquest generates a [lean4game](https://github.com/leanprover-community/lean4game)
game from a [leanblueprint](https://github.com/PatrickMassot/leanblueprint/)
project **together with its Lean sources**: every supported, successfully
mapped theorem-like blueprint node (`lemma`, `theorem`, `proposition`,
`corollary`) becomes one level, each `\chapter` becomes a world, and
definition nodes become staged background inventory. This guide describes
what the current tree — the state targeted at release 0.7.0 — actually
does, including its limits.

| Step         | What it does                                                        |
|--------------|---------------------------------------------------------------------|
| `check`      | fast static validation of blueprint vs Lean sources (no build)      |
| `generate`   | writes a [GameSkeleton](https://github.com/hhu-adam/GameSkeleton) game, with stricter preflight |
| `lake build` | the real Lean compilation of the generated game — the first gate that type-checks the level proofs |
| `serve`      | hosts the built game on localhost — no lean4game clone needed       |

These are four distinct gates — success at one does not certify success at
the next. Nor is any of this automatic formalization: LaTeX proofs are
rendered as in-game hints only, never the source of the Lean proofs, and no
step verifies LaTeX prose or mathematics against the Lean development.

## What your project needs to look like

proofquest reads a leanblueprint project: a `.tex` entry point (the project
root, its `blueprint/` directory, or an explicit `.tex` file all work — see
`proofquest check` below) plus Lean sources in the supported text subset. Each
claim is an environment (`definition`, `lemma`, `theorem`, `proposition`,
`corollary`) with:

- `\label{...}` — a unique blueprint-wide identifier;
- `\lean{Name}` — the matching Lean declaration, given as the exact full
  Unicode Lean name. A commented-out `%\lean{...}` is ignored, and `\leanok`
  does not replace the binding. Definition environments may map several
  declarations with `\lean{A,B}`; every member must resolve.
- `\uses{a, b}` — dependency edges (they drive the level ordering); and
- a `proof` environment placed adjacent and at top level right after the
  claim — its LaTeX becomes the in-game hint (optional; not a Lean proof
  source).

`\input{...}` is followed recursively up to a nesting depth of 10. The
argument must be a literal path, and every `\input` path is resolved
relative to the **selected entry file's parent** directory — not relative
to each included file. Comments are stripped. There is no general TeX
expansion: `\include`, custom environments, starred theorem-style aliases,
nested-brace titles and macros are not generally supported. Unsupported
environments are currently **silently ignored**: `check` can exit 0 with no
warning that claims were dropped — a fully unrecognized source produces
zero nodes and still exits 0 — though unrelated optional-metadata warnings
may still print. Coverage warnings are tracked in
[#32](https://github.com/Mezzovilla/proofquest/issues/32).

Optional: `blueprint/lean_decls` (one declaration name per line) for a
cross-check, and `blueprint/web/` (from `leanblueprint web`) — its presence
only silences the "not built" warning; it enables no extra validation today.

## Prerequisites

| Step         | Needs                                                                 |
|--------------|-----------------------------------------------------------------------|
| `check`      | Python ≥ 3.12 + [uv](https://docs.astral.sh/uv/)                       |
| `generate`   | same (no Lean needed — the game is generated textually)                |
| `lake build` | [elan](https://github.com/leanprover/elan) (fetches the pinned game toolchain automatically) |
| `serve`      | modern games: system Node.js + npm (first run only) plus `lake`/`elan`; legacy v4.7 games: `lake`/`elan` — a private Node 22.17.0 is provisioned in the cache |

### Get proofquest

The public repository is `Mezzovilla/proofquest` on GitHub. From a source
checkout:

```bash
cd /path/to/proofquest
uv sync
uv run proofquest check /path/to/project
```

From anywhere else, point uv at the checkout:

```bash
uv run --project /path/to/proofquest proofquest check /path/to/project
```

A globally installed `proofquest` binary may be an older copy — prefer the
checkout. See the [package README](../README.md) and
`proofquest <command> --help` for details; a runnable fixture project lives in
[`tests/toy_example/`](../tests/toy_example/).

## Workflow

```bash
# 1. validate blueprint x Lean sources (static only)
uv run proofquest check /path/to/project

# 2. generate the game
uv run proofquest generate /path/to/project -o /path/to/game --title "My Game"

# 3. build the game (its own toolchain, pinned by generate)
cd /path/to/game
lake update -R
lake exe cache get   # fetch the Mathlib cache; it can miss, in which case the build rebuilds what it needs
lake build

# 4. host it locally
cd /path/to/proofquest
uv run proofquest serve /path/to/game
```

The game is then playable at the URL `serve` prints, by default
`http://localhost:3000/#/g/local/<game-folder-name>`. Opening a level starts
the game's Lean server (`lake serve` in the game folder); `Ctrl+C` stops
hosting. `serve --build` runs `lake build` when the gamedata is missing — so
builds can still compile Mathlib if the cache could not provide it. After
editing the blueprint or the Lean sources, re-run `check` + `generate` and
`lake build` again; then reload the browser. `generate` overwrites the managed
files it emits but does not purge orphans or replace output transactionally:
for structural changes prefer a fresh output directory, and never delete
`.lake` or your own files to force regeneration.

## Version pinning (why there is no "latest")

lean4game publishes release tags `v4.X.0`. By default a generated game is
pinned to the newest *known* release at or below the **project's** toolchain
minor version when such a tag exists — a project on `v4.32.2` gets its game
pinned to `v4.31.0`, and `generate` prints a warning saying so — and falls
back to the newest known release otherwise. The project's toolchain is not
modified; the selected game toolchain may differ from it. If `lean-toolchain` is
missing the fallback is used silently; if it is present but unrecognizable,
with a warning. `serve` reads the exact ref the game was built against from
`lake-manifest.json` (the `GameServer` entry) and pins the served
client/relay to it — that ref records what resolved at build time, not an
immutability guarantee: a manifest pointing at a moving ref or a
`--lean4game` override can still drift.

`--toolchain X` is used **verbatim** — it bypasses release-tag selection
entirely, so an unreleased or mistyped tag produces a game that may not
build. A game pinned to an older lean4game release is only as compatible as
its source uses: it needs matching mathlib pins and symbols, and a minimal
amount of source compatibility — there is no universal "restore an older
toolchain" fix.

## The supported subsets

### Blueprint

Recognized claim environments are exactly `definition`, `lemma`, `theorem`,
`proposition`, `corollary`; `\chapter`/`\section` titles are read flat.
Current limits worth knowing up front:

- **Map one canonical level binding per theorem-like node.** This is the
  recommended form, not a parser constraint — multiple `\lean` declarations
  are all collected. If a `\lean{A,B}` list is given on a theorem-like node,
  only the first matching name becomes the level target. Kind mismatches (a
  definition bound where a theorem is expected), *distinct* labels mapping
  the same Lean target, and ambiguous resolution are not fully checked —
  duplicate LaTeX `\label`s themselves are already `check` errors
([#30](https://github.com/Mezzovilla/proofquest/issues/30)).
- **Index coverage is textual.** Aliases, `export`ed names and auto-generated
  projections are not reliably indexed as target names — `\lean` should name
  the declaration itself. Make sure targets are not pre-imported answers: the
  level's job is for the player to prove it.
- **Grouped definitions.** `\lean{A,B}` on a definition maps all members.
  Staging is per declaration — each member is emitted after its *own*
  prerequisites, so members can land at different stages — but the group node
  still acts as a single ordering barrier wherever it is referenced, and a
  whole-group edge can create a mixed source+blueprint cycle even when the
  individual declarations are acyclic. When that barrier causes the conflict,
  split the group into separate definition nodes with their own labels,
  `\lean{...}` bindings and `\uses` edges. Several `\lean` macros in the same
  node do not split the group; never drop members to silence warnings.
- **Nested `proof` environments are unsafe today**
  ([#31](https://github.com/Mezzovilla/proofquest/issues/31)). A `proof`
  nested inside another claim's body can attach its `\uses` and hint to the
  previous claim and even produce a spurious self-cycle error in `check`.
  Keep every `proof` adjacent at top level until this is fixed.
- `\uses` is parsed as graph edges; the *proof's* dependencies are not
  semantically validated against it.
- Additional Lean references inside a node still matter for ordering and
  staging: auxiliary declarations are staged after their prerequisite levels.
  Beyond the explicit `\uses` cycles that `check` already reports, the
  *additional* mixed source/definition cycles, contiguous-world constraints
  and normalized chapter-name collisions are only diagnosed by `generate`.

### Lean

The textual parser accepts: top-level `def`, `abbrev`, `lemma`, `theorem`,
`structure`, `class`; `:= by` tactic proofs and plain term proofs; `instance`
declarations including `where` bodies and `noncomputable section`; plain and
command-local `open`; simple `local notation`/`notation3` and bounded global
`notation`; and named instance attributes.

It rejects or fails on: `macro`/`elab`, `mutual` blocks, exotic or complex
notations, other attributes, `set_option`-style project-local context, and
unresolvable name ambiguities. Unsupported context is detected at `generate`
time with an error naming the offending command. Because parsing is textual,
some unsupported forms only surface at `lake build` — there is no universal
guard that everything accepted textually compiles.

## What `check` does (and does not) certify

`proofquest check` reports **errors** — a `\lean{X}` with no matching Lean
declaration, `\label`/`\input` parse errors, `\uses` referencing unknown
labels, cycles in the explicit `\uses` graph — and **warnings**: missing
`\lean{}` on definition *and* theorem-like nodes, `blueprint/lean_decls`
drift or absence, missing `blueprint/web`. Exit code is 1 on errors, **0
with warnings**. Those warnings are metadata diagnostics, not a readiness
score — `check` can miss real blockers with no specific warning (richer
artifact diagnostics are tracked in
[#33](https://github.com/Mezzovilla/proofquest/issues/33)). It is not a
generation-ready certification
([#29](https://github.com/Mezzovilla/proofquest/issues/29)): `generate` adds
a stricter preflight covering unsupported project-local source context
(`set_option`, custom syntax), emission-order cycles introduced by grouped
members or copied definitions, and a level target with no proof to reuse as
the sample solution. `generate` is itself still incomplete — roles,
multiple bindings on theorem-like nodes and empty/unsupported claims are
not fully checked — so `lake build` remains the real gate. There are no
`--for-game`, `--strict` or `--fix` flags — fixes belong in the sources.

## Command options

### `proofquest check TARGET`

Validates and prints the topological order of the blueprint graph. `TARGET`
may be the Lean project root (the directory containing `blueprint/`), the
`blueprint/` directory itself, or an explicit `.tex` entry point inside
`blueprint/` (e.g. `blueprint/src/print.tex`), parsed with recursive `\input`
resolution. For the directory forms the entry point is chosen
deterministically: `content.tex` > `web.tex` > `print.tex` > `main.tex`,
looked up under `blueprint/src/` first and then `blueprint/` itself
(`src/content.tex` is always preferred). No match — or the same
non-`content.tex` name in both places — is an error asking for an explicit
`.tex` file. Whatever the form, Lean scanning and the `blueprint/lean_decls` /
`blueprint/web` checks are always rooted at the enclosing project.

### `proofquest generate TARGET -o GAME_DIR`

`TARGET` accepts exactly the same forms as `check`, with the same
deterministic entry-point selection. The default game title, the
`lean-toolchain` and the Lean scan always come from the enclosing project
root.

| Option         | Effect                                              |
|----------------|-----------------------------------------------------|
| `-o, --output` | output directory for the game (required)            |
| `--title`      | game title (default: project folder name)           |
| `--lang`       | game language code (default `en`)                   |
| `--toolchain`  | override the pinned game toolchain (used verbatim)  |

### `proofquest serve [GAME_DIR]`

| Option            | Effect                                                        |
|-------------------|---------------------------------------------------------------|
| `GAME_DIR`        | the generated game directory (default `./game`)               |
| `-p, --port`      | port to listen on (default 3000)                              |
| `--build`         | run `lake build` first when `.lake/gamedata` is missing       |
| `--rebuild`       | rerun runtime preparation — legacy gets a fresh cache entry, modern rebuilds the managed cache |
| `--lean4game DIR` | copy client/relay sources from this checkout into the cache   |

For client preparation, `serve` copies the pinned sources from the
`GameServer` package already fetched into `game/.lake/packages/GameServer`,
or downloads a pinned tarball — it does not clone lean4game for this step.
With `--build`, the delegated Lake build may fetch or clone dependencies.
Client dependencies are installed into the cache at `$PROOFQUEST_CACHE/proofquest`,
`$XDG_CACHE_HOME/proofquest` or `~/.cache/proofquest`. `--lean4game` overrides
the source; the caller is responsible for matching the game's pinned ref — a
moved checkout can still drift.

Two runtime layouts are supported:

- **Modern games** (recent `v4.X.0` tags): system `node`/`npm` run
  `build:relay` + `build:client` and serve `relay/dist/src/index.js`.
- **Legacy v4.7 games**: the raw `relay/index.mjs` is served with a
  hash-verified private Node 22.17.0 provisioned inside the cache, and the
  three dead git-sourced dependencies are materialized as private tarballs
  pinned by exact commit and checksum — the upstream registry lockfile is
  otherwise untouched. No global Node/npm install is needed for this branch,
  and no `node_modules` is patched. Support covers bounded tested legacy
  refs, not arbitrary old tags; the Node provisioning maps Linux/macOS
  x64/arm64 archives, but end-to-end verification here covered Linux x64
  only.

Legacy hosting is loopback-only: the relay binds to `127.0.0.1`, the game
websocket only accepts same-origin/empty origins, and the remote game-import
endpoints return 404. On v4.7, game inventory is completed automatically at
level end from the GameServer level metadata, so the inventory the shipped
proofs use is available at the default **regular** difficulty — verified
end-to-end on FLT3's first level. Do not lower the Rules setting as a
workaround.

## Troubleshooting

- **`\lean{X} not found`** — the declaration must exist verbatim as a
  top-level declaration in the supported syntax.
- **`\uses references unknown labels` / `cycle detected`** — fix the labels;
  a spurious self-cycle plus misplaced hints is the signature of a `proof`
  nested inside another claim — move it out.
- **unsupported-context error from `generate`** — a module defines
  project-local commands the generated level files cannot reproduce; expand
  the syntax or move the declaration to a module without such context.
- **`lake build` starts rebuilding Mathlib** — `lake exe cache get` can miss;
  let the build continue or re-fetch the cache for the pinned revisions.
- **Toolchain downgrade warning from `generate`** — expected (see pinning
  above); `--toolchain` overrides verbatim, wrong tags fail at build.
- **`port ... is already in use`** — choose another with `--port`.
- **First `serve` run is slow** — it downloads the pinned npm dependencies
  and builds the client once into the cache; on npm ≥ 12 proofquest passes
  `--allow-git=root` for modern lean4game's pinned git dependency.
- **Game folder named `lean4game-...`** — rejected: it would collide with
  proofquest's runtime cache entries; rename the folder.
