"""Host a generated lean4game project locally, without cloning lean4game.

The client and relay artifacts are pinned to the lean4game release tag
``v4.X.0`` derived from the game's toolchain (the same rule the generator uses).
The pinned tree is reused from the ``GameServer`` lake package the game already
fetched (lake clones the whole lean4game repository for that dependency);
otherwise it is downloaded once from the pinned GitHub tag into the proofquest
cache. The user never clones lean4game and never runs ``npm`` by hand: the
first ``proofquest serve`` installs the pinned npm dependencies and builds the
client (vite) and relay (tsc) inside the cache; later runs reuse the result.
"""

from __future__ import annotations

import argparse
import io
import json
import os
import re
import shutil
import signal
import socket
import subprocess
import sys
import tarfile
import time
import urllib.error
import urllib.request
from pathlib import Path

from .toolchain import game_toolchain

_LEAN4GAME_REPO = "leanprover-community/lean4game"
_TAG_RE = re.compile(r"^v\d+\.\d+\.\d+$")
_SHA_RE = re.compile(r"^[0-9a-f]{40}$")
_CACHE_KEY_RE = re.compile(r"^lean4game-")  # any ref form: tag, sha or branch
_READY_MARKER = ".proofquest-serve-ready"
_RELAY_ENTRY = Path("relay/dist/src/index.js")
_CLIENT_INDEX = Path("client/dist/index.html")
# Paths copied from the lean4game tree into the cache; everything else
# (.git, server/, cypress/, ...) is irrelevant for serving.
_COPIED_PATHS = ("client", "relay", "package.json", "package-lock.json")
_COPY_IGNORE = shutil.ignore_patterns("node_modules", "dist", ".lake")
_READY_TIMEOUT = 90.0


class ServeError(Exception):
    """Raised when the game cannot be served; the message is user-facing."""


def lean4game_ref(game_dir: Path) -> tuple[str, str]:
    """Return the lean4game ref (tag, branch or commit) the game was built against.

    The ref must match the game's toolchain so the served client/relay speak
    the same protocol as the built GameServer. ``lake-manifest.json`` records
    the exact ref the game was built against — a release tag ``v4.X.0`` when
    possible, otherwise the branch/commit it names (used as-is for downloads,
    with a warning since it may move); without a manifest, fall back to the
    toolchain rule shared with ``generate``.
    """
    manifest = game_dir / "lake-manifest.json"
    if manifest.exists():
        try:
            packages = json.loads(manifest.read_text(encoding="utf-8"))["packages"]
            entry = next(p for p in packages if p.get("name") == "GameServer")
            rev = entry.get("inputRev")
            if isinstance(rev, str) and rev:
                if _TAG_RE.match(rev):
                    return rev, f"lake-manifest.json (GameServer inputRev {rev})"
                return rev, (
                    f"lake-manifest.json (GameServer inputRev {rev}; not a release "
                    "tag, so it may move — prefer a v4.X.0 tag when rebuilding)"
                )
        except (OSError, ValueError, KeyError, TypeError, AttributeError, StopIteration):
            pass
    toolchain_file = game_dir / "lean-toolchain"
    toolchain = (
        toolchain_file.read_text(encoding="utf-8").strip()
        if toolchain_file.exists()
        else None
    )
    pinned, _warning = game_toolchain(toolchain)
    return "v" + pinned.split(":v", 1)[1], f"lean-toolchain ({toolchain or 'missing'})"


def game_name(game_dir: Path) -> str:
    """URL-safe name for ``/#/g/local/<name>`` (the relay matches ``[\\w.-]+``)."""
    safe = re.sub(r"[^\w.-]+", "-", game_dir.resolve().name).strip("-")
    return safe or "game"


def cache_root() -> Path:
    base = os.environ.get("PROOFQUEST_CACHE") or os.environ.get("XDG_CACHE_HOME")
    return (Path(base).expanduser() if base else Path.home() / ".cache") / "proofquest"


def _looks_like_lean4game(path: Path) -> bool:
    return (
        (path / "client").is_dir()
        and (path / "relay").is_dir()
        and (path / "package.json").is_file()
    )


def _package_rev(package_dir: Path) -> str | None:
    """Short revision of the lake-fetched GameServer checkout, if detectable."""
    try:
        head = (package_dir / ".git" / "HEAD").read_text(encoding="utf-8").strip()
    except OSError:
        return None
    if not head.startswith("ref:"):
        return head[:7]
    ref = package_dir / ".git" / head.removeprefix("ref: ").strip()
    try:
        return ref.read_text(encoding="utf-8").strip()[:7]
    except OSError:
        return None


def _resolve_source(game_dir: Path, lean4game: str | None) -> tuple[Path | None, str]:
    """Locate the pinned lean4game tree to copy the client/relay sources from."""
    if lean4game:
        source = Path(lean4game).expanduser().resolve()
        if not _looks_like_lean4game(source):
            raise ServeError(
                f"--lean4game {source} does not look like a lean4game checkout "
                "(expected client/, relay/ and package.json)"
            )
        return source, f"the --lean4game checkout {source}"
    package = game_dir / ".lake" / "packages" / "GameServer"
    if _looks_like_lean4game(package):
        return package, (
            f"the GameServer dependency already fetched by lake in {package} "
            "(no clone needed)"
        )
    return None, ""


def _codeload_url(ref: str) -> str:
    """Codeload tarball URL for a release tag, branch or commit ref."""
    if _TAG_RE.match(ref):
        return f"https://codeload.github.com/{_LEAN4GAME_REPO}/tar.gz/refs/tags/{ref}"
    if _SHA_RE.fullmatch(ref):
        return f"https://codeload.github.com/{_LEAN4GAME_REPO}/tar.gz/{ref}"
    return f"https://codeload.github.com/{_LEAN4GAME_REPO}/tar.gz/refs/heads/{ref}"


def _tarball_root(members: list[tarfile.TarInfo], ref: str) -> str:
    """Common root directory of a codeload tarball.

    Codeload tarballs start with a ``pax_global_header`` metadata entry (no
    slash, not a directory), which must not be taken for the root.
    """
    roots = {
        member.name.partition("/")[0]
        for member in members
        if "/" in member.name and member.name.partition("/")[0] != "pax_global_header"
    }
    known = next((root for root in roots if root.startswith("lean4game-")), None)
    if known is not None:
        return known + "/"
    if len(roots) == 1:
        return roots.pop() + "/"
    raise ServeError(
        f"the lean4game {ref} tarball has an unexpected layout: {sorted(roots)}"
    )


def _download_pinned(ref: str, target: Path) -> None:
    """Download the lean4game source tarball of the pinned ref into ``target``."""
    url = _codeload_url(ref)
    print(f"downloading pinned lean4game {ref} from GitHub (a versioned download, not a clone):")
    print(f"  {url}")
    try:
        with urllib.request.urlopen(url, timeout=120) as response:
            payload = response.read()
    except OSError as exc:
        raise ServeError(
            f"could not download lean4game {ref}: {exc}\n"
            "the first run needs network access; retry, or point --lean4game at an "
            "existing lean4game checkout"
        ) from exc
    target.mkdir(parents=True, exist_ok=True)
    try:
        with tarfile.open(fileobj=io.BytesIO(payload), mode="r:gz") as tar:
            prefix = _tarball_root(tar.getmembers(), ref)
            for member in tar.getmembers():
                if not member.name.startswith(prefix):
                    continue
                relative = member.name.removeprefix(prefix)
                if not relative.startswith(_COPIED_PATHS):
                    continue
                member.name = relative  # strip the tarball's root directory
                tar.extract(member, target, filter="data")
    except (OSError, tarfile.TarError) as exc:
        raise ServeError(f"could not unpack the lean4game {ref} tarball: {exc}") from exc
    if not _looks_like_lean4game(target):
        raise ServeError(
            f"the lean4game {ref} tarball did not contain client/relay sources"
        )


def _run(cmd: list[str], cwd: Path, env: dict[str, str]) -> None:
    print(f"  $ {' '.join(cmd)}")
    try:
        subprocess.run(cmd, cwd=cwd, env=env, check=True)
    except FileNotFoundError as exc:
        raise ServeError(f"{cmd[0]} not found on PATH; install Node.js/npm first") from exc
    except subprocess.CalledProcessError as exc:
        raise ServeError(
            f"command failed with exit code {exc.returncode}: {' '.join(cmd)}\n"
            "if this was the first run, check your network connection and retry "
            "(the npm dependencies are pinned by package-lock.json and include the "
            "git dependency vscode-lean4, which proofquest fetches with "
            "npm's --allow-git=root)"
        ) from exc


def _cache_key(ref: str, rev: str | None) -> str:
    safe = re.sub(r"[^\w.-]+", "-", ref)
    return f"lean4game-{safe}-{rev}" if rev else f"lean4game-{safe}"


def _is_built(root: Path) -> bool:
    return (root / _RELAY_ENTRY).is_file() and (root / _CLIENT_INDEX).is_file()


def _npm_allow_git(npm: str) -> list[str]:
    """Opt-in flag for npm >= 12, which refuses git dependencies by default.

    lean4game pins one git dependency in its root package.json (vscode-lean4);
    ``--allow-git=root`` allows exactly that. Older npm versions allow git
    dependencies by default and predate the flag, so it is only passed where it
    exists. An unreadable npm lets the install surface its own error.
    """
    try:
        result = subprocess.run(
            [npm, "--version"], capture_output=True, text=True, check=True, timeout=30
        )
    except (OSError, subprocess.SubprocessError):
        return []
    match = re.match(r"^v?(\d+)", result.stdout.strip())
    return ["--allow-git=root"] if match and int(match.group(1)) >= 12 else []


def ensure_runtime(
    game_dir: Path,
    ref: str,
    lean4game: str | None = None,
    rebuild: bool = False,
) -> Path:
    """Return the cached lean4game tree with the client and relay built.

    The tree is pinned by ref (and revision, when known) in the cache, so a
    toolchain change yields a new cache entry instead of version drift.
    """
    source, source_note = _resolve_source(game_dir, lean4game)
    rev = _package_rev(source) if source else None
    root = cache_root() / _cache_key(ref, rev)
    if not rebuild and (root / _READY_MARKER).is_file() and _is_built(root):
        print(f"reusing the cached lean4game {ref} runtime: {root}")
        return root

    if root.exists():
        shutil.rmtree(root)
    root.mkdir(parents=True)
    if not source:
        _download_pinned(ref, root)
    else:
        print(f"preparing the pinned lean4game {ref} runtime in {root}")
        print(f"  source: {source_note}")
        for name in _COPIED_PATHS:
            origin = source / name
            if origin.is_dir():
                shutil.copytree(origin, root / name, ignore=_COPY_IGNORE)
            elif origin.is_file():
                shutil.copy2(origin, root / name)
            else:
                raise ServeError(f"the lean4game tree at {source} is missing {name}")

    npm = shutil.which("npm")
    if npm is None:
        raise ServeError("npm not found on PATH; install Node.js/npm to prepare the client")
    env = dict(os.environ)
    env["CYPRESS_INSTALL_BINARY"] = "0"  # the browser test runner is not needed to serve
    print(
        "installing the pinned npm dependencies (from package-lock.json; a download, not a clone)"
    )
    _run([npm, "ci", *_npm_allow_git(npm), "--no-audit", "--no-fund"], root, env)
    print("building the lean4game relay and client (first run only)")
    _run([npm, "run", "build:relay"], root, env)
    _run([npm, "run", "build:client"], root, env)
    if not _is_built(root):
        raise ServeError(
            "the client/relay build finished but the expected artifacts are missing "
            f"({_RELAY_ENTRY}, {_CLIENT_INDEX})"
        )
    (root / _READY_MARKER).write_text(
        json.dumps({"ref": ref, "rev": rev, "prepared_at": time.strftime("%Y-%m-%dT%H:%M:%S")}),
        encoding="utf-8",
    )
    return root


def link_game(root_name: str, game_dir: Path) -> Path:
    """Expose the game where the relay looks for local games.

    The relay resolves ``/#/g/local/<name>`` to a folder next to its own tree,
    mirroring the upstream layout where the game folder is a sibling of the
    lean4game folder; a symlink reproduces that without moving the game.

    The symlink must live directly in the cache root, so a game folder whose
    name looks like a runtime cache entry (``lean4game-v4.X.Y[-rev]``) is
    rejected instead of being silently disambiguated: renaming the folder is
    the honest fix, and the URL name follows the folder name.
    """
    if _CACHE_KEY_RE.match(root_name):
        raise ServeError(
            f"the game folder name {root_name!r} collides with proofquest's runtime "
            f"cache entries in {cache_root()}; rename the game folder (the URL name "
            "follows the folder name)"
        )
    link = cache_root() / root_name
    link.parent.mkdir(parents=True, exist_ok=True)
    target = game_dir.resolve()
    if link.is_symlink():
        if Path(os.readlink(link)) == target:
            return link
        link.unlink()
    elif link.exists():
        raise ServeError(
            f"{link} exists and is not a proofquest-managed symlink; remove it first"
        )
    link.symlink_to(target)
    return link


def wait_until_ready(
    port: int, timeout: float = _READY_TIMEOUT, process: subprocess.Popen | None = None
) -> bool:
    """Poll the relay's HTTP server until it answers 2xx/3xx, or timeout."""
    url = f"http://127.0.0.1:{port}/"
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if process is not None and process.poll() is not None:
            return False  # the relay exited before answering
        try:
            with urllib.request.urlopen(url, timeout=2):
                return True  # urllib raises HTTPError for 4xx/5xx
        except urllib.error.HTTPError:
            time.sleep(0.25)  # up but not serving the client yet: keep polling
        except (urllib.error.URLError, OSError):
            time.sleep(0.25)
    return False


def _free_port() -> int:
    """Ask the OS for a free port (used for the relay's statistics endpoint)."""
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        return sock.getsockname()[1]


def spawn_relay(entry: Path, port: int, cwd: Path) -> subprocess.Popen:
    """Start the lean4game relay (which also serves the built client)."""
    node = shutil.which("node")
    if node is None:
        raise ServeError("node not found on PATH; install Node.js to serve the game")
    if shutil.which("lake") is None:
        print("warning: lake not found on PATH; players will not be able to connect")
    env = dict(os.environ)
    env["NODE_ENV"] = "development"  # enables local games and the un-sandboxed `lake serve`
    env["PORT"] = str(port)
    env["API_PORT"] = str(_free_port())  # stats endpoint (relay reads API_PORT)
    return subprocess.Popen([node, str(entry)], cwd=cwd, env=env, start_new_session=True)


def stop_relay(process: subprocess.Popen) -> None:
    """Terminate the relay and the game-server processes it spawned."""
    if process.poll() is not None:
        return
    try:
        group = os.getpgid(process.pid)
    except (ProcessLookupError, PermissionError):
        group = None
    if os.name == "posix" and group is not None:
        try:
            os.killpg(group, signal.SIGTERM)
            process.wait(timeout=5)
            return
        except (ProcessLookupError, subprocess.TimeoutExpired):
            try:
                os.killpg(group, signal.SIGKILL)
            except ProcessLookupError:
                pass
    process.terminate()
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()


def _port_available(port: int) -> bool:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            sock.bind(("127.0.0.1", port))
        except OSError:
            return False
    return True


def serve(args: argparse.Namespace) -> int:
    """Host ``args.game`` on ``args.port``; blocks until interrupted."""
    game_dir = Path(args.game).expanduser()
    if not game_dir.is_dir():
        raise ServeError(f"game directory {game_dir} does not exist")
    gamedata = game_dir / ".lake" / "gamedata" / "game.json"
    if args.build and not gamedata.is_file():
        lake = shutil.which("lake")
        if lake is None:
            raise ServeError("lake not found on PATH; install elan/lean first")
        print(f"running `lake build` in {game_dir}")
        _run([lake, "build"], game_dir, dict(os.environ))
    if not gamedata.is_file():
        raise ServeError(
            f"{game_dir} is not built: {gamedata} is missing.\n"
            f"run `lake build` in {game_dir} first (fetch the Mathlib cache with "
            "`lake exe cache get` so Mathlib is not rebuilt), or pass --build"
        )

    if not _port_available(args.port):
        raise ServeError(f"port {args.port} is already in use; choose another with --port")

    ref, ref_source = lean4game_ref(game_dir)
    print(f"proofquest serve: hosting {game_dir}")
    print(f"  lean4game artifacts pinned to {ref} (from {ref_source}; never 'latest')")
    root = ensure_runtime(game_dir, ref, lean4game=args.lean4game, rebuild=args.rebuild)

    name = game_name(game_dir)
    link_game(name, game_dir)
    if not _port_available(args.port):  # cheap re-check after the (slow) prepare step
        raise ServeError(f"port {args.port} is already in use; choose another with --port")

    entry = root / _RELAY_ENTRY
    print(f"  starting the lean4game relay: node {entry}")
    process = spawn_relay(entry, args.port, cwd=cache_root())
    try:
        if not wait_until_ready(args.port, process=process):
            stop_relay(process)
            raise ServeError(
                f"the relay did not answer on port {args.port} within {_READY_TIMEOUT:.0f}s"
            )
        print(f"  game ready: http://localhost:{args.port}/#/g/local/{name}")
        print("  (opening a level starts the game's Lean server; Ctrl+C stops hosting)")
        return process.wait()
    except KeyboardInterrupt:
        print("\nstopping the game server...")
        return 0
    finally:
        stop_relay(process)


def cmd_serve(args: argparse.Namespace) -> int:
    """Entry point for the ``serve`` subcommand."""
    try:
        return serve(args)
    except ServeError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
