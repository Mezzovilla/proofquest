"""Tests for ``proofquest serve``.

The node/npm side is exercised through fake ``npm``/``node`` executables put on
PATH: the fake npm materializes the build artifacts, the fake node serves HTTP
on $PORT and exits after ``PQ_FAKE_NODE_LIFETIME`` seconds. This covers the
whole orchestration (cache preparation, game symlink, relay spawn, readiness
poll, shutdown) without a real npm install or network access.
"""

from __future__ import annotations

import argparse
import io
import json
import os
import socket
import tarfile
import threading
import time
import urllib.error
import urllib.request
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path

import pytest

from proofquest.serve import (
    _LEGACY_NODE_VERSION,
    _LEGACY_VENDOR_PINS,
    ServeError,
    _legacy_runtime,
    _npm_allow_git,
    _pack_package_dir,
    _provision_legacy_node,
    _relay_entry,
    ensure_runtime,
    game_name,
    lean4game_ref,
    link_game,
    serve,
    wait_until_ready,
)

FAKE_NPM = """
import os
import sys
from pathlib import Path

args = sys.argv[1:]
if args[:1] == ["--version"]:
    print(os.environ.get("PQ_NPM_VERSION", "12.0.2"))
    raise SystemExit(0)

root = Path.cwd()
log = os.environ.get("PQ_NPM_LOG")
if log:
    with open(log, "a") as fh:
        fh.write(" ".join(args) + chr(10))
if args[:1] == ["ci"]:
    (root / "node_modules").mkdir(exist_ok=True)
elif args[:2] == ["run", "build:relay"]:
    entry = root / "relay/dist/src/index.js"
    entry.parent.mkdir(parents=True, exist_ok=True)
    entry.write_text("// relay" + chr(10))
elif args[:2] == ["run", "build:client"]:
    index = root / "client/dist/index.html"
    index.parent.mkdir(parents=True, exist_ok=True)
    index.write_text("<html>client</html>")
"""

FAKE_NODE = """
import os
import threading
from http.server import BaseHTTPRequestHandler, HTTPServer


class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        body = b"proofquest-fake-game"
        self.send_response(200)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, *args):
        pass


server = HTTPServer(("127.0.0.1", int(os.environ["PORT"])), Handler)
lifetime = float(os.environ.get("PQ_FAKE_NODE_LIFETIME", "2"))
if lifetime > 0:
    threading.Timer(lifetime, server.shutdown).start()
server.serve_forever()
"""


@pytest.fixture
def fake_bin(tmp_path, monkeypatch):
    bin_dir = tmp_path / "fakebin"
    bin_dir.mkdir()
    for name, body in (("npm", FAKE_NPM), ("node", FAKE_NODE)):
        script = bin_dir / name
        script.write_text("#!/usr/bin/env python3" + chr(10) + body)
        script.chmod(0o755)
    monkeypatch.setenv("PATH", str(bin_dir) + os.pathsep + os.environ["PATH"])
    return bin_dir


def make_lean4game(root: Path) -> Path:
    """A minimal fake lean4game tree with the paths serve() copies."""
    (root / "client/src").mkdir(parents=True)
    (root / "relay/src").mkdir(parents=True)
    (root / "server").mkdir(parents=True)
    (root / "package.json").write_text("{}\n")
    (root / "package-lock.json").write_text("{}\n")
    (root / "client/package.json").write_text("{}\n")
    (root / "client/src/index.ts").write_text("// client\n")
    (root / "relay/package.json").write_text("{}\n")
    (root / "relay/src/index.ts").write_text("// relay\n")
    (root / "server/lakefile.lean").write_text("not needed\n")
    return root


def tarball(root: str = "lean4game-v4.31.0", pax_header: bool = True) -> bytes:
    """An in-memory lean4game source tarball as codeload would serve it.

    Real codeload tarballs start with a ``pax_global_header`` metadata entry
    before the actual ``<repo>-<ref>/`` members.
    """
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w:gz") as tar:
        if pax_header:
            blob = (
                b"52 comment=lean4game-32429782f822085e28dbc2fb576f33eb00e93220\n"
            )
            info = tarfile.TarInfo("pax_global_header")
            info.size = len(blob)
            tar.addfile(info, io.BytesIO(blob))
        for name, data in [
            (f"{root}/package.json", b"{}"),
            (f"{root}/package-lock.json", b"{}"),
            (f"{root}/client/package.json", b"{}"),
            (f"{root}/client/src/index.ts", b"// client"),
            (f"{root}/relay/package.json", b"{}"),
            (f"{root}/relay/src/index.ts", b"// relay"),
            (f"{root}/server/lakefile.lean", b"not needed"),
            (f"{root}/README.md", b"not copied"),
        ]:
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tar.addfile(info, io.BytesIO(data))
    return buffer.getvalue()


def free_port() -> int:
    with socket.socket() as sock:
        sock.bind(("127.0.0.1", 0))
        return sock.getsockname()[1]


def test_lean4game_ref_falls_back_to_toolchain(tmp_path):
    game = tmp_path / "game"
    game.mkdir()
    (game / "lean-toolchain").write_text("leanprover/lean4:v4.32.2\n")
    ref, source = lean4game_ref(game)
    assert ref == "v4.31.0"  # newest lean4game release at or below the toolchain
    assert "lean-toolchain" in source


def test_lean4game_ref_from_lake_manifest(tmp_path):
    game = tmp_path / "game"
    game.mkdir()
    manifest = {
        "packages": [
            {"name": "mathlib", "inputRev": "v4.31.0"},
            {"name": "GameServer", "inputRev": "v4.31.0"},
        ]
    }
    (game / "lake-manifest.json").write_text(json.dumps(manifest))
    ref, source = lean4game_ref(game)
    assert ref == "v4.31.0"
    assert "lake-manifest.json" in source


def test_lean4game_ref_uses_non_tag_revision(tmp_path):
    """A branch/commit inputRev is used as-is for downloads, with a warning."""
    game = tmp_path / "game"
    game.mkdir()
    (game / "lean-toolchain").write_text("leanprover/lean4:v4.31.0\n")
    manifest = {"packages": [{"name": "GameServer", "inputRev": "main"}]}
    (game / "lake-manifest.json").write_text(json.dumps(manifest))
    ref, source = lean4game_ref(game)
    assert ref == "main"  # what the game was actually built against
    assert "inputRev main" in source and "may move" in source


def test_lean4game_ref_survives_malformed_manifest(tmp_path):
    game = tmp_path / "game"
    game.mkdir()
    (game / "lean-toolchain").write_text("leanprover/lean4:v4.31.0\n")
    (game / "lake-manifest.json").write_text('{"packages": "not-a-list"}')
    ref, source = lean4game_ref(game)
    assert ref == "v4.31.0"  # falls back to the toolchain instead of crashing
    assert "lean-toolchain" in source


def test_game_name_is_url_safe(tmp_path):
    weird = tmp_path / "my strange:game?"
    weird.mkdir()
    assert game_name(weird) == "my-strange-game"


def test_ensure_runtime_builds_once_then_reuses(fake_bin, tmp_path, monkeypatch, capsys):
    monkeypatch.setenv("PROOFQUEST_CACHE", str(tmp_path / "cache"))
    log = tmp_path / "npm-log.txt"
    monkeypatch.setenv("PQ_NPM_LOG", str(log))
    source = make_lean4game(tmp_path / "lean4game")

    root = ensure_runtime(Path("."), "v4.31.0", lean4game=str(source))
    assert (root / "relay/dist/src/index.js").is_file()
    assert (root / "client/dist/index.html").is_file()
    assert (root / "client/src/index.ts").is_file()  # sources were copied
    assert (root / ".proofquest-serve-ready").is_file()
    assert log.read_text().count("ci --allow-git=root --no-audit --no-fund") == 1

    assert ensure_runtime(Path("."), "v4.31.0", lean4game=str(source)) == root
    # warm cache: npm skipped entirely
    assert log.read_text().count("ci --allow-git=root --no-audit --no-fund") == 1
    assert "reusing the cached lean4game" in capsys.readouterr().out


def test_ensure_runtime_rebuild_flag(fake_bin, tmp_path, monkeypatch):
    monkeypatch.setenv("PROOFQUEST_CACHE", str(tmp_path / "cache"))
    monkeypatch.setenv("PQ_NPM_LOG", str(tmp_path / "npm-log.txt"))
    source = make_lean4game(tmp_path / "lean4game")

    ensure_runtime(Path("."), "v4.31.0", lean4game=str(source))
    ensure_runtime(Path("."), "v4.31.0", lean4game=str(source), rebuild=True)
    log = (tmp_path / "npm-log.txt").read_text()
    assert log.count("ci --allow-git=root --no-audit --no-fund") == 2
    assert "build:relay" in log and "build:client" in log


def test_download_pinned_tag(fake_bin, tmp_path, monkeypatch):
    requested = []

    def fake_urlopen(url, timeout=None):
        requested.append(url)
        return io.BytesIO(tarball())

    monkeypatch.setattr("proofquest.serve.urllib.request.urlopen", fake_urlopen)
    monkeypatch.setenv("PROOFQUEST_CACHE", str(tmp_path / "cache"))
    monkeypatch.setenv("PQ_NPM_LOG", str(tmp_path / "npm-log.txt"))

    root = ensure_runtime(Path("."), "v4.31.0")
    assert (root / "client/src/index.ts").is_file()
    assert (root / "relay/src/index.ts").is_file()
    assert not (root / "server").exists()  # only serving-relevant paths unpacked
    assert requested == [
        "https://codeload.github.com/leanprover-community/lean4game/tar.gz/refs/tags/v4.31.0"
    ]


def test_download_failure_is_actionable(tmp_path, monkeypatch):
    def fake_urlopen(url, timeout=None):
        raise OSError("connection refused")

    monkeypatch.setattr("proofquest.serve.urllib.request.urlopen", fake_urlopen)
    monkeypatch.setenv("PROOFQUEST_CACHE", str(tmp_path / "cache"))
    with pytest.raises(ServeError, match="network|lean4game checkout"):
        ensure_runtime(Path("."), "v4.31.0")


def test_link_game_retargets(tmp_path, monkeypatch):
    monkeypatch.setenv("PROOFQUEST_CACHE", str(tmp_path / "cache"))
    first = tmp_path / "games" / "one"
    second = tmp_path / "games" / "two"
    first.mkdir(parents=True)
    second.mkdir(parents=True)

    link = link_game("game", first)
    assert link.resolve() == first.resolve()
    link = link_game("game", second)
    assert link.resolve() == second.resolve()


def test_serve_end_to_end(fake_bin, tmp_path, monkeypatch):
    """serve() prepares the pinned runtime, starts the relay and serves HTTP 200."""
    game_dir = tmp_path / "game"
    (game_dir / ".lake" / "gamedata").mkdir(parents=True)
    (game_dir / ".lake" / "gamedata" / "game.json").write_text("{}\n")
    source = make_lean4game(tmp_path / "lean4game")
    monkeypatch.setenv("PROOFQUEST_CACHE", str(tmp_path / "cache"))
    monkeypatch.setenv("PQ_NPM_LOG", str(tmp_path / "npm-log.txt"))
    monkeypatch.setenv("PQ_FAKE_NODE_LIFETIME", "2")

    port = free_port()
    outcome = {}

    def run():
        args = argparse.Namespace(
            game=str(game_dir), port=port, lean4game=str(source), rebuild=False, build=False
        )
        try:
            outcome["code"] = serve(args)
        except (ServeError, OSError) as exc:  # surfaced by the assertion below
            outcome["error"] = repr(exc)

    thread = threading.Thread(target=run, daemon=True)
    thread.start()

    deadline = time.monotonic() + 30
    body = None
    while time.monotonic() < deadline:
        try:
            with urllib.request.urlopen(f"http://127.0.0.1:{port}/", timeout=2) as response:
                assert response.status == 200
                body = response.read()
                break
        except (urllib.error.URLError, OSError):
            time.sleep(0.05)
    assert body == b"proofquest-fake-game", "the relay never answered on the game page"

    thread.join(timeout=20)
    assert not thread.is_alive(), "serve() did not return after the relay exited"
    assert outcome.get("code") == 0, outcome


def test_download_sha_revision(fake_bin, tmp_path, monkeypatch):
    """A commit-sha inputRev downloads the commit tarball, not a tag."""
    sha = "32429782f822085e28dbc2fb576f33eb00e93220"
    requested = []

    def fake_urlopen(url, timeout=None):
        requested.append(url)
        return io.BytesIO(tarball(root=f"lean4game-{sha}"))

    monkeypatch.setattr("proofquest.serve.urllib.request.urlopen", fake_urlopen)
    monkeypatch.setenv("PROOFQUEST_CACHE", str(tmp_path / "cache"))
    monkeypatch.setenv("PQ_NPM_LOG", str(tmp_path / "npm-log.txt"))

    root = ensure_runtime(Path("."), sha)
    assert (root / "client/src/index.ts").is_file()
    assert requested == [
        f"https://codeload.github.com/leanprover-community/lean4game/tar.gz/{sha}"
    ]


def test_download_unexpected_layout(tmp_path, monkeypatch):
    def fake_urlopen(url, timeout=None):
        buffer = io.BytesIO()
        with tarfile.open(fileobj=buffer, mode="w:gz") as tar:
            for name in ("one/client/package.json", "two/relay/package.json"):
                info = tarfile.TarInfo(name)
                info.size = 2
                tar.addfile(info, io.BytesIO(b"{}"))
        return io.BytesIO(buffer.getvalue())

    monkeypatch.setattr("proofquest.serve.urllib.request.urlopen", fake_urlopen)
    monkeypatch.setenv("PROOFQUEST_CACHE", str(tmp_path / "cache"))
    with pytest.raises(ServeError, match="unexpected layout"):
        ensure_runtime(Path("."), "v4.31.0")


def flaky_http_server(failures: int):
    """An HTTP server answering 503 for the first ``failures`` requests, then 200."""
    state = {"remaining": failures}

    class Handler(BaseHTTPRequestHandler):
        def do_GET(self):
            state["remaining"] -= 1
            self.send_response(200 if state["remaining"] < 0 else 503)
            self.send_header("Content-Length", "0")
            self.end_headers()

        def log_message(self, *args):
            pass

    server = HTTPServer(("127.0.0.1", 0), Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    return server, thread


def test_wait_until_ready_retries_server_errors():
    server, thread = flaky_http_server(failures=2)
    try:
        assert wait_until_ready(server.server_address[1], timeout=10) is True
    finally:
        server.shutdown()
        thread.join(timeout=5)


def test_wait_until_ready_rejects_persistent_server_errors():
    server, thread = flaky_http_server(failures=10**9)
    try:
        assert wait_until_ready(server.server_address[1], timeout=1.0) is False
    finally:
        server.shutdown()
        thread.join(timeout=5)


@pytest.mark.parametrize(
    "ref",
    ["v4.31.0", "32429782f822085e28dbc2fb576f33eb00e93220", "main"],
    ids=["tag", "sha", "branch"],
)
def test_link_game_rejects_cache_key_collision(ref, tmp_path, monkeypatch):
    """Any ``lean4game-*`` folder name collides with a runtime cache entry."""
    monkeypatch.setenv("PROOFQUEST_CACHE", str(tmp_path / "cache"))
    game = tmp_path / f"lean4game-{ref}"
    game.mkdir()
    with pytest.raises(ServeError, match="collides"):
        link_game(f"lean4game-{ref}", game)


def test_serve_checks_port_before_building_runtime(fake_bin, tmp_path, monkeypatch):
    """A busy port fails fast, before the expensive npm prepare step."""
    game_dir = tmp_path / "game"
    (game_dir / ".lake" / "gamedata").mkdir(parents=True)
    (game_dir / ".lake" / "gamedata" / "game.json").write_text("{}\n")
    source = make_lean4game(tmp_path / "lean4game")
    monkeypatch.setenv("PROOFQUEST_CACHE", str(tmp_path / "cache"))
    log = tmp_path / "npm-log.txt"
    monkeypatch.setenv("PQ_NPM_LOG", str(log))

    with socket.socket() as blocker:
        blocker.bind(("127.0.0.1", 0))
        blocker.listen(1)
        args = argparse.Namespace(
            game=str(game_dir),
            port=blocker.getsockname()[1],
            lean4game=str(source),
            rebuild=False,
            build=False,
        )
        with pytest.raises(ServeError, match="already in use"):
            serve(args)
    assert not log.exists(), "npm ran even though the port was busy"


def test_npm_allow_git_guard(fake_bin, tmp_path, monkeypatch):
    npm = str(tmp_path / "fakebin" / "npm")
    monkeypatch.setenv("PQ_NPM_VERSION", "12.0.2")
    assert _npm_allow_git(npm) == ["--allow-git=root"]
    monkeypatch.setenv("PQ_NPM_VERSION", "9.6.3")  # flag predates npm 12's default
    assert _npm_allow_git(npm) == []
    monkeypatch.setenv("PQ_NPM_VERSION", "v11.5.1")
    assert _npm_allow_git(npm) == []


def test_npm_allow_git_guard_tolerates_broken_npm(tmp_path):
    broken = tmp_path / "npm"
    broken.write_text("#!/usr/bin/env python3\nraise SystemExit(1)\n")
    broken.chmod(0o755)
    assert _npm_allow_git(str(broken)) == []


def test_ensure_runtime_skips_allow_git_on_old_npm(fake_bin, tmp_path, monkeypatch):
    monkeypatch.setenv("PQ_NPM_VERSION", "9.6.3")
    monkeypatch.setenv("PROOFQUEST_CACHE", str(tmp_path / "cache"))
    log = tmp_path / "npm-log.txt"
    monkeypatch.setenv("PQ_NPM_LOG", str(log))
    source = make_lean4game(tmp_path / "lean4game")

    ensure_runtime(Path("."), "v4.31.0", lean4game=str(source))
    log_text = log.read_text()
    assert "ci --no-audit --no-fund" in log_text  # npm < 12: no flag needed
    assert "--allow-git" not in log_text


def test_serve_refuses_unbuilt_game(tmp_path, monkeypatch):
    game = tmp_path / "game"
    game.mkdir()  # exists but was never built
    args = argparse.Namespace(
        game=str(game), port=free_port(), lean4game=None, rebuild=False, build=False
    )
    with pytest.raises(ServeError, match="lake build"):
        serve(args)


FAKE_NODE_LEGACY = """\
import http.server
import os
import sys

if "--version" in sys.argv:
    print("VERSION_HERE")
    sys.exit(0)
port = int(os.environ.get("PORT", "3999"))
http.server.ThreadingHTTPServer(
    ("127.0.0.1", port), http.server.SimpleHTTPRequestHandler
).serve_forever()
"""

FAKE_NPM_LEGACY = """\
import os
import sys

args = sys.argv[1:]
if args[:2] == ["run", "build_client"]:
    os.makedirs("client/dist", exist_ok=True)
    open("client/dist/index.html", "w").write("<html>legacy</html>")
log = os.environ.get("PQ_NPM_LOG")
if log:
    with open(log, "a") as fh:
        fh.write(" ".join(args) + "\\n")
"""

LEGACY_LOCK = {
    "name": "lean4game",
    "version": "4.7.0",
    "lockfileVersion": 3,
    "requires": True,
    "packages": {
        "": {
            "name": "lean4game",
            "version": "4.7.0",
            "dependencies": {
                "express": "^4.18.2",
                "lean4-infoview": "https://gitpkg.now.sh/leanprover/vscode-lean4"
                "/lean4-infoview?de0062c",
                "lean4web": "github:hhu-adam/lean4web"
                "#414d9e62638a392fca278761b4c61a1d2e138bc7",
            },
        },
        "node_modules/express": {
            "version": "4.18.2",
            "resolved": "https://registry.npmjs.org/express/-/express-4.18.2.tgz",
            "integrity": "sha512-EXPRESS",
        },
        "node_modules/lean4": {
            "version": "0.0.119",
            "resolved": "https://gitpkg.now.sh/leanprover/vscode-lean4"
            "/vscode-lean4?8d0cc34dcfa00da8b4a48394ba1fb3a600e3f985",
            "integrity": "sha512-OLD-lean4",
        },
        "node_modules/lean4-infoview": {
            "version": "0.4.2",
            "resolved": "https://gitpkg.now.sh/leanprover/vscode-lean4"
            "/lean4-infoview?de0062c",
            "integrity": "sha512-OLD-infoview",
        },
        "node_modules/lean4web": {
            "version": "0.1.0",
            "resolved": "git+ssh://git@github.com/hhu-adam/lean4web.git"
            "#414d9e62638a392fca278761b4c61a1d2e138bc7",
            "integrity": "sha512-OLD-lean4web",
            "dependencies": {
                "express": "^4.18.2",
                "lean4": "https://gitpkg.now.sh/leanprover/vscode-lean4"
                "/vscode-lean4?8d0cc34dcfa00da8b4a48394ba1fb3a600e3f985",
            },
        },
    },
}

LEGACY_PACKAGE_JSON = {
    "name": "lean4game",
    "version": "4.7.0",
    "private": True,
    "scripts": {
        "build_client": "vite build",
        "build_server": "cd server && lake build",
        "start": "node relay/index.mjs",
    },
    "dependencies": LEGACY_LOCK["packages"][""]["dependencies"],
}


def _tar_bytes(entries: dict, mode: str = "w:gz") -> bytes:
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode=mode) as tar:
        for name, data in sorted(entries.items()):
            info = tarfile.TarInfo(name)
            info.size = len(data)
            info.mode = 0o755 if name.endswith(("/node", "/npm")) else 0o644
            tar.addfile(info, io.BytesIO(data))
    return buf.getvalue()


def make_legacy_lean4game(root: Path) -> Path:
    source = root / "lean4game-legacy"
    (source / "relay").mkdir(parents=True)
    (source / "relay" / "index.mjs").write_text(
        "import { WebSocketServer } from 'ws';\n"
        "router.get('/import/status/:owner/:repo', importStatus)\n"
        "router.get('/import/trigger/:owner/:repo', importTrigger)\n"
        "  .listen(PORT, () => console.log(`Listening on ${PORT}`));\n"
        "const wss = new WebSocketServer({ server })\n"
    )
    (source / "client" / "src").mkdir(parents=True)
    (source / "client" / "src" / "main.ts").write_text("//\n")
    (source / "package.json").write_text(json.dumps(LEGACY_PACKAGE_JSON))
    (source / "package-lock.json").write_text(json.dumps(LEGACY_LOCK))
    for name in ("index.html", "vite.config.ts", "tsconfig.json", "env.d.ts"):
        (source / name).write_text(f"// {name}\n")
    return source


def _node_dist_payload() -> tuple:
    import hashlib
    import platform as _platform
    import sys as _sys

    osname = {"linux": "linux", "darwin": "darwin"}[_sys.platform]
    arch = {"x86_64": "x64", "aarch64": "arm64", "arm64": "arm64"}[
        _platform.machine().lower()
    ]
    dist = f"node-{_LEGACY_NODE_VERSION}-{osname}-{arch}"
    payload = _tar_bytes(
        {
            f"{dist}/bin/node": (
                "#!/usr/bin/env python3\n"
                + FAKE_NODE_LEGACY.replace("VERSION_HERE", _LEGACY_NODE_VERSION)
            ).encode(),
            f"{dist}/bin/npm": (
                "#!/usr/bin/env python3\n" + FAKE_NPM_LEGACY
            ).encode(),
        },
        mode="w:xz",
    )
    sums = f"{hashlib.sha256(payload).hexdigest()}  {dist}.tar.xz\n".encode()
    return dist, payload, sums


def _vendor_payloads() -> dict:
    payloads = {}
    for pin in _LEGACY_VENDOR_PINS:
        rootname = f"{pin.repo.split('/')[-1]}-{pin.sha}"
        manifest = {"name": pin.package_name, "version": pin.version}
        if pin.dep == "lean4web":
            manifest["dependencies"] = {
                "lean4": "https://gitpkg.now.sh/leanprover/vscode-lean4"
                "/vscode-lean4?8d0cc34dcfa00da8b4a48394ba1fb3a600e3f985"
            }
        prefix = f"{rootname}/{pin.subdir}/" if pin.subdir else f"{rootname}/"
        payloads[(pin.repo, pin.sha)] = _tar_bytes(
            {
                f"{prefix}package.json": json.dumps(manifest).encode(),
                f"{prefix}src/index.ts": b"// source\n",
                f"{prefix}LICENSE": b"MIT\n",
            }
        )
    return payloads


def _fake_urlopen_factory(node_payload=None, node_sums=b"", vendors=None):
    vendors = vendors if vendors is not None else _vendor_payloads()

    def fake_urlopen(url, timeout=None):
        if url.endswith("SHASUMS256.txt"):
            return io.BytesIO(node_sums)
        if url.endswith(".tar.xz"):
            return io.BytesIO(node_payload)
        for (repo, sha), payload in vendors.items():
            if repo in url and sha in url:
                return io.BytesIO(payload)
        raise AssertionError(f"unexpected urlopen {url}")

    return fake_urlopen


def test_legacy_prepare(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    _dist, node_payload, node_sums = _node_dist_payload()
    monkeypatch.setattr(
        "proofquest.serve.urllib.request.urlopen",
        _fake_urlopen_factory(node_payload, node_sums),
    )
    source = make_legacy_lean4game(tmp_path)
    assert _legacy_runtime(source)

    npm_log = tmp_path / "npm.log"
    monkeypatch.setenv("PQ_NPM_LOG", str(npm_log))
    root = ensure_runtime(tmp_path, "v4.7.0", lean4game=str(source))

    assert root.name.endswith("-compat1")
    assert (root / "relay" / "index.mjs").is_file()
    assert not (root / "relay" / "dist" / "src" / "index.js").exists()
    for name in ("index.html", "vite.config.ts", "tsconfig.json", "env.d.ts"):
        assert (root / name).is_file(), name
    assert _relay_entry(root) == Path("relay/index.mjs")

    lines = npm_log.read_text().splitlines()
    assert any(line.startswith("ci ") for line in lines)
    assert "run build_client" in lines
    assert not any("build_server" in line or "build:relay" in line for line in lines)

    marker = json.loads((root / ".proofquest-serve-ready").read_text())
    assert marker["compat"] == "compat1"
    assert marker["node"] == _LEGACY_NODE_VERSION
    assert marker["host"] == "127.0.0.1"
    assert marker["policy"] == "local-only-v1"
    relay_text = (root / "relay" / "index.mjs").read_text()
    assert ".listen(PORT, '127.0.0.1'," in relay_text
    assert "new WebSocketServer({ server })" not in relay_text
    assert "verifyClient: ({ origin }) => !origin || localOrigins.has(origin)" in relay_text
    assert relay_text.count("(_req, res) => res.sendStatus(404)") == 2
    assert "importStatus)" not in relay_text
    assert "importTrigger)" not in relay_text
    assert set(marker["vendor"]) == {"lean4", "lean4-infoview", "lean4web"}
    assert all(
        marker["vendor"][pin.dep]["sha"] == pin.sha for pin in _LEGACY_VENDOR_PINS
    )

    manifest = json.loads((root / "package.json").read_text())
    assert manifest["dependencies"]["lean4-infoview"].startswith("file:vendor/")
    assert manifest["dependencies"]["lean4web"].startswith("file:vendor/")
    assert manifest["dependencies"]["express"] == "^4.18.2"

    lock_text = (root / "package-lock.json").read_text()
    assert "gitpkg" not in lock_text and "git+ssh" not in lock_text
    lock = json.loads(lock_text)
    express = lock["packages"]["node_modules/express"]
    assert express["version"] == "4.18.2"
    assert express["resolved"].endswith("express-4.18.2.tgz")
    assert express["integrity"] == "sha512-EXPRESS"
    for pin in _LEGACY_VENDOR_PINS:
        entry = lock["packages"][f"node_modules/{pin.dep}"]
        assert entry["resolved"].startswith("file:")
        assert entry["integrity"].startswith("sha512-")
        assert "OLD" not in entry["integrity"]

    for pin in _LEGACY_VENDOR_PINS:
        tarball = root / "vendor" / pin.tarball
        assert tarball.is_file()
        with tarfile.open(tarball, "r:gz") as tar:
            names = tar.getnames()
        assert "package/package.json" in names
        assert "package/src/index.ts" in names
        assert "package/LICENSE" in names
    with tarfile.open(root / "vendor" / "lean4web-0.1.0.tgz", "r:gz") as tar:
        patched = json.loads(tar.extractfile("package/package.json").read())
    assert patched["dependencies"]["lean4"].startswith("file:")
    assert patched["dependencies"]["lean4"].endswith("lean4-0.0.119.tgz")


def test_legacy_prepare_reuses_ready_cache(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    _dist, node_payload, node_sums = _node_dist_payload()
    calls = []

    def counting_urlopen(url, timeout=None):
        calls.append(url)
        return _fake_urlopen_factory(node_payload, node_sums)(url, timeout)

    monkeypatch.setattr("proofquest.serve.urllib.request.urlopen", counting_urlopen)
    source = make_legacy_lean4game(tmp_path)
    first = ensure_runtime(tmp_path, "v4.7.0", lean4game=str(source))
    calls.clear()
    second = ensure_runtime(tmp_path, "v4.7.0", lean4game=str(source))
    assert second == first
    assert calls == []


def test_legacy_prepare_never_rewrites_partial_cache(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    _dist, node_payload, node_sums = _node_dist_payload()
    source = make_legacy_lean4game(tmp_path)
    bad = dict(_vendor_payloads())
    pin = next(p for p in _LEGACY_VENDOR_PINS if p.dep == "lean4web")
    rootname = f"{pin.repo.split('/')[-1]}-{pin.sha}"
    bad[(pin.repo, pin.sha)] = _tar_bytes(
        {
            f"{rootname}/package.json": json.dumps(
                {
                    "name": "lean4web",
                    "version": "9.9.9",
                    "dependencies": {"lean4": "https://gitpkg.now.sh/x"},
                }
            ).encode()
        }
    )
    monkeypatch.setattr(
        "proofquest.serve.urllib.request.urlopen",
        _fake_urlopen_factory(node_payload, node_sums, vendors=bad),
    )
    with pytest.raises(ServeError, match="does not match the pinned package"):
        ensure_runtime(tmp_path, "v4.7.0", lean4game=str(source))
    cache = tmp_path / "cache" / "proofquest"
    partial = cache / "lean4game-v4.7.0-compat1"
    assert partial.is_dir()
    monkeypatch.setattr(
        "proofquest.serve.urllib.request.urlopen",
        _fake_urlopen_factory(node_payload, node_sums),
    )
    fixed = ensure_runtime(tmp_path, "v4.7.0", lean4game=str(source))
    assert fixed.name == "lean4game-v4.7.0-compat1-2"
    assert partial.is_dir()


def test_legacy_ignores_old_patched_cache(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    old = tmp_path / "cache" / "proofquest" / "lean4game-v4.7.0"
    (old / "relay" / "dist" / "src").mkdir(parents=True)
    (old / "relay" / "dist" / "src" / "index.js").write_text("// shim\n")
    (old / "relay" / "index.mjs").write_text("// raw\n")
    (old / "client" / "dist").mkdir(parents=True)
    (old / "client" / "dist" / "index.html").write_text("<html></html>")
    (old / "package.json").write_text(json.dumps(LEGACY_PACKAGE_JSON))
    (old / ".proofquest-serve-ready").write_text("{}")

    _dist, node_payload, node_sums = _node_dist_payload()
    monkeypatch.setattr(
        "proofquest.serve.urllib.request.urlopen",
        _fake_urlopen_factory(node_payload, node_sums),
    )
    source = make_legacy_lean4game(tmp_path)
    root = ensure_runtime(tmp_path, "v4.7.0", lean4game=str(source))
    assert root.name.endswith("-compat1")
    assert root != old


def test_legacy_node_hash_mismatch(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    dist, node_payload, _ = _node_dist_payload()
    bad_sums = f"{'0' * 64}  {dist}.tar.xz\n".encode()
    monkeypatch.setattr(
        "proofquest.serve.urllib.request.urlopen",
        _fake_urlopen_factory(node_payload, bad_sums),
    )
    source = make_legacy_lean4game(tmp_path)
    with pytest.raises(ServeError, match="SHA256 mismatch"):
        ensure_runtime(tmp_path, "v4.7.0", lean4game=str(source))
    assert not (tmp_path / "cache" / "proofquest" / dist).exists()


def test_legacy_node_traversal_rejected(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    dist, _, _ = _node_dist_payload()
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:xz") as tar:
        info = tarfile.TarInfo(f"{dist}/../evil")
        info.size = 3
        tar.addfile(info, io.BytesIO(b"bad"))
    payload = buf.getvalue()
    import hashlib

    sums = f"{hashlib.sha256(payload).hexdigest()}  {dist}.tar.xz\n".encode()
    monkeypatch.setattr(
        "proofquest.serve.urllib.request.urlopen",
        _fake_urlopen_factory(payload, sums),
    )
    source = make_legacy_lean4game(tmp_path)
    with pytest.raises(ServeError, match="escapes"):
        ensure_runtime(tmp_path, "v4.7.0", lean4game=str(source))


def test_legacy_node_external_symlink_rejected(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    dist, _, _ = _node_dist_payload()
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:xz") as tar:
        info = tarfile.TarInfo(f"{dist}/bin/link")
        info.type = tarfile.SYMTYPE
        info.linkname = "/etc/passwd"
        tar.addfile(info)
    payload = buf.getvalue()
    import hashlib

    sums = f"{hashlib.sha256(payload).hexdigest()}  {dist}.tar.xz\n".encode()
    monkeypatch.setattr(
        "proofquest.serve.urllib.request.urlopen",
        _fake_urlopen_factory(payload, sums),
    )
    with pytest.raises(ServeError, match="points outside"):
        _provision_legacy_node()
    assert not (tmp_path / "cache" / "proofquest" / dist).exists()


def test_pack_rejects_external_symlink(tmp_path):
    source = tmp_path / "pkg"
    source.mkdir()
    (source / "real.txt").write_text("x")
    (source / "link").symlink_to("/etc/passwd")
    with pytest.raises(ServeError, match="links outside"):
        _pack_package_dir(source, tmp_path / "out" / "x.tgz")


def test_pack_allows_internal_symlink(tmp_path):
    source = tmp_path / "pkg"
    source.mkdir()
    (source / "real.txt").write_text("x")
    (source / "link").symlink_to("real.txt")
    integrity = _pack_package_dir(source, tmp_path / "out" / "x.tgz")
    assert integrity.startswith("sha512-")
    with tarfile.open(tmp_path / "out" / "x.tgz", "r:gz") as tar:
        member = tar.getmember("package/link")
        assert member.issym() and member.linkname == "real.txt"


def test_relay_entry_prefers_modern(tmp_path):
    root = tmp_path / "rt"
    (root / "relay" / "dist" / "src").mkdir(parents=True)
    (root / "relay" / "dist" / "src" / "index.js").write_text("//\n")
    (root / "relay" / "index.mjs").write_text("//\n")
    assert _relay_entry(root) == Path("relay/dist/src/index.js")
    (root / "relay" / "dist" / "src" / "index.js").unlink()
    assert _relay_entry(root) == Path("relay/index.mjs")


def test_modern_tree_not_legacy(tmp_path):
    source = make_lean4game(tmp_path / "lean4game")
    assert not _legacy_runtime(source)


def _legacy_prep(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    _dist, node_payload, node_sums = _node_dist_payload()
    monkeypatch.setattr(
        "proofquest.serve.urllib.request.urlopen",
        _fake_urlopen_factory(node_payload, node_sums),
    )
    source = make_legacy_lean4game(tmp_path)
    return ensure_runtime(tmp_path, "v4.7.0", lean4game=str(source))


@pytest.mark.parametrize(
    "corrupt",
    [
        lambda m: m.update(node="v99.0.0"),
        lambda m: m.pop("host"),
        lambda m: m["vendor"]["lean4"].update(integrity="sha512-bogus"),
        lambda m: m["vendor"]["lean4"].update(sha="0" * 40),
        lambda m: m.pop("vendor"),
        lambda m: m.update(ref="v4.8.0"),
        lambda m: m["vendor"]["lean4"].update(tarball="other.tgz"),
        lambda m: m.update(policy="unsafe"),
        lambda m: m.pop("policy"),
    ],
)
def test_legacy_ready_rejects_bad_marker(tmp_path, monkeypatch, corrupt):
    root = _legacy_prep(tmp_path, monkeypatch)
    marker_path = root / ".proofquest-serve-ready"
    data = json.loads(marker_path.read_text())
    corrupt(data)
    marker_path.write_text(json.dumps(data))
    fresh = ensure_runtime(tmp_path, "v4.7.0", lean4game=str(tmp_path / "lean4game-legacy"))
    assert fresh != root
    assert root.is_dir()


def test_legacy_ready_rejects_missing_tarball(tmp_path, monkeypatch):
    root = _legacy_prep(tmp_path, monkeypatch)
    (root / "vendor" / "lean4-0.0.119.tgz").unlink()
    fresh = ensure_runtime(tmp_path, "v4.7.0", lean4game=str(tmp_path / "lean4game-legacy"))
    assert fresh != root


def test_legacy_ready_rejects_tampered_tarball(tmp_path, monkeypatch):
    root = _legacy_prep(tmp_path, monkeypatch)
    (root / "vendor" / "lean4-0.0.119.tgz").write_bytes(b"tampered")
    fresh = ensure_runtime(tmp_path, "v4.7.0", lean4game=str(tmp_path / "lean4game-legacy"))
    assert fresh != root


def test_legacy_ready_rejects_missing_host_bind(tmp_path, monkeypatch):
    root = _legacy_prep(tmp_path, monkeypatch)
    marker = root / ".proofquest-serve-ready"
    data = json.loads(marker.read_text())
    del data["host"]
    marker.write_text(json.dumps(data))
    fresh = ensure_runtime(tmp_path, "v4.7.0", lean4game=str(tmp_path / "lean4game-legacy"))
    assert fresh != root


def test_lock_migration_fails_closed_on_wrong_sha(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    _dist, node_payload, node_sums = _node_dist_payload()
    monkeypatch.setattr(
        "proofquest.serve.urllib.request.urlopen",
        _fake_urlopen_factory(node_payload, node_sums),
    )
    source = make_legacy_lean4game(tmp_path)
    lock = json.loads((source / "package-lock.json").read_text())
    lock["packages"]["node_modules/lean4"]["resolved"] = lock["packages"][
        "node_modules/lean4"
    ]["resolved"].replace("8d0cc34dcfa00da8b4a48394ba1fb3a600e3f985", "1" * 40)
    (source / "package-lock.json").write_text(json.dumps(lock))
    with pytest.raises(ServeError, match="unsupported lean4 lockfile pin"):
        ensure_runtime(tmp_path, "v4.7.0", lean4game=str(source))
    partial = tmp_path / "cache" / "proofquest" / "lean4game-v4.7.0-compat1"
    assert json.loads((partial / "package.json").read_text()) == LEGACY_PACKAGE_JSON
    assert "gitpkg" in (partial / "package-lock.json").read_text()


def test_lock_migration_fails_closed_on_wrong_manifest_spec(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    _dist, node_payload, node_sums = _node_dist_payload()
    monkeypatch.setattr(
        "proofquest.serve.urllib.request.urlopen",
        _fake_urlopen_factory(node_payload, node_sums),
    )
    source = make_legacy_lean4game(tmp_path)
    manifest = json.loads((source / "package.json").read_text())
    manifest["dependencies"]["lean4web"] = "github:hhu-adam/lean4web#" + "0" * 40
    (source / "package.json").write_text(json.dumps(manifest))
    with pytest.raises(ServeError, match="unsupported lean4web reference"):
        ensure_runtime(tmp_path, "v4.7.0", lean4game=str(source))
    partial = tmp_path / "cache" / "proofquest" / "lean4game-v4.7.0-compat1"
    assert "github:hhu-adam" in (partial / "package.json").read_text()
    assert "file:vendor" not in (partial / "package.json").read_text()


def test_lock_migration_fails_closed_on_missing_dep(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    _dist, node_payload, node_sums = _node_dist_payload()
    monkeypatch.setattr(
        "proofquest.serve.urllib.request.urlopen",
        _fake_urlopen_factory(node_payload, node_sums),
    )
    source = make_legacy_lean4game(tmp_path)
    manifest = json.loads((source / "package.json").read_text())
    del manifest["dependencies"]["lean4web"]
    (source / "package.json").write_text(json.dumps(manifest))
    with pytest.raises(ServeError, match="unsupported lean4web reference"):
        ensure_runtime(tmp_path, "v4.7.0", lean4game=str(source))


def test_vendor_rejects_wrong_lean4_spec(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    _dist, node_payload, node_sums = _node_dist_payload()
    bad = dict(_vendor_payloads())
    pin = next(p for p in _LEGACY_VENDOR_PINS if p.dep == "lean4web")
    rootname = f"{pin.repo.split('/')[-1]}-{pin.sha}"
    bad[(pin.repo, pin.sha)] = _tar_bytes(
        {
            f"{rootname}/package.json": json.dumps(
                {
                    "name": "lean4web",
                    "version": "0.1.0",
                    "dependencies": {
                        "lean4": "https://gitpkg.now.sh/leanprover/vscode-lean4"
                        "/vscode-lean4?different-sha"
                    },
                }
            ).encode()
        }
    )
    monkeypatch.setattr(
        "proofquest.serve.urllib.request.urlopen",
        _fake_urlopen_factory(node_payload, node_sums, vendors=bad),
    )
    source = make_legacy_lean4game(tmp_path)
    with pytest.raises(ServeError, match="unsupported lean4 reference"):
        ensure_runtime(tmp_path, "v4.7.0", lean4game=str(source))


def test_legacy_relay_missing_bind_line_fails(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    _dist, node_payload, node_sums = _node_dist_payload()
    monkeypatch.setattr(
        "proofquest.serve.urllib.request.urlopen",
        _fake_urlopen_factory(node_payload, node_sums),
    )
    source = make_legacy_lean4game(tmp_path)
    (source / "relay" / "index.mjs").write_text("// no listen line\n")
    with pytest.raises(ServeError, match="does not contain the expected"):
        ensure_runtime(tmp_path, "v4.7.0", lean4game=str(source))


@pytest.mark.parametrize(
    "fragment",
    [
        ".listen(PORT, () => console.log(`Listening on ${PORT}`));",
        "const wss = new WebSocketServer({ server })",
        "router.get('/import/status/:owner/:repo', importStatus)",
        "router.get('/import/trigger/:owner/:repo', importTrigger)",
    ],
)
def test_legacy_relay_missing_fragment_fails(tmp_path, monkeypatch, fragment):
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    _dist, node_payload, node_sums = _node_dist_payload()
    monkeypatch.setattr(
        "proofquest.serve.urllib.request.urlopen",
        _fake_urlopen_factory(node_payload, node_sums),
    )
    source = make_legacy_lean4game(tmp_path)
    relay = source / "relay" / "index.mjs"
    relay.write_text(relay.read_text().replace(fragment, "// removed\n"))
    with pytest.raises(ServeError, match="does not contain the expected"):
        ensure_runtime(tmp_path, "v4.7.0", lean4game=str(source))
    copied = (
        tmp_path / "cache" / "proofquest" / "lean4game-v4.7.0-compat1"
        / "relay" / "index.mjs"
    ).read_text()
    assert "127.0.0.1" not in copied and "verifyClient" not in copied


def test_legacy_ready_rejects_nondict_marker(tmp_path, monkeypatch):
    root = _legacy_prep(tmp_path, monkeypatch)
    for payload in ("null", "[1, 2]", "42", '"text"'):
        (root / ".proofquest-serve-ready").write_text(payload)
        fresh = ensure_runtime(
            tmp_path, "v4.7.0", lean4game=str(tmp_path / "lean4game-legacy")
        )
        assert fresh != root
        (root / ".proofquest-serve-ready").unlink()


def test_pack_deterministic_and_exec_bits(tmp_path):
    source = tmp_path / "pkg"
    (source / "sub").mkdir(parents=True)
    (source / "run.sh").write_text("#!/bin/sh\n")
    (source / "run.sh").chmod(0o755)
    (source / "sub" / "data.txt").write_text("x")
    first = _pack_package_dir(source, tmp_path / "a.tgz")
    second = _pack_package_dir(source, tmp_path / "b.tgz")
    assert first == second
    assert (tmp_path / "a.tgz").read_bytes() == (tmp_path / "b.tgz").read_bytes()
    with tarfile.open(tmp_path / "a.tgz", "r:gz") as tar:
        assert tar.getmember("package/run.sh").mode == 0o755
        assert tar.getmember("package/sub/data.txt").mode == 0o644


def test_pack_internal_dir_symlink(tmp_path):
    source = tmp_path / "pkg"
    (source / "realdir").mkdir(parents=True)
    (source / "realdir" / "f.txt").write_text("x")
    (source / "alias").symlink_to("realdir")
    _pack_package_dir(source, tmp_path / "x.tgz")
    with tarfile.open(tmp_path / "x.tgz", "r:gz") as tar:
        member = tar.getmember("package/alias")
        assert member.issym() and member.linkname == "realdir"


def test_node_sums_blank_lines(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    _dist, node_payload, node_sums = _node_dist_payload()
    monkeypatch.setattr(
        "proofquest.serve.urllib.request.urlopen",
        _fake_urlopen_factory(node_payload, node_sums + b"\n\n  \n"),
    )
    node = _provision_legacy_node()
    assert node.is_file()
