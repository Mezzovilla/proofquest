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
    ServeError,
    _npm_allow_git,
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
