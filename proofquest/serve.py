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
import base64
import gzip
import hashlib
import io
import json
import os
import platform
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
from dataclasses import dataclass
from pathlib import Path

from .toolchain import game_toolchain

_LEAN4GAME_REPO = "leanprover-community/lean4game"
_TAG_RE = re.compile(r"^v\d+\.\d+\.\d+$")
_SHA_RE = re.compile(r"^[0-9a-f]{40}$")
_CACHE_KEY_RE = re.compile(r"^lean4game-")  # any ref form: tag, sha or branch
_READY_MARKER = ".proofquest-serve-ready"
_RELAY_ENTRY = Path("relay/dist/src/index.js")
_RELAY_ENTRY_LEGACY = Path("relay/index.mjs")
_CLIENT_INDEX = Path("client/dist/index.html")
# Paths copied from the lean4game tree into the cache; everything else
# (.git, server/, cypress/, ...) is irrelevant for serving.
_COPIED_PATHS = ("client", "relay", "package.json", "package-lock.json")
_LEGACY_COPIED_PATHS = _COPIED_PATHS + (
    "index.html",
    "vite.config.ts",
    "tsconfig.json",
    "env.d.ts",
)
_COPY_IGNORE = shutil.ignore_patterns("node_modules", "dist", ".lake")
_READY_TIMEOUT = 90.0
_LEGACY_COMPAT = "compat1"
_LEGACY_NODE_VERSION = "v22.17.0"
_LEGACY_POLICY = "local-only-v1"
_NODEJS_DIST = "https://nodejs.org/dist"
_LEGACY_RELAY_PATCHES = (
    (
        ".listen(PORT, () => console.log(`Listening on ${PORT}`));",
        ".listen(PORT, '127.0.0.1', () => console.log(`Listening on ${PORT}`));",
    ),
    (
        "const wss = new WebSocketServer({ server })",
        (
            "const localOrigins = new Set("
            "[`http://localhost:${PORT}`, `http://127.0.0.1:${PORT}`]);\n"
            "const wss = new WebSocketServer({\n"
            "  server,\n"
            "  verifyClient: ({ origin }) => !origin || localOrigins.has(origin)\n"
            "})"
        ),
    ),
    (
        "router.get('/import/status/:owner/:repo', importStatus)",
        "router.get('/import/status/:owner/:repo', (_req, res) => res.sendStatus(404))",
    ),
    (
        "router.get('/import/trigger/:owner/:repo', importTrigger)",
        "router.get('/import/trigger/:owner/:repo', (_req, res) => res.sendStatus(404))",
    ),
)


@dataclass(frozen=True)
class _VendorPin:
    dep: str
    repo: str
    sha: str
    subdir: str
    package_name: str
    version: str
    tarball: str
    spec: str
    resolved: str


_LEGACY_VENDOR_PINS = (
    _VendorPin(
        dep="lean4-infoview",
        repo="leanprover-community/vscode-lean4",
        sha="de0062c9e108270c8dbf649a77538f433721154e",
        subdir="lean4-infoview",
        package_name="@leanprover/infoview",
        version="0.4.2",
        tarball="leanprover-infoview-0.4.2.tgz",
        spec="https://gitpkg.now.sh/leanprover/vscode-lean4"
        "/lean4-infoview?de0062c",
        resolved="https://gitpkg.now.sh/leanprover/vscode-lean4"
        "/lean4-infoview?de0062c",
    ),
    _VendorPin(
        dep="lean4web",
        repo="hhu-adam/lean4web",
        sha="414d9e62638a392fca278761b4c61a1d2e138bc7",
        subdir="",
        package_name="lean4web",
        version="0.1.0",
        tarball="lean4web-0.1.0.tgz",
        spec="github:hhu-adam/lean4web"
        "#414d9e62638a392fca278761b4c61a1d2e138bc7",
        resolved="git+ssh://git@github.com/hhu-adam/lean4web.git"
        "#414d9e62638a392fca278761b4c61a1d2e138bc7",
    ),
    _VendorPin(
        dep="lean4",
        repo="leanprover-community/vscode-lean4",
        sha="8d0cc34dcfa00da8b4a48394ba1fb3a600e3f985",
        subdir="vscode-lean4",
        package_name="lean4",
        version="0.0.119",
        tarball="lean4-0.0.119.tgz",
        spec="https://gitpkg.now.sh/leanprover/vscode-lean4"
        "/vscode-lean4?8d0cc34dcfa00da8b4a48394ba1fb3a600e3f985",
        resolved="https://gitpkg.now.sh/leanprover/vscode-lean4"
        "/vscode-lean4?8d0cc34dcfa00da8b4a48394ba1fb3a600e3f985",
    ),
)


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


def _relay_entry(root: Path) -> Path:
    if (root / _RELAY_ENTRY).is_file():
        return _RELAY_ENTRY
    if (root / _RELAY_ENTRY_LEGACY).is_file():
        return _RELAY_ENTRY_LEGACY
    return _RELAY_ENTRY


def _is_built(root: Path) -> bool:
    return (
        (root / _RELAY_ENTRY).is_file() or (root / _RELAY_ENTRY_LEGACY).is_file()
    ) and (root / _CLIENT_INDEX).is_file()


def _legacy_runtime(root: Path) -> bool:
    """Whether the tree is the raw GameServer v4.7 layout (relay/index.mjs +
    a ``build_client`` root script, no ``build:relay``/tsc step)."""
    if not (root / _RELAY_ENTRY_LEGACY).is_file():
        return False
    try:
        scripts = json.loads((root / "package.json").read_text()).get("scripts", {})
    except (OSError, ValueError):
        return False
    return "build_client" in scripts


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


def _fetch(url: str) -> bytes:
    try:
        with urllib.request.urlopen(url, timeout=120) as response:
            return response.read()
    except OSError as exc:
        raise ServeError(
            f"could not download {url}: {exc}\n"
            "preparing the runtime needs network access on the first run"
        ) from exc


def _extract_archive(payload: bytes, dest: Path, mode: str) -> None:
    dest.mkdir(parents=True, exist_ok=True)
    root = dest.resolve()
    try:
        with tarfile.open(fileobj=io.BytesIO(payload), mode=mode) as tar:
            for member in tar.getmembers():
                name = Path(member.name)
                if name.is_absolute() or ".." in name.parts:
                    raise ServeError(f"archive member escapes its root: {member.name}")
                if member.islnk() or member.issym():
                    link = Path(member.linkname)
                    if link.is_absolute():
                        raise ServeError(
                            f"archive link {member.name} points outside: "
                            f"{member.linkname}"
                        )
                    target = Path(os.path.normpath(root / name.parent / link))
                    if not target.is_relative_to(root):
                        raise ServeError(
                            f"archive link {member.name} escapes to "
                            f"{member.linkname}"
                        )
                elif not (member.isdir() or member.isreg()):
                    raise ServeError(
                        f"archive member of unsupported type: {member.name}"
                    )
            tar.extractall(dest, filter="data")
    except tarfile.TarError as exc:
        raise ServeError(f"could not unpack archive into {dest}: {exc}") from exc


def _node_platform() -> tuple[str, str]:
    osname = {"linux": "linux", "darwin": "darwin"}.get(sys.platform)
    arch = {
        "x86_64": "x64", "amd64": "x64",
        "aarch64": "arm64", "arm64": "arm64",
    }.get(platform.machine().lower())
    if osname is None or arch is None:
        raise ServeError(
            f"no pinned Node {_LEGACY_NODE_VERSION} build for "
            f"{sys.platform}/{platform.machine()}"
        )
    return osname, arch


def _check_node(node: Path) -> bool:
    try:
        result = subprocess.run(
            [str(node), "--version"], capture_output=True, text=True, check=False,
            timeout=30
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return result.returncode == 0 and result.stdout.strip() == _LEGACY_NODE_VERSION


def _free_dir(base: Path) -> Path:
    candidate = base
    suffix = 1
    while candidate.exists():
        suffix += 1
        candidate = base.with_name(f"{base.name}-{suffix}")
    return candidate


def _provision_legacy_node() -> Path:
    """Official Node v22.17.0 for the legacy runtime, privately in the cache."""
    osname, arch = _node_platform()
    dist = f"node-{_LEGACY_NODE_VERSION}-{osname}-{arch}"
    base = cache_root() / dist
    target = base
    suffix = 1
    while target.exists():
        node = target / "bin" / "node"
        if _check_node(node):
            return node
        suffix += 1
        target = base.with_name(f"{base.name}-{suffix}")

    filename = f"{dist}.tar.xz"
    url = f"{_NODEJS_DIST}/{_LEGACY_NODE_VERSION}/{filename}"
    print(f"downloading the pinned Node {_LEGACY_NODE_VERSION} build:")
    print(f"  {url}")
    payload = _fetch(url)
    sums = _fetch(f"{_NODEJS_DIST}/{_LEGACY_NODE_VERSION}/SHASUMS256.txt").decode()
    expected = next(
        (
            parts[0]
            for line in sums.splitlines()
            if len(parts := line.split()) >= 2 and parts[-1] == filename
        ),
        None,
    )
    if expected is None:
        raise ServeError(f"SHASUMS256.txt has no entry for {filename}")
    actual = hashlib.sha256(payload).hexdigest()
    if actual != expected:
        raise ServeError(
            f"SHA256 mismatch for {filename}: got {actual}, expected {expected}"
        )
    staging = target.with_name(f"{target.name}.staging-{os.getpid()}")
    _extract_archive(payload, staging, "r:xz")
    roots = [p for p in staging.iterdir() if p.name != "pax_global_header"]
    if roots != [staging / dist]:
        raise ServeError(f"unexpected Node tarball layout: {[p.name for p in roots]}")
    (staging / dist).rename(target)
    staging.rmdir()
    node = target / "bin" / "node"
    if not _check_node(node):
        raise ServeError(
            f"the extracted Node binary does not report {_LEGACY_NODE_VERSION}"
        )
    return node


def _sha512_integrity(path: Path) -> str:
    digest = hashlib.sha512(path.read_bytes()).digest()
    return "sha512-" + base64.b64encode(digest).decode()


def _pack_package_dir(source: Path, out: Path) -> str:
    """Pack ``source`` into an npm-style ``package/`` tarball: deterministic
    bytes (mtime=0 gzip + tar members, uid/gid 0, sorted), executable bits
    preserved, symlinks only when they stay inside the package."""
    out.parent.mkdir(parents=True, exist_ok=True)
    members = ["package"]
    for path in sorted(source.rglob("*")):
        if path.is_symlink():
            if not path.resolve().is_relative_to(source.resolve()):
                raise ServeError(
                    f"vendored source {path} links outside the package: "
                    f"{path.readlink()}"
                )
            members.append("package/" + path.relative_to(source).as_posix())
        elif path.is_file() or path.is_dir():
            members.append("package/" + path.relative_to(source).as_posix())
        else:
            raise ServeError(f"unsupported file type in vendored source: {path}")
    with (
        open(out, "wb") as raw,
        gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as gz,
        tarfile.open(fileobj=gz, mode="w") as tar,
    ):
        for arcname in members:
            rel = arcname.removeprefix("package/") if arcname != "package" else "."
            real = source / rel
            info = tarfile.TarInfo(arcname)
            info.mtime = 0
            info.uid = info.gid = 0
            info.uname = info.gname = ""
            if real.is_symlink():
                info.type = tarfile.SYMTYPE
                info.linkname = real.readlink().as_posix()
                info.mode = 0o777
                tar.addfile(info)
            elif real.is_dir():
                info.type = tarfile.DIRTYPE
                info.mode = 0o755
                tar.addfile(info)
            else:
                info.type = tarfile.REGTYPE
                info.mode = 0o755 if real.stat().st_mode & 0o111 else 0o644
                info.size = real.stat().st_size
                with open(real, "rb") as fh:
                    tar.addfile(info, fh)
    return _sha512_integrity(out)


def _vendor_dep(pin: _VendorPin, work: Path, vendor_dir: Path, lean4_spec: str | None) -> str:
    """Download ``pin``'s exact codeload source, verify it, and pack it into
    ``vendor_dir`` as an npm tarball. Returns its sha512 integrity string."""
    url = f"https://codeload.github.com/{pin.repo}/tar.gz/{pin.sha}"
    print(f"vendoring {pin.dep} from {pin.repo}@{pin.sha[:12]} ({url})")
    payload = _fetch(url)
    stage = work / pin.dep
    _extract_archive(payload, stage, "r:gz")
    roots = [
        p for p in stage.iterdir()
        if p.is_dir() and p.name != "pax_global_header"
    ]
    if len(roots) != 1:
        raise ServeError(
            f"the {pin.repo}@{pin.sha[:12]} archive has an unexpected layout: "
            f"{[p.name for p in roots]}"
        )
    package_dir = roots[0] / pin.subdir if pin.subdir else roots[0]
    manifest = package_dir / "package.json"
    if not manifest.is_file():
        raise ServeError(
            f"no package.json at {pin.subdir or '.'} in {pin.repo}@{pin.sha[:12]}"
        )
    try:
        info = json.loads(manifest.read_text())
    except ValueError as exc:
        raise ServeError(f"unreadable {pin.dep} package.json: {exc}") from exc
    if info.get("name") != pin.package_name or info.get("version") != pin.version:
        raise ServeError(
            f"the {pin.dep} source does not match the pinned package "
            f"{pin.package_name}@{pin.version}: got "
            f"{info.get('name')}@{info.get('version')}"
        )
    if lean4_spec is not None:
        dependencies = info.get("dependencies", {})
        expected = next(p.spec for p in _LEGACY_VENDOR_PINS if p.dep == "lean4")
        if dependencies.get("lean4") != expected:
            raise ServeError(
                "unsupported lean4 reference in the lean4web source: "
                f"{dependencies.get('lean4')!r}; expected {expected!r}"
            )
        dependencies["lean4"] = lean4_spec
        manifest.write_text(json.dumps(info, indent=2) + "\n")
    has_license = any(
        p.is_file() and p.name.upper().startswith("LICENSE")
        for p in package_dir.iterdir()
    )
    if not has_license:
        license_src = next(
            (
                p
                for p in roots[0].iterdir()
                if p.is_file() and p.name.upper().startswith("LICENSE")
            ),
            None,
        )
        if license_src is not None:
            shutil.copy2(license_src, package_dir / license_src.name)
    return _pack_package_dir(package_dir, vendor_dir / pin.tarball)


def _migrate_legacy_lock(root: Path, integrities: dict[str, str]) -> None:
    """Point the three dead git deps at the vendored ``file:`` tarballs.

    Every reference is validated against the exact pinned upstream spec
    before anything is written, so an unrecognized source fails closed with
    both files untouched. All other registry versions, resolved URLs and
    integrities are preserved.
    """
    manifest = json.loads((root / "package.json").read_text())
    lock = json.loads((root / "package-lock.json").read_text())
    deps = manifest.get("dependencies", {})
    packages = lock.get("packages", {})
    root_deps = packages.get("", {}).get("dependencies", {})
    lean4_spec = f"file:{(root / 'vendor' / 'lean4-0.0.119.tgz').resolve()}"

    for pin in _LEGACY_VENDOR_PINS:
        entry = packages.get(f"node_modules/{pin.dep}")
        if entry is None:
            raise ServeError(f"package-lock.json has no node_modules/{pin.dep} entry")
        if entry.get("version") != pin.version or entry.get("resolved") != pin.resolved:
            raise ServeError(
                f"unsupported {pin.dep} lockfile pin: "
                f"{entry.get('resolved')!r} version {entry.get('version')!r}; "
                f"expected {pin.resolved!r} version {pin.version!r}"
            )
    specs: dict[str, str] = {}
    for pin in _LEGACY_VENDOR_PINS:
        if pin.dep == "lean4":
            continue
        if deps.get(pin.dep) != pin.spec:
            raise ServeError(
                f"unsupported {pin.dep} reference in package.json: "
                f"{deps.get(pin.dep)!r}; expected {pin.spec!r}"
            )
        if root_deps.get(pin.dep) != pin.spec:
            raise ServeError(
                f"unsupported {pin.dep} root reference in package-lock.json: "
                f"{root_deps.get(pin.dep)!r}; expected {pin.spec!r}"
            )
        specs[pin.dep] = f"file:vendor/{pin.tarball}"
    lean4_pin = next(p for p in _LEGACY_VENDOR_PINS if p.dep == "lean4")
    lean4web = packages["node_modules/lean4web"]
    if lean4web.get("dependencies", {}).get("lean4") != lean4_pin.spec:
        raise ServeError(
            "unsupported transitive lean4 reference in package-lock.json: "
            f"{lean4web.get('dependencies', {}).get('lean4')!r}; "
            f"expected {lean4_pin.spec!r}"
        )

    for dep, spec in specs.items():
        deps[dep] = spec
        root_deps[dep] = spec
    lean4web["dependencies"]["lean4"] = lean4_spec
    for pin in _LEGACY_VENDOR_PINS:
        entry = packages[f"node_modules/{pin.dep}"]
        entry["resolved"] = lean4_spec if pin.dep == "lean4" else specs[pin.dep]
        entry["integrity"] = integrities[pin.dep]
    migrated_lock = json.dumps(lock, indent=2)
    migrated_manifest = json.dumps(manifest, indent=2)
    for dead in ("gitpkg.now.sh", "git+ssh", "github:hhu-adam"):
        if dead in migrated_lock or dead in migrated_manifest:
            raise ServeError(f"dead remote reference {dead!r} survived lock migration")
    (root / "package.json").write_text(migrated_manifest + "\n")
    (root / "package-lock.json").write_text(migrated_lock + "\n")


def _legacy_ready(root: Path, ref: str, rev: str | None) -> bool:
    if not _is_built(root):
        return False
    try:
        data = json.loads((root / _READY_MARKER).read_text())
    except (OSError, ValueError):
        return False
    if not isinstance(data, dict):
        return False
    if (
        data.get("compat") != _LEGACY_COMPAT
        or data.get("ref") != ref
        or data.get("rev") != rev
        or data.get("node") != _LEGACY_NODE_VERSION
        or data.get("host") != "127.0.0.1"
        or data.get("policy") != _LEGACY_POLICY
    ):
        return False
    vendor = data.get("vendor")
    if not isinstance(vendor, dict) or set(vendor) != {
        pin.dep for pin in _LEGACY_VENDOR_PINS
    }:
        return False
    for pin in _LEGACY_VENDOR_PINS:
        entry = vendor[pin.dep]
        if (
            not isinstance(entry, dict)
            or entry.get("repo") != pin.repo
            or entry.get("sha") != pin.sha
            or entry.get("subdir") != pin.subdir
            or entry.get("tarball") != pin.tarball
        ):
            return False
        tarball = root / "vendor" / pin.tarball
        if not tarball.is_file():
            return False
        try:
            if _sha512_integrity(tarball) != entry.get("integrity"):
                return False
        except OSError:
            return False
    return True


def _ensure_legacy_runtime(
    source: Path, ref: str, rev: str | None, rebuild: bool
) -> Path:
    """Prepare (once) the reproducible GameServer v4.7 runtime: pinned Node
    v22.17.0, vendored pins replacing the dead gitpkg deps, ``npm ci``, and
    the root ``build_client`` vite build. Never rewrites an existing cache
    entry: a stale or partial one is left in place and a fresh suffixed
    directory is used instead."""
    key = _cache_key(ref, rev) + f"-{_LEGACY_COMPAT}"
    base = cache_root() / key
    candidate = base
    suffix = 1
    while candidate.exists():
        if not rebuild and _legacy_ready(candidate, ref, rev):
            print(f"reusing the cached lean4game {ref} runtime: {candidate}")
            return candidate
        suffix += 1
        candidate = base.with_name(f"{base.name}-{suffix}")
    root = candidate
    root.mkdir(parents=True)

    print(f"preparing the pinned lean4game {ref} legacy runtime in {root}")
    for name in _LEGACY_COPIED_PATHS:
        origin = source / name
        if origin.is_dir():
            shutil.copytree(origin, root / name, ignore=_COPY_IGNORE)
        elif origin.is_file():
            shutil.copy2(origin, root / name)
        else:
            raise ServeError(f"the lean4game tree at {source} is missing {name}")
    relay = root / _RELAY_ENTRY_LEGACY
    relay_text = relay.read_text()
    for unbound, bound in _LEGACY_RELAY_PATCHES:
        if unbound not in relay_text:
            raise ServeError(
                f"the legacy relay at {relay} does not contain the expected "
                f"{unbound.strip()!r} line; refusing to serve"
            )
    for unbound, bound in _LEGACY_RELAY_PATCHES:
        relay_text = relay_text.replace(unbound, bound, 1)
    relay.write_text(relay_text)

    node = _provision_legacy_node()
    work = root / ".vendor-work"
    vendor = root / "vendor"
    lean4_spec = f"file:{(vendor / 'lean4-0.0.119.tgz').resolve()}"
    integrities = {
        pin.dep: _vendor_dep(
            pin, work, vendor, lean4_spec if pin.dep == "lean4web" else None
        )
        for pin in _LEGACY_VENDOR_PINS
    }
    _migrate_legacy_lock(root, integrities)

    env = dict(os.environ)
    env["PATH"] = str(node.parent) + os.pathsep + env.get("PATH", "")
    env["CYPRESS_INSTALL_BINARY"] = "0"
    npm = node.parent / "npm"
    print("installing the pinned npm dependencies (npm ci, migrated lockfile)")
    _run([str(npm), "ci", "--no-audit", "--no-fund"], root, env)
    print("building the lean4game client (first run only)")
    _run([str(npm), "run", "build_client"], root, env)
    if not _is_built(root):
        raise ServeError(
            "the legacy client build finished but the expected artifacts are "
            f"missing ({_CLIENT_INDEX})"
        )
    (root / _READY_MARKER).write_text(
        json.dumps(
            {
                "ref": ref,
                "rev": rev,
                "compat": _LEGACY_COMPAT,
                "node": _LEGACY_NODE_VERSION,
                "host": "127.0.0.1",
                "policy": _LEGACY_POLICY,
                "vendor": {
                    pin.dep: {
                        "repo": pin.repo,
                        "sha": pin.sha,
                        "subdir": pin.subdir,
                        "tarball": pin.tarball,
                        "integrity": integrities[pin.dep],
                    }
                    for pin in _LEGACY_VENDOR_PINS
                },
                "prepared_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
            }
        ),
        encoding="utf-8",
    )
    return root


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
    if source is not None and _legacy_runtime(source):
        return _ensure_legacy_runtime(source, ref, rev, rebuild)
    root = cache_root() / _cache_key(ref, rev)
    if not rebuild and (root / _READY_MARKER).is_file() and _is_built(root):
        print(f"reusing the cached lean4game {ref} runtime: {root}")
        return root
    if source is None:
        staging = _free_dir(cache_root() / (_cache_key(ref, rev) + ".source"))
        _download_pinned(ref, staging)
        if _legacy_runtime(staging):
            return _ensure_legacy_runtime(staging, ref, rev, rebuild)
        source = staging
        source_note = f"the downloaded lean4game {ref} tarball"

    if root.exists():
        shutil.rmtree(root)
    root.mkdir(parents=True)
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


def spawn_relay(
    entry: Path, port: int, cwd: Path, node: Path | None = None
) -> subprocess.Popen:
    """Start the lean4game relay (which also serves the built client)."""
    node_bin = str(node) if node is not None else shutil.which("node")
    if node_bin is None:
        raise ServeError("node not found on PATH; install Node.js to serve the game")
    if shutil.which("lake") is None:
        print("warning: lake not found on PATH; players will not be able to connect")
    env = dict(os.environ)
    env["NODE_ENV"] = "development"  # enables local games and the un-sandboxed `lake serve`
    env["PORT"] = str(port)
    env["API_PORT"] = str(_free_port())  # stats endpoint (relay reads API_PORT)
    if node is not None:
        env["PATH"] = str(node.parent) + os.pathsep + env.get("PATH", "")
    return subprocess.Popen(
        [node_bin, str(entry)], cwd=cwd, env=env, start_new_session=True
    )


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

    entry = root / _relay_entry(root)
    node = _provision_legacy_node() if _legacy_runtime(root) else None
    print(f"  starting the lean4game relay: node {entry}")
    process = spawn_relay(entry, args.port, cwd=cache_root(), node=node)
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
