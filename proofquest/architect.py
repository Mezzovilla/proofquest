"""Generate leanblueprint sources from LeanArchitect annotations."""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import tomllib
from dataclasses import dataclass
from pathlib import Path


class ArchitectError(Exception):
    """Raised when LeanArchitect configuration, extraction, or publication fails."""


@dataclass(frozen=True)
class ArchitectConfig:
    library: str
    modules: tuple[str, ...]


@dataclass(frozen=True)
class ArchitectMetadata:
    toolchain: str
    revision: str
    package_dir: Path


_CONFIG_KEYS = {"provider", "library", "modules"}
_INPUTLEANNODE_RE = re.compile(r"\\inputleannode\{([^}]*)\}")
_LEAN_NAME_RE = re.compile(r"\\lean\{([^}]*)\}")
_USES_RE = re.compile(r"\\uses\{([^}]*)\}")
_LEFTOVER_RE = re.compile(r"\\(inputleannode|inputleanmodule|newleannode|newleanmodule)\b")
_LIBRARY_INPUT_RE = re.compile(r"\\input\{([^}]*/blueprint/module/([^}]+)\.tex)\}")
_REVISION_RE = re.compile(r"[0-9a-fA-F]{40}")
_SHA256_RE = re.compile(r"[0-9a-fA-F]{64}")
_FIXED_ENV = {
    "TZ": "UTC",
    "LC_ALL": "C.UTF-8",
    "PYTHONHASHSEED": "0",
    "SOURCE_DATE_EPOCH": "946684800",
    "FORCE_SOURCE_DATE": "1",
    "SOURCE_DATE_EPOCH_TEX_PRIMITIVES": "1",
}
_MANIFEST = ".proofquest-leanarchitect.json"
_PRIMARY_FILES = (Path("src/content.tex"), Path("lean_decls"))
_MANAGED_FILES = (*_PRIMARY_FILES, Path("SHA256SUMS"), Path(_MANIFEST))


def _validate_lean_name(value: object, field: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ArchitectError(f"proofquest.toml: {field} must be a non-empty string")
    value = value.strip()
    parts = value.split(".")
    if any(part in ("", ".", "..") or "/" in part or "\\" in part for part in parts):
        raise ArchitectError(f"proofquest.toml: invalid Lean name for {field}: {value!r}")
    return value


def load_config(project_dir: Path) -> ArchitectConfig:
    """Read the strict ``[blueprint]`` configuration from ``proofquest.toml``."""
    config_path = project_dir / "proofquest.toml"
    if not config_path.is_file():
        raise ArchitectError(f"configuration file not found: {config_path}")
    try:
        data = tomllib.loads(config_path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as exc:
        raise ArchitectError(f"cannot read {config_path}: {exc}") from exc
    unknown_tables = sorted(set(data) - {"blueprint"})
    if unknown_tables:
        raise ArchitectError(
            "proofquest.toml: unknown top-level table(s): " + ", ".join(unknown_tables)
        )
    table = data.get("blueprint")
    if not isinstance(table, dict):
        raise ArchitectError("proofquest.toml: missing [blueprint] table")
    unknown = sorted(set(table) - _CONFIG_KEYS)
    if unknown:
        raise ArchitectError(
            "proofquest.toml: unknown [blueprint] key(s): " + ", ".join(unknown)
        )
    if table.get("provider") != "leanarchitect":
        raise ArchitectError(
            'proofquest.toml: blueprint.provider must be "leanarchitect"'
        )
    library = _validate_lean_name(table.get("library"), "blueprint.library")
    raw_modules = table.get("modules")
    if not isinstance(raw_modules, list) or not raw_modules:
        raise ArchitectError("proofquest.toml: blueprint.modules must be a non-empty array")
    modules = tuple(
        _validate_lean_name(module, f"blueprint.modules[{index}]")
        for index, module in enumerate(raw_modules)
    )
    duplicates = sorted({module for module in modules if modules.count(module) > 1})
    if duplicates:
        raise ArchitectError(
            "proofquest.toml: duplicate blueprint module(s): " + ", ".join(duplicates)
        )
    return ArchitectConfig(library=library, modules=modules)


def _fixed_env() -> dict[str, str]:
    env = os.environ.copy()
    env.update(_FIXED_ENV)
    return env


def _run(cmd: list[str], cwd: Path) -> str:
    try:
        result = subprocess.run(
            cmd,
            cwd=cwd,
            env=_fixed_env(),
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as exc:
        raise ArchitectError(f"cannot run {cmd[0]!r}: {exc}") from exc
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        suffix = f"\n{detail}" if detail else ""
        raise ArchitectError(
            f"command failed with exit {result.returncode}: {' '.join(cmd)}{suffix}"
        )
    return result.stdout


def _read_metadata(project_dir: Path) -> ArchitectMetadata:
    toolchain_path = project_dir / "lean-toolchain"
    if not toolchain_path.is_file():
        raise ArchitectError(f"Lean toolchain file not found: {toolchain_path}")
    toolchain = toolchain_path.read_text(encoding="utf-8").strip()
    if not toolchain:
        raise ArchitectError(f"Lean toolchain file is empty: {toolchain_path}")

    manifest_path = project_dir / "lake-manifest.json"
    if not manifest_path.is_file():
        raise ArchitectError(
            f"Lake manifest not found: {manifest_path}; pin LeanArchitect and run lake update explicitly"
        )
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ArchitectError(f"cannot read {manifest_path}: {exc}") from exc
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        raise ArchitectError(f"{manifest_path}: missing packages array")
    package = next(
        (
            item
            for item in packages
            if isinstance(item, dict)
            and str(item.get("name", "")).casefold() == "leanarchitect"
        ),
        None,
    )
    if package is None:
        raise ArchitectError("lake-manifest.json: LeanArchitect dependency not found")
    revision = package.get("rev")
    if package.get("type") != "git" or not isinstance(revision, str) or not _REVISION_RE.fullmatch(revision):
        raise ArchitectError(
            "lake-manifest.json: LeanArchitect must be a Git dependency pinned to an exact 40-character commit"
        )
    packages_dir = manifest.get("packagesDir", ".lake/packages")
    if not isinstance(packages_dir, str) or not packages_dir:
        raise ArchitectError("lake-manifest.json: invalid packagesDir")
    package_name = str(package.get("name") or "LeanArchitect")
    package_dir = (project_dir / packages_dir / package_name).resolve()
    if not package_dir.is_dir():
        raise ArchitectError(
            f"LeanArchitect checkout not found: {package_dir}; fetch dependencies explicitly before building"
        )
    actual = _run(["git", "-C", str(package_dir), "rev-parse", "HEAD"], project_dir).strip()
    if actual.casefold() != revision.casefold():
        raise ArchitectError(
            f"LeanArchitect checkout is at {actual or 'an unknown revision'}, expected {revision} from lake-manifest.json"
        )
    return ArchitectMetadata(toolchain=toolchain, revision=revision.lower(), package_dir=package_dir)


def _library_modules(project_dir: Path, library: str) -> set[str]:
    index = project_dir / ".lake" / "build" / "blueprint" / "library" / f"{library}.tex"
    if not index.is_file():
        raise ArchitectError(
            f"LeanArchitect library index not found after build: {index}"
        )
    text = index.read_text(encoding="utf-8")
    return {
        match.group(2).replace("/", ".").replace("\\", ".")
        for match in _LIBRARY_INPUT_RE.finditer(text)
    }


def _canonicalize_artifact(text: str, label: str, project_dir: Path) -> str:
    root = str(project_dir.resolve())
    text = text.replace(f"% at {root}/", "% at ")
    if root in text or re.search(r"(?m)^% at /", text):
        raise ArchitectError(f"artifact {label}: machine-absolute source path remains")

    def sort_uses(match: re.Match[str]) -> str:
        labels = sorted({value.strip() for value in match.group(1).split(",") if value.strip()})
        return "\\uses{" + ",".join(labels) + "}"

    return _USES_RE.sub(sort_uses, text)


def _module_body(build_dir: Path, module: str, seen_labels: set[str], project_dir: Path) -> str:
    module_path = Path(*module.split("."))
    tex_path = build_dir / "blueprint" / "module" / module_path.with_suffix(".tex")
    artifacts_dir = build_dir / "blueprint" / "module" / Path(
        str(module_path) + ".artifacts"
    )
    if not tex_path.is_file():
        raise ArchitectError(f"LeanArchitect did not produce configured module {module}: {tex_path}")
    text = tex_path.read_text(encoding="utf-8")
    marker = f"\\newleanmodule{{{module}}}{{\n"
    start = text.find(marker)
    if start < 0:
        raise ArchitectError(f"{tex_path}: missing module marker for {module}")
    body = text[start + len(marker) :].rstrip()
    if not body.endswith("\n}"):
        raise ArchitectError(f"{tex_path}: malformed LeanArchitect module body")
    body = body[:-2]

    def expand(match: re.Match[str]) -> str:
        label = match.group(1)
        if label in seen_labels:
            raise ArchitectError(f"duplicate blueprint label across modules: {label}")
        seen_labels.add(label)
        artifact = (artifacts_dir / f"{label}.tex").resolve()
        if not artifact.is_relative_to(artifacts_dir.resolve()):
            raise ArchitectError(f"blueprint label escapes the artifacts directory: {label!r}")
        if not artifact.is_file():
            raise ArchitectError(f"missing LeanArchitect artifact for {label}: {artifact}")
        content = artifact.read_text(encoding="utf-8")
        if f"\\label{{{label}}}" not in content:
            raise ArchitectError(f"artifact {artifact}: expected \\label{{{label}}}")
        return _canonicalize_artifact(content, label, project_dir).strip("\n")

    expanded = _INPUTLEANNODE_RE.sub(expand, body)
    if _LEFTOVER_RE.search(expanded):
        raise ArchitectError(f"{tex_path}: unresolved LeanArchitect input command remains")
    return expanded.strip("\n")


def _extract(project_dir: Path, config: ArchitectConfig, stage: Path) -> dict[Path, bytes]:
    build_dir = stage / "architect-build"
    build_dir.mkdir(parents=True, exist_ok=True)
    for module in config.modules:
        _run(
            [
                "lake",
                "env",
                "extract_blueprint",
                "single",
                "--build",
                str(build_dir),
                module,
            ],
            project_dir,
        )
    seen_labels: set[str] = set()
    bodies = [
        _module_body(build_dir, module, seen_labels, project_dir)
        for module in config.modules
    ]
    content = "\n\n".join(bodies) + "\n"
    lean_names = sorted(
        {
            name.strip()
            for match in _LEAN_NAME_RE.finditer(content)
            for name in match.group(1).split(",")
            if name.strip()
        }
    )
    return {
        Path("src/content.tex"): content.encode(),
        Path("lean_decls"): "".join(f"{name}\n" for name in lean_names).encode(),
    }


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _complete_deliverables(
    primary: dict[Path, bytes], config: ArchitectConfig, metadata: ArchitectMetadata
) -> dict[Path, bytes]:
    sums = "".join(
        f"{_sha256(primary[path])}  blueprint/{path.as_posix()}\n"
        for path in sorted(primary, key=lambda item: item.as_posix())
    ).encode()
    files = {path.as_posix(): _sha256(data) for path, data in primary.items()}
    files["SHA256SUMS"] = _sha256(sums)
    manifest = {
        "schema": 1,
        "provider": "leanarchitect",
        "toolchain": metadata.toolchain,
        "leanarchitect_rev": metadata.revision,
        "library": config.library,
        "modules": list(config.modules),
        "files": dict(sorted(files.items())),
    }
    manifest_bytes = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()
    return {**primary, Path("SHA256SUMS"): sums, Path(_MANIFEST): manifest_bytes}


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _publication_conflicts(blueprint_dir: Path) -> list[str]:
    manifest_path = blueprint_dir / _MANIFEST
    existing_managed = [path for path in _MANAGED_FILES if (blueprint_dir / path).exists()]
    if not manifest_path.is_file():
        return [f"{path}: exists but is not managed by ProofQuest" for path in existing_managed]
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [f"{_MANIFEST}: cannot verify existing manifest: {exc}"]
    if manifest.get("schema") != 1 or manifest.get("provider") != "leanarchitect":
        return [f"{_MANIFEST}: unsupported or invalid ownership manifest"]
    files = manifest.get("files")
    if not isinstance(files, dict):
        return [f"{_MANIFEST}: missing files hash map"]
    conflicts: list[str] = []
    expected_paths = {path.as_posix() for path in (*_PRIMARY_FILES, Path("SHA256SUMS"))}
    for rel in sorted(expected_paths):
        expected = files.get(rel)
        path = blueprint_dir / rel
        if not isinstance(expected, str) or not _SHA256_RE.fullmatch(expected):
            conflicts.append(f"{_MANIFEST}: missing or invalid hash for {rel}")
        elif not path.is_file():
            conflicts.append(f"{rel}: managed file is missing")
        elif _file_sha256(path) != expected.lower():
            conflicts.append(f"{rel}: managed file was modified after generation")
    return conflicts


def _publish(project_dir: Path, deliverables: dict[Path, bytes], force: bool) -> list[Path]:
    blueprint_dir = project_dir / "blueprint"
    conflicts = _publication_conflicts(blueprint_dir)
    if conflicts and not force:
        listing = "\n".join(f"  {item}" for item in conflicts)
        raise ArchitectError(
            "refusing to overwrite an unmanaged or modified Blueprint; "
            f"review it or rerun with --force:\n{listing}"
        )

    stage = Path(tempfile.mkdtemp(prefix=".proofquest-publish-", dir=project_dir))
    backup = Path(tempfile.mkdtemp(prefix=".proofquest-backup-", dir=project_dir))
    replaced: list[Path] = []
    had_original: set[Path] = set()
    order = [*_PRIMARY_FILES, Path("SHA256SUMS"), Path(_MANIFEST)]
    try:
        for rel in order:
            staged = stage / rel
            staged.parent.mkdir(parents=True, exist_ok=True)
            staged.write_bytes(deliverables[rel])
        for rel in order:
            destination = blueprint_dir / rel
            if destination.exists():
                saved = backup / rel
                saved.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(destination, saved)
                had_original.add(rel)
            destination.parent.mkdir(parents=True, exist_ok=True)
            os.replace(stage / rel, destination)
            replaced.append(rel)
    except OSError as exc:
        for rel in reversed(replaced):
            destination = blueprint_dir / rel
            try:
                if rel in had_original:
                    os.replace(backup / rel, destination)
                elif destination.exists():
                    destination.unlink()
            except OSError:
                pass
        raise ArchitectError(f"failed to publish Blueprint transactionally: {exc}") from exc
    finally:
        shutil.rmtree(stage, ignore_errors=True)
        shutil.rmtree(backup, ignore_errors=True)
    return [blueprint_dir / rel for rel in order]


def build_architect_blueprint(project_dir: Path, force: bool = False) -> list[Path]:
    """Build, verify, and transactionally publish a LeanArchitect Blueprint."""
    project_dir = project_dir.resolve()
    if not project_dir.is_dir():
        raise ArchitectError(f"project directory not found: {project_dir}")
    config = load_config(project_dir)
    metadata = _read_metadata(project_dir)

    _run(["lake", "build", f"{config.library}:blueprint"], project_dir)
    available = _library_modules(project_dir, config.library)
    missing = [module for module in config.modules if module not in available]
    if missing:
        raise ArchitectError(
            f"configured module(s) not found in LeanArchitect library {config.library}: "
            + ", ".join(missing)
        )

    with (
        tempfile.TemporaryDirectory(prefix="proofquest-architect-1-") as first_dir,
        tempfile.TemporaryDirectory(prefix="proofquest-architect-2-") as second_dir,
    ):
        first = _extract(project_dir, config, Path(first_dir))
        second = _extract(project_dir, config, Path(second_dir))
    differences = [
        path.as_posix()
        for path in sorted(set(first) | set(second), key=lambda item: item.as_posix())
        if first.get(path) != second.get(path)
    ]
    if differences:
        raise ArchitectError(
            "LeanArchitect extraction is not deterministic; differing file(s): "
            + ", ".join(differences)
        )
    return _publish(
        project_dir,
        _complete_deliverables(first, config, metadata),
        force=force,
    )
