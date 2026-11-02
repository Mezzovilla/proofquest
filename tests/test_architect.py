import json
import os
from pathlib import Path

import pytest

from proofquest import architect
from proofquest.architect import (
    ArchitectConfig,
    ArchitectError,
    ArchitectMetadata,
    _complete_deliverables,
    _module_body,
    _publish,
    _read_metadata,
    build_architect_blueprint,
    load_config,
)
from proofquest.cli import main

REVISION = "a" * 40


def make_project(tmp_path: Path, modules=("Example.Main",)) -> Path:
    project = tmp_path / "project"
    package = project / ".lake" / "packages" / "LeanArchitect"
    package.mkdir(parents=True)
    (project / "lean-toolchain").write_text(
        "leanprover/lean4:v4.31.0\n", encoding="utf-8"
    )
    (project / "lake-manifest.json").write_text(
        json.dumps(
            {
                "packagesDir": ".lake/packages",
                "packages": [
                    {
                        "name": "LeanArchitect",
                        "type": "git",
                        "rev": REVISION,
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    module_lines = "\n".join(f'  "{module}",' for module in modules)
    (project / "proofquest.toml").write_text(
        "[blueprint]\n"
        'provider = "leanarchitect"\n'
        'library = "Example"\n'
        "modules = [\n"
        f"{module_lines}\n"
        "]\n",
        encoding="utf-8",
    )
    (project / "Basic.lean").write_text(
        "theorem foo : True := by\n  trivial\n", encoding="utf-8"
    )
    return project


def install_fake_runner(monkeypatch, project: Path, *, nondeterministic=False):
    def fake_run(cmd: list[str], cwd: Path) -> str:
        if cmd[0] == "git":
            return REVISION + "\n"
        if cmd[:2] == ["lake", "build"]:
            index = project / ".lake/build/blueprint/library/Example.tex"
            index.parent.mkdir(parents=True, exist_ok=True)
            modules = load_config(project).modules
            index.write_text(
                "\n".join(
                    f"\\input{{{project}/.lake/build/blueprint/module/"
                    f"{module.replace('.', '/')}.tex}}"
                    for module in modules
                ),
                encoding="utf-8",
            )
            return ""
        if cmd[:3] == ["lake", "env", "extract_blueprint"]:
            build_dir = Path(cmd[cmd.index("--build") + 1])
            module = cmd[-1]
            module_path = Path(*module.split("."))
            module_file = build_dir / "blueprint/module" / module_path.with_suffix(
                ".tex"
            )
            artifacts = build_dir / "blueprint/module" / Path(
                str(module_path) + ".artifacts"
            )
            module_file.parent.mkdir(parents=True, exist_ok=True)
            artifacts.mkdir(parents=True, exist_ok=True)
            label = "foo" if module.endswith("Main") else "other"
            module_file.write_text(
                f"preamble\n\\newleanmodule{{{module}}}{{\n"
                f"\\chapter{{Example}}\n\\inputleannode{{{label}}}\n}}\n",
                encoding="utf-8",
            )
            marker = "stage one" if nondeterministic and "-1-" in str(build_dir) else "same"
            (artifacts / f"{label}.tex").write_text(
                "\\begin{lemma}\n"
                f"\\label{{{label}}}\n"
                "\\lean{foo}\n"
                f"% at {project}/Basic.lean:1.0-2.9\n"
                "\\leanok\n"
                f"Statement {marker}.\n"
                "\\end{lemma}\n"
                "\\begin{proof}\nTrivial.\n\\end{proof}\n",
                encoding="utf-8",
            )
            return ""
        raise AssertionError(f"unexpected command: {cmd}")

    monkeypatch.setattr(architect, "_run", fake_run)


def test_load_config_rejects_unknown_and_duplicate_values(tmp_path):
    project = make_project(tmp_path)
    config = project / "proofquest.toml"
    config.write_text(
        "[blueprint]\n"
        'provider = "leanarchitect"\n'
        'library = "Example"\n'
        'modules = ["Example.Main", "Example.Main"]\n'
        "extra = true\n",
        encoding="utf-8",
    )
    with pytest.raises(ArchitectError, match="unknown.*extra"):
        load_config(project)
    config.write_text(
        "[blueprint]\n"
        'provider = "leanarchitect"\n'
        'library = "Example"\n'
        'modules = ["Example.Main", "Example.Main"]\n',
        encoding="utf-8",
    )
    with pytest.raises(ArchitectError, match="duplicate"):
        load_config(project)


def test_metadata_requires_toolchain_exact_pin_and_matching_checkout(tmp_path, monkeypatch):
    project = make_project(tmp_path)
    (project / "lean-toolchain").unlink()
    with pytest.raises(ArchitectError, match="toolchain file not found"):
        _read_metadata(project)

    (project / "lean-toolchain").write_text(
        "leanprover/lean4:v4.31.0\n", encoding="utf-8"
    )
    manifest = json.loads((project / "lake-manifest.json").read_text())
    manifest["packages"][0]["rev"] = "main"
    (project / "lake-manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
    with pytest.raises(ArchitectError, match="exact 40-character commit"):
        _read_metadata(project)

    manifest["packages"][0]["rev"] = REVISION
    (project / "lake-manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
    monkeypatch.setattr(architect, "_run", lambda cmd, cwd: "b" * 40 + "\n")
    with pytest.raises(ArchitectError, match="expected"):
        _read_metadata(project)


def test_cli_build_check_generate_end_to_end(tmp_path, monkeypatch):
    project = make_project(tmp_path)
    install_fake_runner(monkeypatch, project)

    assert main(["blueprint", "build", str(project)]) == 0
    content = (project / "blueprint/src/content.tex").read_text(encoding="utf-8")
    assert "% at Basic.lean:1.0-2.9" in content
    assert str(project) not in content
    assert (project / "blueprint/lean_decls").read_text() == "foo\n"
    assert main(["check", str(project)]) == 0

    game = tmp_path / "game"
    assert main(["generate", str(project), "-o", str(game)]) == 0
    assert any((game / "Game/Levels").glob("*/L*_foo.lean"))


def test_build_rejects_nondeterministic_extraction(tmp_path, monkeypatch):
    project = make_project(tmp_path)
    install_fake_runner(monkeypatch, project, nondeterministic=True)
    with pytest.raises(ArchitectError, match="not deterministic"):
        build_architect_blueprint(project)
    assert not (project / "blueprint").exists()


def test_build_rejects_configured_module_outside_library(tmp_path, monkeypatch):
    project = make_project(tmp_path)
    install_fake_runner(monkeypatch, project)
    monkeypatch.setattr(architect, "_library_modules", lambda project, library: set())
    with pytest.raises(ArchitectError, match="not found.*Example.Main"):
        build_architect_blueprint(project)


def test_manual_blueprint_is_protected_and_force_preserves_static_files(
    tmp_path, monkeypatch
):
    project = make_project(tmp_path)
    install_fake_runner(monkeypatch, project)
    content = project / "blueprint/src/content.tex"
    content.parent.mkdir(parents=True)
    content.write_text("manual\n", encoding="utf-8")
    static = project / "blueprint/web/index.html"
    static.parent.mkdir(parents=True)
    static.write_text("static\n", encoding="utf-8")

    with pytest.raises(ArchitectError, match="refusing to overwrite"):
        build_architect_blueprint(project)
    build_architect_blueprint(project, force=True)
    assert "\\begin{lemma}" in content.read_text(encoding="utf-8")
    assert static.read_text(encoding="utf-8") == "static\n"

    content.write_text("edited generated output\n", encoding="utf-8")
    with pytest.raises(ArchitectError, match="modified after generation"):
        build_architect_blueprint(project)


def test_module_label_cannot_escape_artifacts_directory(tmp_path):
    build = tmp_path / "build"
    module = build / "blueprint/module/Example/Main.tex"
    module.parent.mkdir(parents=True)
    module.write_text(
        "\\newleanmodule{Example.Main}{\n\\inputleannode{../../escape}\n}\n",
        encoding="utf-8",
    )
    with pytest.raises(ArchitectError, match="escapes"):
        _module_body(build, "Example.Main", set(), tmp_path)


def test_unresolved_leanarchitect_commands_are_rejected(tmp_path):
    build = tmp_path / "build"
    module = build / "blueprint/module/Example/Main.tex"
    module.parent.mkdir(parents=True)
    module.write_text(
        "\\newleanmodule{Example.Main}{\n\\inputleanmodule{Other}\n}\n",
        encoding="utf-8",
    )
    with pytest.raises(ArchitectError, match="unresolved"):
        _module_body(build, "Example.Main", set(), tmp_path)


def test_duplicate_labels_across_modules_are_rejected(tmp_path):
    build = tmp_path / "build"
    seen: set[str] = set()
    for name in ("One", "Two"):
        module = build / f"blueprint/module/Example/{name}.tex"
        artifacts = build / f"blueprint/module/Example/{name}.artifacts"
        module.parent.mkdir(parents=True, exist_ok=True)
        artifacts.mkdir(parents=True)
        module.write_text(
            f"\\newleanmodule{{Example.{name}}}{{\n\\inputleannode{{same}}\n}}\n",
            encoding="utf-8",
        )
        (artifacts / "same.tex").write_text(
            "\\begin{lemma}\\label{same}x\\end{lemma}\n", encoding="utf-8"
        )
    _module_body(build, "Example.One", seen, tmp_path)
    with pytest.raises(ArchitectError, match="duplicate"):
        _module_body(build, "Example.Two", seen, tmp_path)


def test_publication_rolls_back_if_replace_fails(tmp_path, monkeypatch):
    project = tmp_path / "project"
    project.mkdir()
    config = ArchitectConfig(library="Example", modules=("Example.Main",))
    metadata = ArchitectMetadata(
        toolchain="leanprover/lean4:v4.31.0",
        revision=REVISION,
        package_dir=tmp_path,
    )
    original = _complete_deliverables(
        {Path("src/content.tex"): b"old\n", Path("lean_decls"): b"old\n"},
        config,
        metadata,
    )
    _publish(project, original, force=True)

    replacement = _complete_deliverables(
        {Path("src/content.tex"): b"new\n", Path("lean_decls"): b"new\n"},
        config,
        metadata,
    )
    real_replace = os.replace
    calls = 0

    def fail_once(source, destination):
        nonlocal calls
        calls += 1
        if calls == 3:
            raise OSError("injected failure")
        return real_replace(source, destination)

    monkeypatch.setattr(architect.os, "replace", fail_once)
    with pytest.raises(ArchitectError, match="transactionally"):
        _publish(project, replacement, force=False)
    assert (project / "blueprint/src/content.tex").read_bytes() == b"old\n"
    assert (project / "blueprint/lean_decls").read_bytes() == b"old\n"
