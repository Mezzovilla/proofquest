import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

import proofquest.cli
from proofquest.blueprint_parser import parse_blueprint
from proofquest.dep_graph import topological_order
from proofquest.generator import _camel
from proofquest.lean_parser import parse_project

PROJECT_ROOT = Path(__file__).resolve().parents[1]
CLI_CODE = "from proofquest.cli import main; raise SystemExit(main())"

BANACH = {
    "url": "https://github.com/Mezzovilla/Banach-Steinhaus-Sokal-proof-",
    "sha": "9b3d80db2ba2b15e0728a7a8ec2ec03def22f412",
    "toolchain": "leanprover/lean4:v4.31.0",
    "prefix": "BanachSteinhausSokalProof",
}
FLT3 = {
    "url": "https://github.com/Mezzovilla/FLT3-proofquest-game",
    "sha": "a199fa0467f86504a9d2f6164b0456608e586821",
    "prefix": "FLT3",
}
FLT3_KNOWN_DIAGNOSTIC = (
    "error: def:Solution1: copied declaration Solution' (FLT3/FLT3.lean:201) is "
    "declared in a source context (module FLT3.FLT3) that defines project-local "
    "commands which cannot be reproduced in Game/Generated/Defs.lean: attribute "
    "(FLT3/Mathlib/NumberTheory/NumberField/Units.lean:318), instance "
    "(FLT3/Mathlib/NumberTheory/NumberField/Units.lean:480), notation3 "
    "(FLT3/FLT3.lean:153); expand the notation/syntax manually or move the "
    "declaration (and the declarations it uses) to a module that does not rely "
    "on project-local syntax"
)
BANACH_WORLDS = {
    "PreliminaryTechnicalResult": [
        "max_gt_mean",
        "norm_times_scalar_sup_ball",
        "sup_ball_lt_sup_max_ball",
        "sup_max_lt_sup_ball",
        "norm_times_scalar_lt_sup_norm_in_ball",
    ],
    "TheBanachSteinhausTheorem": [
        "choose_geometric_norm_indices",
        "construct_x_sequence",
        "cauchy_of_summable_increments",
        "geometric_dist_is_cauchy",
        "chosen_seq_is_cauchy",
        "limit_dist_geometric_bound",
        "geometric_sequence_diverges",
        "final_contradiction",
        "uniform_boundedness_principle",
    ],
}
BANACH_FILES = {
    "Game.lean",
    "Game/Metadata.lean",
    "Game/Generated/Defs.lean",
    "Game/Generated/TacticDocs.lean",
    "Game/Generated/TheoremDocs.lean",
    "lakefile.lean",
    "lean-toolchain",
    ".gitignore",
    "README.md",
    *{f"Game/Levels/{world}.lean" for world in BANACH_WORLDS},
    *{
        f"Game/Levels/{world}/L{index:02d}_{name}.lean"
        for world, names in BANACH_WORLDS.items()
        for index, name in enumerate(names, 1)
    },
}


class WorkflowFailure(AssertionError):
    pass


class KnownFLT3Failure(AssertionError):
    pass


def _failure(stage, result):
    return WorkflowFailure(
        f"{stage} failed with status {result.get('status')} "
        f"(returncode={result.get('returncode')}): argv={result.get('argv')}\n"
        f"cwd={result.get('cwd')}\n"
        f"repository_url={result.get('repository_url')}\n"
        f"requested_sha={result.get('requested_sha')}\n"
        f"actual_sha={result.get('actual_sha')}\n"
        f"stdout:\n{result.get('stdout', '')}\n"
        f"stderr:\n{result.get('stderr', '')}"
    )


def _decode(stream):
    if stream is None:
        return ""
    return stream.decode("utf-8", "replace") if isinstance(stream, bytes) else stream


def _run_stage(stage, argv, cwd, timeout, evidence_dir, context):
    record = {
        "stage": stage,
        "argv": [str(arg) for arg in argv],
        "cwd": str(cwd),
        "timeout_seconds": timeout,
        "repository_url": context.get("repository_url"),
        "requested_sha": context.get("requested_sha"),
        "actual_sha": context.get("actual_sha"),
    }
    try:
        completed = subprocess.run(
            argv,
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
        record.update(
            {
                "status": "exit",
                "returncode": completed.returncode,
                "stdout": completed.stdout,
                "stderr": completed.stderr,
            }
        )
    except subprocess.TimeoutExpired as exc:
        record.update(
            {
                "status": "timeout",
                "returncode": None,
                "stdout": _decode(exc.stdout),
                "stderr": _decode(exc.stderr),
            }
        )
    except OSError as exc:
        record.update(
            {
                "status": "oserror",
                "returncode": None,
                "stdout": "",
                "stderr": str(exc),
            }
        )
    evidence_dir.mkdir(parents=True, exist_ok=True)
    stem = stage.replace(" ", "-").replace("/", "-")
    (evidence_dir / f"{stem}.stdout.log").write_text(record["stdout"], encoding="utf-8")
    (evidence_dir / f"{stem}.stderr.log").write_text(record["stderr"], encoding="utf-8")
    (evidence_dir / f"{stem}.json").write_text(json.dumps(record, indent=2), encoding="utf-8")
    return record


def _evidence_dir(tmp_path):
    return tmp_path / "evidence"


def _clone_repository(repo, source, tmp_path, record_property):
    if shutil.which("git") is None:
        pytest.skip("requires git on PATH")
    evidence = _evidence_dir(tmp_path)
    context = {
        "repository_url": repo["url"],
        "requested_sha": repo["sha"],
        "actual_sha": None,
    }
    record_property("repository_url", repo["url"])
    record_property("requested_sha", repo["sha"])
    clone = _run_stage(
        "git-clone",
        ["git", "clone", "--no-checkout", repo["url"], source],
        PROJECT_ROOT,
        180,
        evidence,
        context,
    )
    if clone["returncode"] != 0:
        raise _failure("git clone", clone)
    checkout = _run_stage(
        "git-checkout",
        ["git", "checkout", "--detach", repo["sha"]],
        source,
        180,
        evidence,
        context,
    )
    if checkout["returncode"] != 0:
        raise _failure("git checkout", checkout)
    head = _run_stage(
        "git-head", ["git", "rev-parse", "HEAD"], source, 30, evidence, context
    )
    if head["returncode"] != 0:
        raise _failure("git rev-parse", head)
    actual = head["stdout"].strip()
    context["actual_sha"] = actual
    record_property("actual_source_sha", actual)
    if actual != repo["sha"]:
        raise WorkflowFailure(f"cloned HEAD {actual} != pinned SHA {repo['sha']}")
    status = _run_stage(
        "git-status", ["git", "status", "--short", "--branch"], source, 30, evidence,
        context,
    )
    if status["returncode"] != 0 or len(status["stdout"].splitlines()) != 1:
        raise _failure("git status", status)
    return evidence, context


def _proofquest(stage, project, evidence, context, output=None, timeout=300):
    argv = [sys.executable, "-c", CLI_CODE, stage, project]
    if output is not None:
        argv.extend(["-o", output])
    return _run_stage(f"proofquest-{stage}", argv, PROJECT_ROOT, timeout, evidence, context)


def _assert_source_pristine(source, evidence, context):
    status = _run_stage(
        "git-status-final", ["git", "status", "--short", "--branch"], source, 30,
        evidence, context,
    )
    if status["returncode"] != 0 or len(status["stdout"].splitlines()) != 1:
        raise _failure("final git status", status)


def _assert_nonempty(output, relative):
    path = output / relative
    if not path.is_file() or path.stat().st_size == 0:
        raise WorkflowFailure(f"missing or empty generated file: {relative}")
    return path


def _import_lines(path):
    return [
        line.strip()
        for line in path.read_text().splitlines()
        if line.startswith("import ")
    ]


def _assert_banach_completeness(source, output):
    actual_files = {
        str(path.relative_to(output))
        for path in output.rglob("*")
        if path.is_file() and ".lake" not in path.parts and ".i18n" not in path.parts
    }
    if actual_files != BANACH_FILES:
        raise WorkflowFailure(
            f"unexpected generated file set; missing={sorted(BANACH_FILES - actual_files)}, "
            f"extra={sorted(actual_files - BANACH_FILES)}"
        )
    for relative in BANACH_FILES:
        _assert_nonempty(output, relative)
    if (output / "lean-toolchain").read_text().strip() != BANACH["toolchain"]:
        raise WorkflowFailure("unexpected generated toolchain")

    root_imports = _import_lines(output / "Game.lean")
    expected_root = [f"import Game.Levels.{world}" for world in BANACH_WORLDS]
    if root_imports != expected_root:
        raise WorkflowFailure(
            f"Game.lean imports {root_imports}, expected {expected_root}"
        )
    for world, names in BANACH_WORLDS.items():
        world_imports = _import_lines(output / "Game" / "Levels" / f"{world}.lean")
        expected = [
            f"import Game.Levels.{world}.L{index:02d}_{name}"
            for index, name in enumerate(names, 1)
        ]
        if world_imports != expected:
            raise WorkflowFailure(
                f"{world}.lean imports {world_imports}, expected {expected}"
            )

    metadata = _import_lines(output / "Game" / "Metadata.lean")
    for expected in (
        "import GameServer",
        "import Game.Generated.Defs",
        "import Game.Generated.TacticDocs",
        "import Game.Generated.TheoremDocs",
    ):
        if expected not in metadata:
            raise WorkflowFailure(f"Game/Metadata.lean is missing {expected}")

    lakefile = _assert_nonempty(output, "lakefile.lean").read_text()
    for expected in (
        "package Game",
        "name := `GameServer",
        'require "leanprover-community" / mathlib @ git leanVersion',
    ):
        if expected not in lakefile:
            raise WorkflowFailure(f"lakefile.lean is missing {expected!r}")

    decls = parse_project(source)
    norm_map = decls["NormOverBall.NormMap"]
    if norm_map.module != "BanachSteinhausSokalProof.SlidingHump":
        raise WorkflowFailure(f"NormMap came from {norm_map.module}, not the original source")
    defs = _assert_nonempty(output, "Game/Generated/Defs.lean").read_text()
    if norm_map.source_text not in defs:
        raise WorkflowFailure("NormMap is not copied verbatim from the original source")
    if f"namespace {norm_map.namespace}" not in defs:
        raise WorkflowFailure("generated definitions lost the NormOverBall namespace")
    if "theorem " in defs:
        raise WorkflowFailure("a theorem leaked into generated definitions")
    if "DefinitionDoc NormOverBall.NormMap" not in defs:
        raise WorkflowFailure("NormMap lacks its generated DefinitionDoc")

    theorem_names = {
        decl.name: decl for decl in decls.values() if not decl.is_definition
    }
    previous = None
    for world, names in BANACH_WORLDS.items():
        for index, name in enumerate(names, 1):
            level = _assert_nonempty(
                output, f"Game/Levels/{world}/L{index:02d}_{name}.lean"
            ).read_text()
            decl = theorem_names.get(name)
            if decl is None:
                raise WorkflowFailure(f"no source theorem named {name}")
            if (
                f"Statement {decl.name}" not in level
                or decl.signature.strip() not in level
            ):
                raise WorkflowFailure(
                    f"level {name} lacks the exact source statement"
                )
            if decl.namespace and f"namespace {decl.namespace}" not in level:
                raise WorkflowFailure(f"level {name} lost namespace {decl.namespace}")
            if f"TheoremDoc {decl.full_name}" not in level:
                raise WorkflowFailure(f"level {name} lacks its TheoremDoc")
            expected_imports = ["import Game.Metadata"]
            if previous is not None:
                expected_imports.append(f"import Game.Levels.{previous}")
            if _import_lines(output / f"Game/Levels/{world}/L{index:02d}_{name}.lean") != (
                expected_imports
            ):
                raise WorkflowFailure(f"level {name} has unexpected imports")
            previous = f"{world}.L{index:02d}_{name}"
    for path in output.rglob("*.lean"):
        text = path.read_text()
        if f"import {BANACH['prefix']}" in text:
            raise WorkflowFailure(f"generated file imports original project: {path}")


def _assert_flt3_completeness(source, output):
    blueprint = parse_blueprint(source / "blueprint" / "src" / "web.tex")
    decls = parse_project(source)
    for relative in (
        "Game.lean",
        "Game/Metadata.lean",
        "Game/Generated/Defs.lean",
        "Game/Generated/TacticDocs.lean",
        "Game/Generated/TheoremDocs.lean",
        "lakefile.lean",
        "lean-toolchain",
    ):
        _assert_nonempty(output, relative)
    worlds: dict[str, list[str]] = {}
    for node in topological_order(blueprint):
        if not node.is_theorem:
            continue
        decl = next((decls[name] for name in node.lean_names if name in decls), None)
        if decl is None:
            raise WorkflowFailure(f"blueprint theorem {node.label} lacks a source declaration")
        world = _camel(node.chapter)
        levels = worlds.setdefault(world, [])
        stem = decl.name.replace(".", "_")
        relative = f"Game/Levels/{world}/L{len(levels) + 1:02d}_{stem}.lean"
        text = _assert_nonempty(output, relative).read_text()
        if f"Statement {decl.name}" not in text or decl.signature.strip() not in text:
            raise WorkflowFailure(f"generated level lacks source statement for {decl.full_name}")
        levels.append(stem)
    root_imports = _import_lines(output / "Game.lean")
    for world, stems in worlds.items():
        if f"import Game.Levels.{world}" not in root_imports:
            raise WorkflowFailure(f"Game.lean does not import world {world}")
        world_imports = _import_lines(output / "Game" / "Levels" / f"{world}.lean")
        expected = [
            f"import Game.Levels.{world}.L{index:02d}_{stem}"
            for index, stem in enumerate(stems, 1)
        ]
        if world_imports != expected:
            raise WorkflowFailure(
                f"{world}.lean imports {world_imports}, expected {expected}"
            )
    for path in output.rglob("*.lean"):
        if f"import {FLT3['prefix']}" in path.read_text():
            raise WorkflowFailure(f"generated file imports original project: {path}")


def _lake_workflow(output, evidence, context):
    if shutil.which("lake") is None:
        pytest.skip("requires lake/elan on PATH for generated-game build")
    for stage, timeout in (
        ("lake-update", 1200),
        ("lake-cache", 1800),
        ("lake-build", 5400),
    ):
        argv = {
            "lake-update": ["lake", "update", "-R"],
            "lake-cache": ["lake", "exe", "cache", "get"],
            "lake-build": ["lake", "build"],
        }[stage]
        result = _run_stage(stage, argv, output, timeout, evidence, context)
        if result["returncode"] != 0:
            raise _failure(stage, result)


def _assert_package_under_test():
    package_file = Path(proofquest.cli.__file__).resolve()
    if not package_file.is_relative_to(PROJECT_ROOT):
        raise WorkflowFailure(f"proofquest imported from outside workspace: {package_file}")


def _run_check_and_generate(source, output, evidence, context):
    check = _proofquest("check", source, evidence, context)
    if check["returncode"] != 0:
        raise _failure("proofquest check", check)
    return _proofquest("generate", source, evidence, context, output)


def _raise_known_flt3_if_matched(generate, output, source, evidence, context):
    if generate["returncode"] == 0:
        return
    lines = [line for line in generate["stderr"].splitlines() if line.strip()]
    if (
        generate["returncode"] != 1
        or FLT3_KNOWN_DIAGNOSTIC not in lines
        or any(
            not line.startswith("warning:") and line != FLT3_KNOWN_DIAGNOSTIC
            for line in lines
        )
    ):
        raise _failure("proofquest generate", generate)
    if output.exists() and any(output.rglob("*")):
        raise WorkflowFailure("known FLT3 failure left partial generated output")
    _assert_source_pristine(source, evidence, context)
    raise KnownFLT3Failure(FLT3_KNOWN_DIAGNOSTIC)


@pytest.mark.integration
def test_banach_steinhaus_full_game(tmp_path, request, record_property):
    if not request.config.getoption("--run-integration"):
        pytest.skip("requires --run-integration; network, git and Lean dependencies")
    _assert_package_under_test()
    source = tmp_path / "source"
    output = tmp_path / "game"
    evidence, context = _clone_repository(BANACH, source, tmp_path, record_property)
    generate = _run_check_and_generate(source, output, evidence, context)
    if generate["returncode"] != 0:
        raise _failure("proofquest generate", generate)
    _assert_banach_completeness(source, output)
    _lake_workflow(output, evidence, context)
    _assert_source_pristine(source, evidence, context)


@pytest.mark.integration
@pytest.mark.xfail(strict=True, raises=KnownFLT3Failure)
def test_flt3_full_game(tmp_path, request, record_property):
    if not request.config.getoption("--run-integration"):
        pytest.skip("requires --run-integration; network, git and Lean dependencies")
    _assert_package_under_test()
    source = tmp_path / "source"
    output = tmp_path / "game"
    evidence, context = _clone_repository(FLT3, source, tmp_path, record_property)
    generate = _run_check_and_generate(source, output, evidence, context)
    _raise_known_flt3_if_matched(generate, output, source, evidence, context)
    _assert_flt3_completeness(source, output)
    _lake_workflow(output, evidence, context)
    _assert_source_pristine(source, evidence, context)


def _completed(returncode, stdout="", stderr=""):
    return subprocess.CompletedProcess([], returncode, stdout, stderr)


def _fake_run(results):
    queue = list(results)

    def run(*args, **kwargs):
        return queue.pop(0)

    return run


def test_known_flt3_matcher_accepts_only_reproduced_diagnostic(tmp_path, monkeypatch):
    monkeypatch.setattr(
        subprocess, "run", _fake_run([_completed(0, stdout="## HEAD (no branch)\n")])
    )
    result = {
        "returncode": 1,
        "stderr": f"warning: one\nwarning: two\n{FLT3_KNOWN_DIAGNOSTIC}\n",
        "stdout": "",
    }
    with pytest.raises(KnownFLT3Failure):
        _raise_known_flt3_if_matched(
            result, tmp_path / "game", tmp_path / "source", tmp_path / "evidence", {}
        )


@pytest.mark.parametrize(
    "result",
    [
        {"returncode": 2, "stderr": f"{FLT3_KNOWN_DIAGNOSTIC}\n", "stdout": ""},
        {
            "returncode": 1,
            "stderr": f"{FLT3_KNOWN_DIAGNOSTIC}\nerror: unrelated\n",
            "stdout": "",
        },
        {
            "returncode": 1,
            "stderr": f"warning: ok\n{FLT3_KNOWN_DIAGNOSTIC}\nTraceback: boom\n",
            "stdout": "",
        },
        {
            "returncode": 1,
            "stderr": (
                "error: def:Solution1: copied declaration Solution' is declared "
                "in a source context (module FLT3.FLT3): attribute, notation3 "
                "differently\n"
            ),
            "stdout": "",
        },
    ],
)
def test_known_flt3_matcher_rejects_other_outcomes(tmp_path, result):
    with pytest.raises(WorkflowFailure):
        _raise_known_flt3_if_matched(
            result, tmp_path / "game", tmp_path / "source", tmp_path / "evidence", {}
        )


def test_known_flt3_matcher_returns_on_success(tmp_path):
    result = {"returncode": 0, "stderr": "", "stdout": "generated"}
    assert (
        _raise_known_flt3_if_matched(
            result, tmp_path / "game", tmp_path / "source", tmp_path / "evidence", {}
        )
        is None
    )


def test_known_flt3_matcher_rejects_partial_output(tmp_path):
    output = tmp_path / "game"
    output.mkdir()
    (output / "Game.lean").write_text("partial")
    result = {
        "returncode": 1,
        "stderr": f"{FLT3_KNOWN_DIAGNOSTIC}\n",
        "stdout": "",
    }
    with pytest.raises(WorkflowFailure, match="partial"):
        _raise_known_flt3_if_matched(
            result, output, tmp_path / "source", tmp_path / "evidence", {}
        )


def test_stage_timeout_is_workflow_failure(tmp_path, monkeypatch):
    def timeout(*args, **kwargs):
        raise subprocess.TimeoutExpired(
            args[0], kwargs["timeout"], output=b"partial", stderr=b"diagnostic"
        )

    monkeypatch.setattr(subprocess, "run", timeout)
    context = {
        "repository_url": "https://example.invalid/repo",
        "requested_sha": "0" * 40,
        "actual_sha": None,
    }
    result = _run_stage("stage", ["cmd"], tmp_path, 30, tmp_path / "logs", context)
    assert result["status"] == "timeout"
    record = json.loads((tmp_path / "logs" / "stage.json").read_text())
    assert record["repository_url"] == context["repository_url"]
    assert record["requested_sha"] == context["requested_sha"]
    assert record["actual_sha"] is None
    failure = _failure("stage", result)
    assert context["repository_url"] in str(failure)
    assert context["requested_sha"] in str(failure)


def test_stage_missing_command_is_workflow_failure(tmp_path, monkeypatch):
    def missing(*args, **kwargs):
        raise FileNotFoundError("no such executable")

    monkeypatch.setattr(subprocess, "run", missing)
    result = _run_stage("stage", ["cmd"], tmp_path, 30, tmp_path / "logs", {})
    assert result["status"] == "oserror"
    with pytest.raises(WorkflowFailure):
        raise _failure("stage", result)


def test_clone_failure_reports_requested_sha(tmp_path, monkeypatch):
    monkeypatch.setattr(
        subprocess, "run", _fake_run([_completed(128, stderr="fatal: network")])
    )
    with pytest.raises(WorkflowFailure) as excinfo:
        _clone_repository(FLT3, tmp_path / "source", tmp_path, lambda *a: None)
    assert FLT3["url"] in str(excinfo.value)
    assert FLT3["sha"] in str(excinfo.value)


def test_clone_success_records_actual_sha(tmp_path, monkeypatch):
    calls = []

    def run(argv, **kwargs):
        calls.append(list(map(str, argv)))
        if argv[:2] == ["git", "rev-parse"]:
            return _completed(0, stdout=f"{FLT3['sha']}\n")
        if argv[:2] == ["git", "status"]:
            return _completed(0, stdout="## HEAD (no branch)\n")
        return _completed(0)

    monkeypatch.setattr(subprocess, "run", run)
    evidence, context = _clone_repository(
        FLT3, tmp_path / "source", tmp_path, lambda *a: None
    )
    assert context["actual_sha"] == FLT3["sha"]
    assert calls[0][:2] == ["git", "clone"]
    assert calls[1][:2] == ["git", "checkout"]
    assert evidence.is_dir()


def test_clone_sha_mismatch_is_workflow_failure(tmp_path, monkeypatch):
    other = "f" * 40

    def run(argv, **kwargs):
        if argv[:2] == ["git", "rev-parse"]:
            return _completed(0, stdout=f"{other}\n")
        return _completed(0)

    monkeypatch.setattr(subprocess, "run", run)
    with pytest.raises(WorkflowFailure, match=other):
        _clone_repository(FLT3, tmp_path / "source", tmp_path, lambda *a: None)


def test_lake_build_failure_is_workflow_failure(tmp_path, monkeypatch):
    def run(argv, **kwargs):
        if "build" in argv:
            return _completed(1, stderr="error: build failed")
        return _completed(0)

    monkeypatch.setattr(subprocess, "run", run)
    with pytest.raises(WorkflowFailure, match="lake-build"):
        _lake_workflow(tmp_path / "game", tmp_path / "evidence", {})


def test_missing_generated_output_is_workflow_failure(tmp_path):
    with pytest.raises(WorkflowFailure):
        _assert_nonempty(tmp_path, "Game.lean")


def _write_banach_fixture(source, output):
    all_names = [name for names in BANACH_WORLDS.values() for name in names]
    (source / "BanachSteinhausSokalProof").mkdir(parents=True)
    (source / "BanachSteinhausSokalProof" / "SlidingHump.lean").write_text(
        "namespace NormOverBall\n\n"
        "abbrev NormMap (T : Type*) := T\n\n"
        "end NormOverBall\n\n"
        "namespace BanachSteinhausSokal\n\n"
        + "\n\n".join(
            f"theorem {name} : True := by\n  trivial" for name in all_names
        )
        + "\n\nend BanachSteinhausSokal\n",
        encoding="utf-8",
    )
    (output / "Game" / "Generated").mkdir(parents=True)
    (output / "Game" / "Levels").mkdir(parents=True)
    (output / "Game.lean").write_text(
        "\n".join(f"import Game.Levels.{world}" for world in BANACH_WORLDS)
        + "\n\nMakeGame\n",
        encoding="utf-8",
    )
    (output / "Game" / "Metadata.lean").write_text(
        "import GameServer\n"
        "import Game.Generated.Defs\n"
        "import Game.Generated.TacticDocs\n"
        "import Game.Generated.TheoremDocs\n",
        encoding="utf-8",
    )
    (output / "Game" / "Generated" / "Defs.lean").write_text(
        "import GameServer.Commands\n\n"
        "namespace NormOverBall\n\n"
        "abbrev NormMap (T : Type*) := T\n\n"
        'DefinitionDoc NormOverBall.NormMap as "NormMap"\n\n'
        "end NormOverBall\n",
        encoding="utf-8",
    )
    (output / "Game" / "Generated" / "TacticDocs.lean").write_text(
        "import Game.Generated.Defs\n", encoding="utf-8"
    )
    (output / "Game" / "Generated" / "TheoremDocs.lean").write_text(
        "import Game.Generated.Defs\n", encoding="utf-8"
    )
    (output / "lakefile.lean").write_text(
        'def leanVersion : String := "v4.31.0"\n'
        "def RemoteGameServer : Dependency := {\n"
        "  name := `GameServer\n"
        "}\n"
        "package Game\n"
        'require "leanprover-community" / mathlib @ git leanVersion\n',
        encoding="utf-8",
    )
    (output / "lean-toolchain").write_text(
        BANACH["toolchain"] + "\n", encoding="utf-8"
    )
    (output / ".gitignore").write_text("/.lake\n", encoding="utf-8")
    (output / "README.md").write_text("# game\n", encoding="utf-8")
    previous = None
    for world, names in BANACH_WORLDS.items():
        world_dir = output / "Game" / "Levels" / world
        world_dir.mkdir()
        (output / "Game" / "Levels" / f"{world}.lean").write_text(
            "\n".join(
                f"import Game.Levels.{world}.L{index:02d}_{name}"
                for index, name in enumerate(names, 1)
            )
            + f'\n\nWorld "{world}"\n',
            encoding="utf-8",
        )
        for index, name in enumerate(names, 1):
            imports = "import Game.Metadata\n"
            if previous is not None:
                imports += f"import Game.Levels.{previous}\n"
            (world_dir / f"L{index:02d}_{name}.lean").write_text(
                imports
                + f'\nWorld "{world}"\nLevel {index}\n\n'
                "namespace BanachSteinhausSokal\n\n"
                f'TheoremDoc BanachSteinhausSokal.{name} as "{name}" in "W"\n\n'
                f"Statement {name} : True := by\n  trivial\n\n"
                "end BanachSteinhausSokal\n",
                encoding="utf-8",
            )
            previous = f"{world}.L{index:02d}_{name}"


def test_banach_complete_fixture_passes(tmp_path):
    source = tmp_path / "source"
    output = tmp_path / "game"
    source.mkdir()
    output.mkdir()
    _write_banach_fixture(source, output)
    _assert_banach_completeness(source, output)


def test_banach_missing_world_is_workflow_failure(tmp_path):
    source = tmp_path / "source"
    output = tmp_path / "game"
    source.mkdir()
    output.mkdir()
    _write_banach_fixture(source, output)
    (output / "Game" / "Levels" / "PreliminaryTechnicalResult.lean").unlink()
    with pytest.raises(WorkflowFailure):
        _assert_banach_completeness(source, output)


def test_banach_missing_level_is_workflow_failure(tmp_path):
    source = tmp_path / "source"
    output = tmp_path / "game"
    source.mkdir()
    output.mkdir()
    _write_banach_fixture(source, output)
    (
        output
        / "Game"
        / "Levels"
        / "TheBanachSteinhausTheorem"
        / "L09_uniform_boundedness_principle.lean"
    ).unlink()
    with pytest.raises(WorkflowFailure):
        _assert_banach_completeness(source, output)
