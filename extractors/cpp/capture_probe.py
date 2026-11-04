#!/usr/bin/env python3
"""Capture pinned declaration observations and positive-input stability receipts."""

import argparse
import json
import math
import os
from pathlib import Path
import shutil
import sys
import tempfile

import extract as translation
from capture_support import (
    CaptureError, atomic_publish, controlled_environment, hash_file,
    run_process, strict_probe,
)


SCHEMA_VERSION = "cpp-probe-capture-0.1"
PROFILE_ID = "cpp23-clang-probe-capture-0.1"
PROBE_SCHEMA = "cpp-canonical-probe-0.3"
TOOL_VERSION = "leancpp-probe-capture-0.1"
ENVIRONMENT_POLICY = "controlled-clang-environment-0.1"


def image(path):
    logical = Path(path).absolute()
    resolved = logical.resolve(strict=True)
    if not resolved.is_file():
        raise CaptureError(f"tool image is not a file: {logical}")
    return {
        "path": str(logical), "resolved_path": str(resolved),
        "sha256": hash_file(resolved), "byte_count": resolved.stat().st_size,
    }


def tool_images(clang, plugin, runtime_libraries):
    executable = shutil.which(str(clang))
    if executable is None:
        raise CaptureError(f"frontend unavailable: {clang}")
    libraries = [image(path) for path in runtime_libraries]
    identities = [entry["resolved_path"] for entry in libraries]
    if len(identities) != len(set(identities)):
        raise CaptureError("duplicate declared runtime-library image")
    return {
        "compiler": image(executable), "plugin": image(plugin),
        "declared_runtime_libraries": libraries,
    }


def producer_identity():
    directory = Path(__file__).resolve().parent
    return {
        "version": TOOL_VERSION,
        "sources": [image(directory / name) for name in (
            "capture_probe.py", "capture_support.py", "extract.py")],
        "interpreter": image(sys.executable),
    }


def check_images(before):
    for entry in before:
        after = image(entry["path"])
        if entry != after:
            raise CaptureError(f"declared tool image changed during capture: {entry['path']}")


def flatten_images(frontend, producer):
    return [frontend["compiler"], frontend["plugin"],
            *frontend["declared_runtime_libraries"],
            *producer["sources"], producer["interpreter"]]


def resource_walk_error(error):
    raise CaptureError(f"resource directory unavailable: {error}")


def resource_manifest(directory):
    entries = []
    for root, directories, files in os.walk(directory, followlinks=False,
                                            onerror=resource_walk_error):
        directories.sort()
        files.sort()
        for name in directories + files:
            path = Path(root) / name
            relative = str(path.relative_to(directory))
            if path.is_symlink():
                entries.append({"path": relative, "kind": "symlink", "target": os.readlink(path)})
            elif path.is_file():
                entries.append({"path": relative, "kind": "file", "sha256": hash_file(path),
                                "byte_count": path.stat().st_size})
            elif path.is_dir():
                entries.append({"path": relative, "kind": "directory"})
            else:
                raise CaptureError(f"unsupported resource input: {path}")
    return entries


def artifact(directory, filename):
    path = directory / filename
    return {"path": filename, "byte_count": path.stat().st_size,
            "sha256": hash_file(path)}


def utf8_text(directory, record):
    try:
        return (directory / record["stdout"]).read_text(encoding="utf-8")
    except UnicodeError as error:
        raise CaptureError(f"frontend observation is not UTF-8: {error}") from error


def single_line(directory, record, label):
    lines = utf8_text(directory, record).splitlines()
    if len(lines) != 1 or not lines[0]:
        raise CaptureError(f"{label}: expected one nonempty frontend observation")
    return lines[0]


def dependencies(path, cwd):
    try:
        return translation.dependency_paths(path.read_text(encoding="utf-8"), cwd)
    except (translation.ExtractionError, UnicodeError) as error:
        raise CaptureError(f"invalid dependency record: {error}") from error


def input_manifest(paths):
    try:
        return translation.manifest(paths)
    except translation.ExtractionError as error:
        raise CaptureError(str(error)) from error


def write_record(path, record):
    try:
        contents = json.dumps(record, ensure_ascii=False, allow_nan=False,
                              separators=(",", ":")) + "\n"
        path.write_text(contents, encoding="utf-8")
    except (ValueError, UnicodeError) as error:
        raise CaptureError(f"receipt cannot be encoded without loss: {error}") from error


def observe_toolchain(base, environment, staging, timeout, memory_mib):
    commands = [
        ("version", [base[0], "--no-default-config", "--version"]),
        ("target", [*base, "-dumpmachine"]),
        ("resource", [*base, "-print-resource-dir"]),
        ("predefines", [*base, "-dM", "-E", "-"]),
    ]
    records = {}
    for label, command in commands:
        records[label] = run_process(command, Path.cwd(), environment, staging,
                                     label, timeout, memory_mib)
    version = utf8_text(staging, records["version"])
    first = version.splitlines()[0] if version else ""
    if first != "clang version 21.1.8" and not first.startswith("clang version 21.1.8 "):
        raise CaptureError("capture requires explicitly pinned Clang 21.1.8")
    resource_path = single_line(staging, records["resource"], "resource directory")
    resource = Path(resource_path).resolve(strict=True)
    if not resource.is_dir():
        raise CaptureError("frontend resource directory is not a directory")
    return records, {
        "version": version,
        "target": single_line(staging, records["target"], "target"),
        "resource_directory": {
            "path": resource_path, "resolved_path": str(resource),
            "before": resource_manifest(resource),
            "scope": "observed-tree-without-symlink-directory-traversal",
            "closure": "unestablished",
        },
    }


def observe_inputs(base, source_argument, environment, staging, timeout, memory_mib):
    command = [*base, "-M", "-MT", "cpp-input", "-MF",
               str(staging / "discovery.d"), source_argument]
    record = run_process(command, Path.cwd(), environment, staging, "discovery",
                         timeout, memory_mib)
    paths = dependencies(staging / "discovery.d", Path.cwd())
    return record, paths, input_manifest(paths)


def probe_command(base, source_argument, plugin, staging):
    return [*base, "-fsyntax-only", "-Xclang", "-load", "-Xclang", plugin,
            "-Xclang", "-plugin", "-Xclang", "leancpp-canonical-probe",
            "-MD", "-MT", "cpp-input", "-MF", str(staging / "inputs.d"),
            source_argument]


def verify_inputs(staging, paths, before, source):
    actual = dependencies(staging / "inputs.d", Path.cwd())
    after = input_manifest(actual)
    if paths != actual or before != after:
        raise CaptureError("positive translation inputs changed during capture")
    source_entry = next((entry for entry in before if entry["path"] == str(source)), None)
    if source_entry is None:
        raise CaptureError("main source absent from positive dependency manifest")
    return actual, after, source_entry


def receipt(staging, frontend, producer, observations, discovery, probe_record,
            paths, before, actual, after, source_argument, source_entry, metadata,
            environment):
    frontend.update({
        **observations,
        "compiled_frontend": metadata["compiled_frontend"],
        "llvm_headers": metadata["llvm_headers"],
        "runtime_frontend": metadata["runtime_frontend"],
        "image_closure": "unestablished",
    })
    processes = [*observations["processes"], discovery, probe_record]
    payloads = {
        "probe": artifact(staging, "probe.json"),
        "stderr": artifact(staging, "stderr.txt"),
        "dependencies": artifact(staging, "inputs.d"),
        "discovery_dependencies": artifact(staging, "discovery.d"),
    }
    for process in processes:
        for stream in ("stdout", "stderr"):
            filename = process[stream]
            if filename not in ("probe.json", "stderr.txt"):
                payloads[filename] = artifact(staging, filename)
    return {
        "schema_version": SCHEMA_VERSION, "profile_id": PROFILE_ID,
        "edition": "c++23", "probe_schema": PROBE_SCHEMA, "producer": producer,
        "payloads": payloads,
        "launch": {
            "executable": frontend["compiler"]["path"],
            "resolved_executable": frontend["compiler"]["resolved_path"],
            "argv": probe_record["argv"], "cwd": probe_record["cwd"],
            "environment_policy": ENVIRONMENT_POLICY, "environment": environment,
        },
        "frontend": frontend,
        "source": {"logical_command_path": source_argument, **source_entry},
        "positive_inputs": {
            "discovery_command": discovery["argv"], "discovery_manifest": paths,
            "before": before, "actual_manifest": actual, "after": after,
            "paths_equal": True, "hashes_equal": True,
            "discovery_payload": artifact(staging, "discovery.d"),
        },
        "completion": {
            "exit_status": 0, "timed_out": False,
            "processes": processes,
            "bounds_scope": "frontend-subprocesses-only",
        },
        "closure_limits": {
            "input_world": "unestablished", "runtime_image_closure": "unestablished",
            "effective_cc1": "unestablished",
            "ordinary_source_profile": "unestablished",
            "guarantee": "observed-positive-input-stability",
            "semantic_admission": False, "runtime_admission": False,
        },
    }


def capture_staged(source_argument, source, staging, frontend, producer,
                   environment, flags, timeout, memory_mib):
    base = [frontend["compiler"]["path"], "--no-default-config", "-x", "c++",
            "-std=c++23", "-pedantic-errors", *translation.frontend_flags(flags)]
    records, observations = observe_toolchain(base, environment, staging, timeout, memory_mib)
    observations["processes"] = list(records.values())
    discovery, paths, before = observe_inputs(base, source_argument, environment,
                                              staging, timeout, memory_mib)
    command = probe_command(base, source_argument, frontend["plugin"]["path"], staging)
    probe_record = run_process(command, Path.cwd(), environment, staging, "probe",
                               timeout, memory_mib)
    (staging / probe_record["stdout"]).rename(staging / "probe.json")
    (staging / probe_record["stderr"]).rename(staging / "stderr.txt")
    probe_record["stdout"] = "probe.json"
    probe_record["stderr"] = "stderr.txt"
    write_record(staging / "probe.process.json", probe_record)
    document = strict_probe(staging / "probe.json")
    actual, after, source_entry = verify_inputs(staging, paths, before, source)
    resource = observations["resource_directory"]
    resource["after"] = resource_manifest(Path(resource["resolved_path"]))
    if resource["before"] != resource["after"]:
        raise CaptureError("observed resource-directory inputs changed during capture")
    check_images(flatten_images(frontend, producer))
    record = receipt(staging, frontend, producer, observations, discovery, probe_record,
                     paths, before, actual, after, source_argument, source_entry,
                     document["metadata"], environment)
    write_record(staging / "capture.json", record)
    for binding in record["payloads"].values():
        if artifact(staging, binding["path"]) != binding:
            raise CaptureError("output artifact changed before publication")
    return record


def capture(source, output, *, clang="clang++", plugin, runtime_libraries=(),
            flags=(), timeout=300, memory_mib=16384):
    staging = None
    try:
        if sys.platform != "linux":
            raise CaptureError("initial observational capture profile requires Linux")
        if type(timeout) not in (int, float) or not math.isfinite(timeout) or timeout <= 0:
            raise CaptureError("process timeout must be a positive finite number")
        if type(memory_mib) is not int or memory_mib <= 0:
            raise CaptureError("process timeout and memory bound must be positive")
        flags = list(flags)
        translation.validate_flags(flags)
        source_argument = os.fspath(source)
        source_argument.encode("utf-8")
        if source_argument.startswith(("-", "@")):
            raise CaptureError("source argument cannot be an option, response file or stdin")
        source_path = Path(source_argument).resolve(strict=True)
        if not source_path.is_file():
            raise CaptureError("source must be a readable file")
        destination = Path(output).absolute()
        if destination.exists() or destination.is_symlink():
            raise CaptureError(f"capture output already exists: {destination}")
        environment = controlled_environment()
        frontend = tool_images(clang, plugin, runtime_libraries)
        producer = producer_identity()
        staging = Path(tempfile.mkdtemp(prefix=f".{destination.name}.staging.",
                                        dir=destination.parent))
        capture_staged(source_argument, source_path, staging, frontend, producer,
                       environment, flags, timeout, memory_mib)
        atomic_publish(staging, destination)
        return destination
    except (CaptureError, translation.ExtractionError, OSError, ValueError) as error:
        detail = str(error)
        if staging is not None and staging.exists():
            write_record(staging / "failure.json", {
                "schema_version": "cpp-probe-capture-failure-0.1", "state": "failed",
                "error": detail, "successful_publication": False,
            })
            detail += f"; failed capture retained at {staging}"
        raise CaptureError(detail) from error


def main(argv=None):
    arguments = list(sys.argv[1:] if argv is None else argv)
    split = arguments.index("--") if "--" in arguments else len(arguments)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source")
    parser.add_argument("--out-dir", required=True)
    parser.add_argument("--plugin", required=True)
    parser.add_argument("--runtime-library", action="append", default=[])
    parser.add_argument("--clang", default=os.environ.get("LEANCPP_CLANG", "clang++"))
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("--memory-mib", type=int, default=16384)
    options = parser.parse_args(arguments[:split])
    try:
        destination = capture(options.source, options.out_dir, clang=options.clang,
                              plugin=options.plugin, runtime_libraries=options.runtime_library,
                              flags=arguments[split + 1:], timeout=options.timeout,
                              memory_mib=options.memory_mib)
        print(destination)
        return 0
    except CaptureError as error:
        print(f"leancpp capture refused: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
