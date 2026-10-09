#!/usr/bin/env python3
"""Compare focused signed SV fixtures against explicit Icarus and one Lean batch.

Lean artifacts are caller-owned: this harness never builds. Set SV_PYTHON
to a Python environment with pyslang 11.x, or use the current interpreter.
--source appends external JSON arrays (or {"sources": [...]}) or text lists
of source paths; relative paths are resolved beside the external list.
Envelopes, oracle output and model output are retained outside the repo.
"""

import argparse
import difflib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


REPO = Path(__file__).resolve().parents[2]
FIXTURES = REPO / "harness" / "sv" / "signed"
RUNNER = REPO / "harness" / "sv" / "conformance" / "runner.lean"
EXTRACTOR = REPO / "extractors" / "sv" / "extract.py"
FINISH_INFO = re.compile(
    r"^.+:[0-9]+: \$finish called at [0-9]+ \([^\r\n)]*\)\r?\n?$"
)


class HarnessError(Exception):
    pass


def run_command(command, workdir, timeout, log_path):
    try:
        result = subprocess.run(
            command, cwd=workdir, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=timeout, check=False,
        )
    except subprocess.TimeoutExpired as error:
        log_path.with_suffix(".stdout").write_bytes(error.stdout or b"")
        log_path.with_suffix(".stderr").write_bytes(error.stderr or b"")
        raise HarnessError("command timed out: %s" % command[0]) from error
    log_path.with_suffix(".stdout").write_bytes(result.stdout)
    log_path.with_suffix(".stderr").write_bytes(result.stderr)
    log_path.with_suffix(".command.json").write_text(
        json.dumps(command, indent=2) + "\n", encoding="utf-8",
    )
    if result.returncode != 0:
        raise HarnessError(
            "command failed (%d): %s; logs: %s"
            % (result.returncode, command[0], log_path)
        )
    return result.stdout.decode("utf-8")


def validate_environment(workdir, timeout):
    for executable in ("iverilog", "vvp", "lake"):
        if shutil.which(executable) is None:
            raise HarnessError("required executable not on PATH: " + executable)
    python = os.environ.get("SV_PYTHON", sys.executable)
    script = (
        "import json, pyslang, sys; "
        "print(json.dumps({'python': sys.version.split()[0], "
        "'pyslang': pyslang.__version__}))"
    )
    identity = json.loads(run_command(
        [python, "-c", script], REPO, timeout, workdir / "frontend",
    ))
    if identity["pyslang"].split(".")[0] != "11":
        raise HarnessError("SV frontend requires pyslang 11.x: " + str(identity))
    print("frontend: %s %s" % (python, identity))
    oracle = run_command(
        ["iverilog", "-V"], REPO, timeout, workdir / "iverilog-version",
    )
    run_command(["vvp", "-V"], REPO, timeout, workdir / "vvp-version")
    print("oracle: " + oracle.splitlines()[0])
    return python


def read_source_list(path):
    path = path.resolve()
    text = path.read_text(encoding="utf-8")
    if text.lstrip().startswith(("[", "{")):
        entries = json.loads(text)
        if isinstance(entries, dict):
            entries = entries.get("sources")
    else:
        entries = [line.strip() for line in text.splitlines() if line.strip()]
    if not isinstance(entries, list) or not entries:
        raise HarnessError("external source list must be a nonempty list: " + str(path))
    if not all(isinstance(entry, str) and entry for entry in entries):
        raise HarnessError("source list entries must be nonempty path strings")
    return [(path.parent / entry).resolve() for entry in entries]


def select_sources(external_lists, selected_names):
    sources = sorted(FIXTURES.glob("*.sv"))
    if selected_names:
        available = {source.stem for source in sources}
        missing = set(selected_names) - available
        if missing:
            raise HarnessError("unknown fixture names: " + ", ".join(sorted(missing)))
        sources = [source for source in sources if source.stem in selected_names]
    for external in external_lists:
        sources.extend(read_source_list(external))
    if not sources:
        raise HarnessError("no sources selected; nothing can be verified")
    if len(sources) != len(set(sources)):
        raise HarnessError("source selection contains duplicate paths")
    if any(not source.is_file() for source in sources):
        raise HarnessError("selected source does not exist")
    return sources


def prepare_case(index, source, python, workdir, timeout):
    case_dir = workdir / ("case-%03d" % index)
    case_dir.mkdir()
    staged = case_dir / "input.sv"
    shutil.copyfile(source, staged)
    run_command(
        [python, str(EXTRACTOR), str(staged)], REPO, timeout,
        case_dir / "extract",
    )
    executable = case_dir / "sim.vvp"
    run_command(
        ["iverilog", "-g2012", "-o", str(executable), str(staged)],
        case_dir, timeout, case_dir / "compile",
    )
    stdout = run_command(
        ["vvp", str(executable)], case_dir, timeout, case_dir / "oracle",
    )
    filtered = "".join(
        line for line in stdout.splitlines(keepends=True)
        if not (line.startswith(str(staged) + ":") and FINISH_INFO.fullmatch(line))
    )
    return {
        "source": str(source), "envelope": str(staged) + ".json",
        "oracle_status": "ok", "oracle_stdout": filtered,
    }


def parse_batch(stdout, expected_paths):
    records = {}
    active = None
    output = []
    for line in stdout.splitlines(keepends=True):
        bare = line.removesuffix("\n")
        if active is None:
            expected = expected_paths[len(records)] if len(records) < len(expected_paths) else None
            if bare != "=== BEGIN " + str(expected):
                raise HarnessError("unexpected batch output: " + repr(line))
            active = expected
            output = []
        elif bare.startswith("=== END " + active + " status="):
            tail = bare[len("=== END " + active + " status="):]
            status, separator, detail = tail.partition(" ")
            if status not in ("ok", "error", "timeout", "unsupported"):
                raise HarnessError("unknown END status: " + status)
            records[active] = {
                "model_status": status, "model_detail": detail,
                "model_stdout": "".join(output),
            }
            active = None
        else:
            output.append(line)
    if active is not None or len(records) != len(expected_paths):
        raise HarnessError("batch omitted or truncated a selected envelope")
    return records


def run_batch(cases, workdir, timeout, fuel):
    envelopes = [case["envelope"] for case in cases]
    listing = workdir / "envelopes.txt"
    listing.write_text("\n".join(envelopes) + "\n", encoding="utf-8")
    stdout = run_command(
        ["lake", "env", "lean", "--run", str(RUNNER), "--batch",
         str(listing), "--fuel", str(fuel)],
        REPO, timeout, workdir / "model-batch",
    )
    return parse_batch(stdout, envelopes)


def compare_cases(cases, records, workdir):
    failed = 0
    for case in cases:
        case.update(records[case["envelope"]])
        matches = (
            case["oracle_status"] == case["model_status"]
            and case["oracle_stdout"] == case["model_stdout"]
        )
        case["verdict"] = "PASS" if matches else "FAIL"
        print("%s %s" % (case["verdict"], case["source"]))
        if not matches:
            failed += 1
            print("  status: oracle=%s model=%s %s" % (
                case["oracle_status"], case["model_status"], case["model_detail"],
            ))
            sys.stdout.writelines(difflib.unified_diff(
                case["oracle_stdout"].splitlines(keepends=True),
                case["model_stdout"].splitlines(keepends=True),
                fromfile="Icarus stdout", tofile="Lean stdout",
            ))
    (workdir / "results.json").write_text(
        json.dumps(cases, indent=2) + "\n", encoding="utf-8",
    )
    print("signed differential: %d PASS / %d FAIL" % (len(cases) - failed, failed))
    return 1 if failed else 0


def parse_arguments():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--source", type=Path, action="append", default=[])
    parser.add_argument("--case", action="append", default=[])
    parser.add_argument("--workdir", type=Path)
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--batch-timeout", type=int, default=600)
    parser.add_argument("--fuel", type=int, default=1000000)
    parser.add_argument("--no-build", action="store_true",
                        help="accepted for consistency; this harness never builds")
    arguments = parser.parse_args()
    if min(arguments.timeout, arguments.batch_timeout, arguments.fuel) <= 0:
        parser.error("timeouts and fuel must be positive")
    return arguments


def main():
    arguments = parse_arguments()
    workdir = arguments.workdir or Path(tempfile.mkdtemp(prefix="sv-signed-"))
    workdir = workdir.resolve()
    if workdir.is_relative_to(REPO):
        raise HarnessError("logs and envelopes must live outside the repository")
    workdir.mkdir(parents=True, exist_ok=True)
    print("workdir: " + str(workdir))
    sources = select_sources(arguments.source, arguments.case)
    python = validate_environment(workdir, arguments.timeout)
    cases = [
        prepare_case(index, source, python, workdir, arguments.timeout)
        for index, source in enumerate(sources)
    ]
    records = run_batch(cases, workdir, arguments.batch_timeout, arguments.fuel)
    return compare_cases(cases, records, workdir)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (HarnessError, OSError, ValueError) as error:
        print("signed differential: COULD NOT VERIFY: " + str(error), file=sys.stderr)
        sys.exit(1)
