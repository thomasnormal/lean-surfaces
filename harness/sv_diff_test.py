#!/usr/bin/env python3
"""Differential checks for the SystemVerilog self-check surface.

Each row in ``harness/sv_cases.json`` names a source file, its module, a
committed self-check oracle result, and ``expect`` (``match`` or ``refuse``).
The model is run by the public self-check runner in one capped Lean process.
When ``SV_ORACLE_CMD`` is set, it is an additional host oracle: the command
template receives ``{file}`` and ``{module}``, and its stdout is compared with
the row's pinned declaration.  The command is deliberately not named here.

The default oracle is the source's declared PASS/output transcript.  This is
the stable sv-tests-2 convention: the source says what a passing test prints;
the repository stores that declaration in the case row so a host simulator is
never silently treated as normative.
"""

import argparse
import json
import os
import shlex
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
CASES = REPO / "harness" / "sv_cases.json"
RUNNER = REPO / "harness" / "sv" / "conformance" / "runner.lean"
TIMED_RUNNER = REPO / "harness" / "sv" / "conformance" / "timed_runner.lean"
def capped(cmd, timeout=600):
    """Run a Lean command under the fleet's cgroup memory/CPU cap.

    An address-space cap makes Lean abort while creating worker threads on the
    shared runner.  Keep the cap in a cgroup instead, matching the lane build
    rule and leaving Lean's address space unconstrained.
    """
    env = os.environ.copy()
    env.setdefault("LEAN_NUM_THREADS", "1")
    return subprocess.run(["systemd-run", "--user", "--scope", "-q",
                           "-p", "MemoryMax=24G", "-p", "CPUQuota=800%"] + list(cmd),
                          cwd=str(REPO), capture_output=True, text=True,
                          timeout=timeout, env=env)


def load_cases(path=CASES):
    doc = json.loads(Path(path).read_text(encoding="utf-8"))
    rows = doc.get("cases")
    if not isinstance(rows, list) or not rows:
        raise SystemExit("sv_diff_test: cases file has no cases")
    for row in rows:
        for key in ("name", "file", "module", "expect", "oracle"):
            if key not in row:
                raise SystemExit("sv_diff_test: row missing %r: %r" % (key, row))
        if row["expect"] not in ("match", "refuse"):
            raise SystemExit("sv_diff_test: bad expect in %s" % row["name"])
        if row["oracle"] not in ("refuse",) and not isinstance(row["oracle"], list):
            raise SystemExit("sv_diff_test: oracle must be a line list or 'refuse' in %s"
                             % row["name"])
    return doc, rows


def source_and_envelope(row):
    source = REPO / row["file"]
    envelope = Path(str(source) + ".json")
    if not source.is_file():
        raise RuntimeError("source does not exist: %s" % row["file"])
    if not envelope.is_file():
        raise RuntimeError("missing generated envelope: %s" % envelope.relative_to(REPO))
    env = json.loads(envelope.read_text(encoding="utf-8"))
    modules = env.get("design", {}).get("modules", [])
    if len(modules) != 1 or modules[0].get("name") != row["module"]:
        raise RuntimeError("%s: envelope module is not %r" %
                           (row["name"], row["module"]))
    return source, envelope


def run_oracle(row, source):
    """Run an optional host oracle, while retaining the committed declaration."""
    # Keep the JSON declaration tied to the source-level self-check oracle;
    # a hand-edited expected line that is absent from the test is a harness
    # error, never a new oracle result.
    if isinstance(row["oracle"], list):
        source_text = source.read_text(encoding="utf-8")
        missing = [line for line in row["oracle"] if line and line not in source_text]
        if missing:
            raise RuntimeError("%s: pinned declaration %r is absent from %s" %
                               (row["name"], missing, row["file"]))
    command = os.environ.get("SV_ORACLE_CMD")
    if not command:
        return list(row["oracle"]) if isinstance(row["oracle"], list) else "refuse", None
    argv = [x.format(file=str(source), module=row["module"]) for x in shlex.split(command)]
    p = subprocess.run(argv, cwd=str(REPO), capture_output=True, text=True,
                       timeout=600)
    host = [line.rstrip("\n") for line in p.stdout.splitlines()]
    declared = row["oracle"]
    if declared != "refuse" and host != declared:
        raise RuntimeError("%s: SV_ORACLE_CMD disagrees with pinned declaration\n"
                           "  declared=%r\n  host=%r\n%s" %
                           (row["name"], declared, host, p.stderr[-1000:]))
    return host, p.returncode


def parse_batch(text):
    rows = {}
    current = None
    for line in text.splitlines():
        if line.startswith("=== BEGIN "):
            current = line[len("=== BEGIN "):]
            rows[current] = {"lines": []}
        elif line.startswith("=== END ") and current is not None:
            tail = line[len("=== END "):]
            marker = " status="
            if marker not in tail:
                raise RuntimeError("malformed runner END line: %s" % line)
            path, status = tail.split(marker, 1)
            entry = rows.pop(current)
            entry["status"], entry["detail"] = status.split(" ", 1)[0], status[len(status.split(" ", 1)[0]):].lstrip()
            rows[path] = entry
            current = None
        elif current is not None:
            rows[current]["lines"].append(line)
    if current is not None:
        raise RuntimeError("runner output ended inside %s" % current)
    return rows


def run_model(envelopes, fuel):
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
        listing = Path(f.name)
        for envelope in envelopes:
            f.write(str(envelope) + "\n")
    try:
        p = capped(["lake", "env", "lean", "-j", "1", "--run", str(RUNNER),
                    "--batch", str(listing), "--fuel", str(fuel)], timeout=1800)
        if p.returncode != 0:
            raise RuntimeError("self-check runner failed (%d):\n%s\n%s" %
                               (p.returncode, p.stdout[-3000:], p.stderr[-3000:]))
        return parse_batch(p.stdout)
    finally:
        try:
            listing.unlink()
        except OSError:
            pass


def run_timed_model(envelopes, fuel, ticks):
    """Run timed rows through the scheduler-facing conformance runner."""
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
        listing = Path(f.name)
        for envelope in envelopes:
            f.write(str(envelope) + "\n")
    try:
        p = capped(["lake", "env", "lean", "-j", "1", "--run", str(TIMED_RUNNER),
                    "--batch", str(listing), "--fuel", str(fuel),
                    "--ticks", str(ticks)], timeout=1800)
        if p.returncode != 0:
            raise RuntimeError("timed self-check runner failed (%d):\n%s\n%s" %
                               (p.returncode, p.stdout[-3000:], p.stderr[-3000:]))
        return parse_batch(p.stdout)
    finally:
        try:
            listing.unlink()
        except OSError:
            pass


def run_models(resolved, fuel):
    """Run standard and timed rows, preserving one merged path-indexed view."""
    model = {}
    standard = [item for item in resolved if item[0].get("mode", "self-check") != "timed"]
    timed = [item for item in resolved if item[0].get("mode", "self-check") == "timed"]
    if standard:
        model.update(run_model([item[2] for item in standard], fuel))
    by_ticks = {}
    for item in timed:
        ticks = int(item[0].get("ticks", 16))
        by_ticks.setdefault(ticks, []).append(item)
    for ticks, items in by_ticks.items():
        model.update(run_timed_model([item[2] for item in items], fuel, ticks))
    return model


def check_row(row, source, envelope, model_entry, oracle):
    status = model_entry["status"]
    lines = model_entry["lines"]
    if row["expect"] == "refuse":
        ok = status == "unsupported"
        detail = model_entry.get("detail", "")
        if ok and not detail:
            ok = False
        return ok, "REFUSE" if ok else "model returned %s (%s)" % (status, detail)
    if oracle == "refuse":
        return False, "case marked match but oracle is refuse"
    ok = status == "ok" and lines == oracle
    if ok:
        return True, "MATCH"
    return False, "model=%s %r, oracle=%r" % (status, lines, oracle)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--cases", default=str(CASES))
    ap.add_argument("--case")
    ap.add_argument("--fuel", type=int, default=1000000)
    ap.add_argument("--json", action="store_true", help="emit machine-readable summary")
    args = ap.parse_args(argv)
    doc, rows = load_cases(args.cases)
    if args.case:
        rows = [r for r in rows if r["name"] == args.case]
        if not rows:
            raise SystemExit("sv_diff_test: no case named %s" % args.case)
    resolved = []
    envelopes = []
    for row in rows:
        source, envelope = source_and_envelope(row)
        oracle, host_rc = run_oracle(row, source)
        resolved.append((row, source, envelope, oracle, host_rc))
        envelopes.append(envelope)
    model = run_models(resolved, args.fuel)
    results = []
    for row, source, envelope, oracle, host_rc in resolved:
        entry = model.get(str(envelope))
        if entry is None:
            raise RuntimeError("runner omitted %s" % envelope)
        ok, detail = check_row(row, source, envelope, entry, oracle)
        results.append({"name": row["name"], "file": row["file"],
                        "expect": row["expect"], "verdict": "MATCH" if ok else "DIVERGE",
                        "model_status": entry["status"],
                        "model_lines": entry["lines"],
                        "detail": detail, "host_oracle": host_rc is not None})
    summary = {"rows": len(results),
               "agree": sum(r["verdict"] == "MATCH" and r["expect"] == "match" for r in results),
               "disagree": sum(r["verdict"] == "DIVERGE" for r in results),
               "recorded_refusals": sum(r["verdict"] == "MATCH" and r["expect"] == "refuse" for r in results),
               "results": results, "oracle": "sv-tests-2 declarations"}
    if args.json:
        print(json.dumps(summary, sort_keys=True))
    else:
        print("oracle: sv-tests-2 self-check declarations")
        print("%-28s %-8s %-10s %s" % ("CASE", "EXPECT", "VERDICT", "DETAIL"))
        print("-" * 80)
        for r in results:
            print("%-28s %-8s %-10s %s" % (r["name"], r["expect"], r["verdict"], r["detail"]))
        print("-" * 80)
        print("%d rows: %d agree, %d disagree, %d recorded refusals" %
              (summary["rows"], summary["agree"], summary["disagree"], summary["recorded_refusals"]))
    return 0 if summary["disagree"] == 0 else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, OSError, subprocess.SubprocessError) as exc:
        print("sv_diff_test: ERROR: %s" % exc, file=sys.stderr)
        sys.exit(2)
