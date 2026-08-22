#!/usr/bin/env python3
"""SV envelope ROUND-TRIP gate: every committed envelope regenerates byte-identically.

Usage (from the repo root):

    python3 harness/sv_round_trip.py            # gate: exit 1 on any drift
    python3 harness/sv_round_trip.py --list     # show what would run, no extraction

Walks every committed ``Examples/system-verilog/**/*.sv.json``, re-runs
``extractors/sv/extract.py`` on its recorded source(s), and compares the
result BYTE FOR BYTE against the committed file.

THE LAW THIS ENCODES ("read the mode out of the artefact, never assume it").
An envelope records the mode it was produced in, and a round-trip that
guesses the mode produces a silent wrong answer.  Two ways to get it wrong
were both hit for real while founding this lane (docs/sv-charter.md §0, §7):

  * guessing the SCHEMA — ``sv-0.2`` envelopes need ``--top``; comparing
    them against single-file ``sv-0.1`` output reported 12 spurious
    failures;
  * guessing the TOP MODULE from the FILE NAME — the file
    ``cv32e40p_register_file_ff.sv`` declares module
    ``cv32e40p_register_file``, so a filename-derived ``--top`` reported a
    19th spurious failure and was misdiagnosed as a missing dependency.

So the mode, the top module and the source list are read from the envelope's
own ``schema_version`` / ``top`` / ``source_files`` fields.  Nothing is
inferred from a path.

NEVER SILENT.  Each envelope ends in exactly one of:

  MATCH   regenerated, byte-identical             (gate passes)
  DIFFER  regenerated, bytes differ               (gate FAILS)
  ERROR   extractor crashed / timed out / no out  (gate FAILS)
  SKIP    recorded sources are not in this tree   (reported, with the
          reason and the missing path; does NOT fail the gate)

SKIP exists for the three CV32E40P phase-1 envelopes whose ``source_files``
are absolute paths into a scratch directory on a DIFFERENT machine, which no
checkout can reproduce.  A SKIP always prints why, and the summary counts
them, so the category can never quietly grow.

CRASH-SAFE BY CONSTRUCTION.  The extractor runs as a SUBPROCESS with a
timeout and an explicit return-code check, because the frontend really does
die: pyslang 11.0.0 aborts with SIGTRAP (rc 133, no diagnostic) on
```unconnected_drive pull2``.  In-process extraction would take this
gate down with it; here it is one ERROR row naming the file.

Requires python3.12 + pyslang 11.x for the extractor subprocess (see
docs/sv-charter.md §1.1).  Set SV_PYTHON to choose the interpreter;
defaults to the one running this script.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXAMPLES = os.path.join(REPO, "Examples", "system-verilog")
EXTRACT = os.path.join(REPO, "extractors", "sv", "extract.py")

# Generous: the largest committed envelope (cv32e40p_alu_div) extracts in
# about a second, so anything near this is a hang, not slow work.
TIMEOUT_S = 120

SV_PYTHON = os.environ.get("SV_PYTHON") or sys.executable


class Skip(Exception):
    """Recorded sources are not reproducible in this tree."""


def envelopes():
    """Every committed *.sv.json under Examples/system-verilog, sorted."""
    out = []
    for root, _dirs, files in os.walk(EXAMPLES):
        for fn in files:
            if fn.endswith(".sv.json"):
                out.append(os.path.join(root, fn))
    return sorted(out)


def plan(env_path):
    """Read the envelope's OWN record of how it was produced.

    Returns (schema, top, [abs source paths]).  Raises Skip if a recorded
    source is not present in this tree.
    """
    with open(env_path, encoding="utf-8") as f:
        env = json.load(f)

    schema = env.get("schema_version")
    if schema not in ("sv-0.1", "sv-0.2"):
        raise ValueError("unknown schema_version %r" % (schema,))

    if schema == "sv-0.1":
        recorded = [env.get("source_file")]
        top = None
    else:
        top = env.get("top")
        if not top:
            raise ValueError("sv-0.2 envelope with no 'top' field")
        recorded = [s.get("path") if isinstance(s, dict) else s
                    for s in env.get("source_files") or []]
    if not recorded or any(s is None for s in recorded):
        raise ValueError("envelope records no usable source list")

    # A recorded path may be repo-relative (the in-tree case) or absolute
    # (the phase-1 case, pointing at another machine).  Resolve repo-relative
    # first, then fall back to a sibling of the envelope.
    resolved = []
    for s in recorded:
        cand = os.path.join(REPO, s)
        if os.path.exists(cand):
            resolved.append(cand)
            continue
        sib = os.path.join(os.path.dirname(env_path), os.path.basename(s))
        if os.path.exists(sib):
            resolved.append(sib)
            continue
        raise Skip(s)
    return schema, top, recorded, resolved


def regenerate(schema, top, recorded, sources, workdir):
    """Run the extractor as a subprocess; return the produced bytes.

    THE PATH STRING IS PART OF THE ENVELOPE.  ``source_file`` /
    ``source_files`` record the path exactly as it was spelled on the
    command line, so regenerating with a different spelling changes the
    output even when the AST is identical.  (Measured: passing absolute
    paths instead of the recorded repo-relative ones made all 18
    in-tree envelopes differ, by exactly the length delta of the strings.)

    So the gate rebuilds a MIRROR of the recorded layout inside a scratch
    directory and runs there with the recorded relative paths verbatim.
    That also keeps the gate from ever writing into the repository.

    Raises RuntimeError with a precise cause on crash, timeout or no output.
    """
    for rec, real in zip(recorded, sources):
        if os.path.isabs(rec):
            raise RuntimeError("recorded source path is absolute: %s" % rec)
        dst = os.path.join(workdir, rec)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copyfile(real, dst)

    if schema == "sv-0.2":
        out_path = os.path.join(workdir, "out.json")
        cmd = [SV_PYTHON, EXTRACT, "--top", top] + list(recorded) + ["-o", out_path]
    else:
        # sv-0.1 has no -o: it writes <source>.json beside the source, which
        # inside the mirror is the scratch copy, not the committed file.
        out_path = os.path.join(workdir, recorded[0]) + ".json"
        cmd = [SV_PYTHON, EXTRACT, recorded[0]]

    try:
        proc = subprocess.run(cmd, capture_output=True, timeout=TIMEOUT_S,
                              cwd=workdir)
    except subprocess.TimeoutExpired:
        raise RuntimeError("extractor timed out after %ds" % TIMEOUT_S)

    if proc.returncode != 0:
        detail = (proc.stderr or b"").decode("utf-8", "replace").strip()
        detail = detail.splitlines()[-1] if detail else "(no stderr)"
        if proc.returncode < 0 or proc.returncode > 128:
            # 133 = 128+5 = SIGTRAP is the known pyslang abort.
            raise RuntimeError("extractor KILLED by signal (rc=%d): %s"
                               % (proc.returncode, detail))
        raise RuntimeError("extractor failed (rc=%d): %s"
                           % (proc.returncode, detail))

    if not os.path.exists(out_path):
        raise RuntimeError("extractor exited 0 but wrote no envelope")
    with open(out_path, "rb") as f:
        return f.read()


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--list", action="store_true",
                    help="show the plan for each envelope; extract nothing")
    args = ap.parse_args()

    found = envelopes()
    if not found:
        # An empty sweep is an instrument fault, never a finding.
        print("sv_round_trip: FAIL — no envelopes found under %s" % EXAMPLES)
        return 1
    if not os.path.exists(EXTRACT):
        print("sv_round_trip: FAIL — extractor missing: %s" % EXTRACT)
        return 1

    rows, n_match, n_differ, n_error, n_skip = [], 0, 0, 0, 0

    for env_path in found:
        rel = os.path.relpath(env_path, REPO)
        try:
            schema, top, recorded, sources = plan(env_path)
        except Skip as exc:
            rows.append(("SKIP", rel, "source not in tree: %s" % exc))
            n_skip += 1
            continue
        except (ValueError, OSError, json.JSONDecodeError) as exc:
            rows.append(("ERROR", rel, "unreadable envelope: %s" % exc))
            n_error += 1
            continue

        if args.list:
            rows.append((schema, rel, "--top %s" % top if top else "(single-file)"))
            continue

        workdir = tempfile.mkdtemp(prefix="sv_round_trip.")
        try:
            produced = regenerate(schema, top, recorded, sources, workdir)
        except RuntimeError as exc:
            rows.append(("ERROR", rel, str(exc)))
            n_error += 1
            continue
        finally:
            shutil.rmtree(workdir, ignore_errors=True)

        with open(env_path, "rb") as f:
            committed = f.read()
        if produced == committed:
            rows.append(("MATCH", rel, "%s%s" % (schema, " --top %s" % top if top else "")))
            n_match += 1
        else:
            rows.append(("DIFFER", rel,
                         "%d bytes committed vs %d regenerated"
                         % (len(committed), len(produced))))
            n_differ += 1

    width = max(len(r[1]) for r in rows)
    for status, rel, note in rows:
        print("%-6s %-*s  %s" % (status, width, rel, note))

    if args.list:
        print("\n%d envelopes, %d skipped (sources not in tree)" % (len(found), n_skip))
        return 0

    print("\nMATCH %d  DIFFER %d  ERROR %d  SKIP %d  (of %d envelopes)"
          % (n_match, n_differ, n_error, n_skip, len(found)))
    if n_differ or n_error:
        print("sv_round_trip: FAIL")
        return 1
    print("sv_round_trip: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
