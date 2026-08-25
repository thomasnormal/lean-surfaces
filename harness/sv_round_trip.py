#!/usr/bin/env python3
"""SV envelope ROUND-TRIP gate: every committed envelope regenerates byte-identically.

Usage (from the repo root):

    python3 harness/sv_round_trip.py            # gate: exit 1 on any drift
    python3 harness/sv_round_trip.py --list     # show what would run, no extraction

Exit: 0 agreement   1 drift   3 instrument refusal (frontend not pinned)

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

  MATCH            regenerated, byte-identical          (gate passes)
  DIVERGE          regenerated, bytes differ            (gate FAILS)
  REFUSE <cause>   extraction refused, cause named      (gate FAILS if live)
  TIMEOUT          extractor exceeded its deadline      (gate FAILS)

plus a `live` flag on every row.  This is the family verdict vocabulary
(docs/family-architecture.md §5.1-5.3), which this gate now speaks instead
of its own former MATCH/DIFFER/ERROR/SKIP.

**`live` is the load-bearing part, and it is why the old `SKIP` had to go.**
Three CV32E40P phase-1 envelopes record ``source_files`` as absolute paths
into a scratch directory on a DIFFERENT machine, which no checkout can
reproduce.  Those rows are `REFUSE sources-not-in-tree` with **live=false**:
the run never happened, so it is neither agreement nor disagreement.  A
not-live row cannot serialize as a MATCH, which is exactly §5.3's rule that
a vacuous run must not read as agreement.  The summary reports live and
not-live separately so the category can never quietly grow.

CRASH-SAFE BY CONSTRUCTION.  The extractor runs as a SUBPROCESS with a
timeout and an explicit return-code check, because the frontend really does
die: pyslang 11.0.0 aborts with SIGTRAP (rc 133, no diagnostic) on
```unconnected_drive pull2``.  In-process extraction would take this
gate down with it; here it is one REFUSE row naming the file.

THE FRONTEND PIN IS CHECKED BEFORE ANYTHING IS COMPARED, and this gate had
no such check.  It regenerated under ``sys.executable`` -- whatever
interpreter happened to invoke it -- and then compared RAW BYTES.  The
envelopes stamp their frontend family, so under the wrong pyslang every
live envelope becomes a DIVERGE: content drift is REPORTED for what is
actually a frontend change, which is `envelope_fresh`'s "version detector
wearing a freshness label" in this instrument.  Worse, the interpreter was
never checked for pyslang at all, so a pyslang-less one turned every live
envelope into `REFUSE extractor-failed`.

So the pin is resolved FIRST, from `envelope_fresh.MANIFESTS["sv"]` -- one
spelling of the pin, shared with the freshness harness, rather than a
second copy that can drift from it -- and its absence is a REFUSAL (exit 3),
never a comparison made anyway.

**The interpreter checked is the interpreter run.**  An explicit SV_PYTHON
is VALIDATED against the same pin rather than trusted: an override that
bypassed the check would reintroduce exactly the defect the check exists to
remove.
"""

import argparse
import copy
import json
import os
import shutil
import subprocess
import sys
import tempfile

# `harness/` on the path so the pin is IMPORTED rather than re-spelled.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from envelope_fresh import MANIFESTS, Refuse, resolve_frontend  # noqa: E402

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXAMPLES = os.path.join(REPO, "Examples", "system-verilog")
EXTRACT = os.path.join(REPO, "extractors", "sv", "extract.py")

# Generous: the largest committed envelope (cv32e40p_alu_div) extracts in
# about a second, so anything near this is a hang, not slow work.
TIMEOUT_S = 120

# Resolved in main() against the frontend pin, never at import: resolution
# can REFUSE, and a refusal at import time would crash instead of reporting.
SV_PYTHON = None


def pinned_frontend():
    """The interpreter satisfying the SV frontend pin, or `Refuse`.

    An explicit `SV_PYTHON` becomes the ONLY candidate -- so it is checked,
    not obeyed. Anything else would let an override defeat the pin silently,
    which is the failure this function exists to prevent."""
    man = copy.deepcopy(MANIFESTS["sv"])
    override = os.environ.get("SV_PYTHON")
    if override:
        man["frontend"]["candidates"] = [override]
    return resolve_frontend(man)


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

    # THE PIN, BEFORE ANY COMPARISON. A wrong-family frontend changes envelope
    # CONTENT, so comparing under one is a version detector wearing a
    # freshness label. Refusing is not a verdict about the corpus.
    global SV_PYTHON
    try:
        SV_PYTHON = pinned_frontend()
    except Refuse as exc:
        print("sv_round_trip: COULD NOT VERIFY — %s" % exc)
        return 3
    print("frontend: %s (%s)" % (SV_PYTHON, MANIFESTS["sv"]["frontend"]["expect"]))

    rows = []
    n = {"MATCH": 0, "DIVERGE": 0, "REFUSE": 0, "TIMEOUT": 0}
    n_notlive = 0

    for env_path in found:
        rel = os.path.relpath(env_path, REPO)
        try:
            schema, top, recorded, sources = plan(env_path)
        except Skip as exc:
            rows.append(("REFUSE", False, rel,
                         "sources-not-in-tree: %s" % exc))
            n["REFUSE"] += 1; n_notlive += 1
            continue
        except (ValueError, OSError, json.JSONDecodeError) as exc:
            rows.append(("REFUSE", True, rel,
                         "unreadable-envelope: %s" % exc))
            n["REFUSE"] += 1
            continue

        if args.list:
            rows.append((schema, True, rel, "--top %s" % top if top else "(single-file)"))
            continue

        workdir = tempfile.mkdtemp(prefix="sv_round_trip.")
        try:
            produced = regenerate(schema, top, recorded, sources, workdir)
        except RuntimeError as exc:
            detail = str(exc)
            if "timed out" in detail:
                rows.append(("TIMEOUT", True, rel, detail))
                n["TIMEOUT"] += 1
            else:
                rows.append(("REFUSE", True, rel, "extractor-failed: " + detail))
                n["REFUSE"] += 1
            continue
        finally:
            shutil.rmtree(workdir, ignore_errors=True)

        with open(env_path, "rb") as f:
            committed = f.read()
        if produced == committed:
            rows.append(("MATCH", True, rel,
                         "%s%s" % (schema, " --top %s" % top if top else "")))
            n["MATCH"] += 1
        else:
            rows.append(("DIVERGE", True, rel,
                         "%d bytes committed vs %d regenerated"
                         % (len(committed), len(produced))))
            n["DIVERGE"] += 1

    width = max(len(r[2]) for r in rows)
    for verdict, live, rel, note in rows:
        # `live=false` is printed, never folded into the verdict: a reader
        # must be able to see that the row did not exercise anything.
        flag = "" if live else "  [not live]"
        print("%-8s %-*s  %s%s" % (verdict, width, rel, note, flag))

    if args.list:
        print("\n%d envelopes, %d with sources not in tree"
              % (len(found), n_notlive))
        return 0

    live_total = len(rows) - n_notlive
    print("\nMATCH %d  DIVERGE %d  REFUSE %d  TIMEOUT %d"
          % (n["MATCH"], n["DIVERGE"], n["REFUSE"], n["TIMEOUT"]))
    print("%d live of %d envelopes (%d not live: sources not in tree)"
          % (live_total, len(found), n_notlive))

    # A not-live REFUSE does not fail the gate -- it did not run, so it is
    # neither agreement nor disagreement.  Everything else that is not a
    # live MATCH does fail.
    bad = n["DIVERGE"] + n["TIMEOUT"] + (n["REFUSE"] - n_notlive)
    if bad:
        print("sv_round_trip: FAIL")
        return 1
    print("sv_round_trip: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
