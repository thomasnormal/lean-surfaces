#!/usr/bin/env python3.12
"""Corpus census for the lean_models SV lane: run the extract.py pipeline
in-process over the IEEE 1800-2023 conformance corpus (sv-tests-2) and
measure axis-1/2 coverage on real code.

Usage (from the repo root):

    python3.12 extractors/sv/census.py                 # full census
    python3.12 extractors/sv/census.py --recheck       # determinism check
    python3.12 extractors/sv/census.py --limit 500     # smoke run

Outputs (full run):
  * harness/sv/conformance/census.json  — per-file classification + summary
  * harness/sv/conformance/unlockable.txt — the chapter-4/6/11 unlockable
    set (see below), one corpus-relative path per line

Classification per .sv file under <corpus>/chapter-*/:
  * skip_include — the source uses a real `include directive (multi-file
    test; extract.py compiles single files with no include path, so the
    envelope would be built from a partial parse — skip with reason)
  * error   — the pipeline raised (pyslang/driver exception or timeout);
    should be ~0, every one is an extractor bug to report
  * clean   — envelope has zero Unsupported nodes
  * partial — envelope has Unsupported nodes; the distinct sv_kind values
    are recorded (the construct-frequency table over these is the
    implementation priority queue)

Adapter (pass 2, "unlockable") analysis — computed for every parsed file:
the self-check tier the Adapter phase builds extends M0 with exactly
  {initial blocks, $display/$finish calls, string literals,
   local variable declarations (M0-typed: unsigned 4-state scalar/[W-1:0])}
A file is UNLOCKABLE iff it is `partial` and re-walking its elaborated AST
with those four constructs treated as supported (descending into initial
bodies, which the envelope collapses into a single Unsupported node) leaves
zero blockers. Everything inside an initial body must otherwise be M0
vocabulary (begin/end, =, <=, if/else, M0 expressions); $display/$finish
args may be string literals or M0 expressions; local decls must be M0-typed
with M0/string initializers. The residual blockers of non-unlockable files
are recorded in `adapter_blockers` (tags mirror extract.py's sv_kind
convention, plus `Call:<name>` for non-$display/$finish calls).

Determinism: --recheck re-runs a fixed-seed 200-file random sample against
the stored census.json and asserts identical classification.
"""

import argparse
import json
import os
import random
import re
import signal
import sys
import time
from collections import Counter
from multiprocessing import Pool

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DEFAULT_CORPUS = "/home/thomas-ahle/mox/sv-conformance/sv-tests-2/tests"
OUT_DIR = os.path.join(REPO, "harness", "sv", "conformance")
CENSUS_JSON = os.path.join(OUT_DIR, "census.json")
UNLOCKABLE_TXT = os.path.join(OUT_DIR, "unlockable.txt")

SEED = 20260721
SAMPLE_SIZE = 200
FILE_TIMEOUT_S = 90
ADAPTER_CALLS = ("$display", "$finish")
DEEP_DIVE_CHAPTERS = ("chapter-4", "chapter-6", "chapter-11")

# A *real* include directive at the start of a line (`include "f" / <f> /
# `MACRO). Mentions inside // comments or :description: lines don't match.
INCLUDE_RE = re.compile(r'^\s*`include\s*(["<`])', re.M)
META_RE = re.compile(r'^:(name|tags|type):[ \t]*(.*?)[ \t]*$', re.M)


class FileTimeout(Exception):
    pass


def _on_alarm(signum, frame):
    raise FileTimeout("per-file timeout (%ds)" % FILE_TIMEOUT_S)


# ---------------------------------------------------------------------------
# Worker
# ---------------------------------------------------------------------------

_CORPUS = None
extract = None  # the extract.py module, imported in the worker initializer
_pyslang_ast = None


def _init_worker(corpus):
    global _CORPUS, extract, _pyslang_ast
    _CORPUS = corpus
    sys.path.insert(0, os.path.join(REPO, "extractors", "sv"))
    import extract as _e
    import pyslang.ast as _a
    extract = _e
    _pyslang_ast = _a
    signal.signal(signal.SIGALRM, _on_alarm)


def kinds_in(node):
    """All sv_kind values of Unsupported nodes in a converted dict tree."""
    out = []
    if isinstance(node, dict):
        if node.get("kind") == "Unsupported":
            out.append(node.get("sv_kind", "?"))
        for v in node.values():
            out.extend(kinds_in(v))
    elif isinstance(node, list):
        for v in node:
            out.extend(kinds_in(v))
    return out


def _minus_string(kinds):
    """String literals are in the adapter tier — not blockers in pass 2."""
    return [k for k in kinds if k != "StringLiteral"]


def adapter_expr(sm, e):
    return _minus_string(kinds_in(extract.convert_expr(sm, e)))


def adapter_stmt(sm, s):
    """Blocker tags of a statement under the adapter tier (M0 vocabulary
    + $display/$finish + string literals + M0-typed local var decls)."""
    if getattr(s, "bad", False):
        return ["InvalidStatement"]
    cn = type(s).__name__

    if cn == "BlockStatement":
        from pyslang.ast import StatementBlockKind
        if s.blockKind != StatementBlockKind.Sequential:
            return ["BlockStatement:" + str(s.blockKind).split(".")[-1]]
        body = s.body
        items = body.list if type(body).__name__ == "StatementList" else [body]
        out = []
        for x in items:
            out.extend(adapter_stmt(sm, x))
        return out

    if cn == "StatementList":
        out = []
        for x in s.list:
            out.extend(adapter_stmt(sm, x))
        return out

    if cn == "VariableDeclStatement":
        sym = s.symbol
        w, reason = extract.type_width(sym.type)
        out = [] if w is not None else ["VariableDeclStatement:" + reason]
        init = getattr(sym, "initializer", None)
        if init is not None:
            out.extend(adapter_expr(sm, init))
        return out

    if cn == "ExpressionStatement":
        e = s.expr
        if type(e).__name__ == "CallExpression":
            name = None
            try:
                name = e.subroutineName
            except Exception:
                pass
            if name in ADAPTER_CALLS:
                out = []
                try:
                    args = list(e.arguments)
                except Exception:
                    return ["Call:" + name + ":args"]
                for a in args:
                    out.extend(adapter_expr(sm, a))
                return out
            return ["Call:" + (name if name else type(e).__name__)]
        return _minus_string(kinds_in(extract.convert_stmt(sm, s)))

    if cn == "ConditionalStatement":
        from pyslang.ast import UniquePriorityCheck
        if s.check != UniquePriorityCheck.None_:
            return ["ConditionalStatement:" + str(s.check).split(".")[-1]]
        conds = s.conditions
        if len(conds) != 1:
            return ["ConditionalStatement:multi"]
        if conds[0].pattern is not None:
            return ["ConditionalStatement:pattern"]
        out = adapter_expr(sm, conds[0].expr)
        out.extend(adapter_stmt(sm, s.ifTrue))
        if s.ifFalse is not None:
            out.extend(adapter_stmt(sm, s.ifFalse))
        return out

    if cn == "TimedStatement":
        return ["TimedStatement:" + type(s.timing).__name__]

    # Everything else (loops, case, fork, empty, ...): what extract.py says.
    return _minus_string(kinds_in(extract.convert_stmt(sm, s)))


def adapter_proc_blockers(sm, m):
    """Blocker tags of one procedural block under the adapter tier.
    Initial blocks are descended into; always* mirror extract.py's gating
    but with adapter-aware bodies (so $display inside always is fine)."""
    from pyslang.ast import EdgeKind, ProceduralBlockKind
    pk = m.procedureKind
    if pk == ProceduralBlockKind.Initial:
        return adapter_stmt(sm, m.body)
    if pk == ProceduralBlockKind.AlwaysComb:
        return adapter_stmt(sm, m.body)
    if pk in (ProceduralBlockKind.Always, ProceduralBlockKind.AlwaysFF):
        body = m.body
        if type(body).__name__ != "TimedStatement":
            return ["ProceduralBlockSymbol:NoEventControl"]
        timing = body.timing
        if type(timing).__name__ != "SignalEventControl":
            return ["TimedStatement:" + type(timing).__name__]
        if timing.edge != EdgeKind.PosEdge:
            return ["SignalEventControl:" + str(timing.edge).split(".")[-1]]
        if timing.iffCondition is not None:
            return ["SignalEventControl:iff"]
        clk = extract.convert_expr(sm, timing.expr)
        if clk.get("kind") != "Ident" or clk.get("width") != 1:
            return ["SignalEventControl:clock"]
        return adapter_stmt(sm, body.stmt)
    return ["ProceduralBlockSymbol:" + str(pk).split(".")[-1]]


def adapter_design_blockers(sm, comp):
    """Pass 2: residual blockers with the adapter tier treated as
    supported. Mirrors extract.convert_module's member routing."""
    out = []
    for inst in comp.getRoot().topInstances:
        try:
            body = inst.body
            port_names = set()
            for m in body:
                if str(m.kind) == "SymbolKind.Port":
                    port_names.add(m.name)
            for m in body:
                try:
                    k = str(m.kind).split(".")[-1]
                    if k == "Port":
                        out.extend(kinds_in(extract.convert_port(sm, m)))
                    elif k in ("Variable", "Net"):
                        if m.name in port_names:
                            continue
                        d = (extract.convert_var(sm, m) if k == "Variable"
                             else extract.convert_net(sm, m))
                        out.extend(_minus_string(kinds_in(d)))
                    elif k == "ProceduralBlock":
                        out.extend(adapter_proc_blockers(sm, m))
                    elif k == "ContinuousAssign":
                        out.extend(_minus_string(
                            kinds_in(extract.convert_continuous_assign(sm, m))))
                    elif k == "StatementBlock":
                        continue
                    else:
                        out.append(type(m).__name__ + ":" + k)
                except Exception as exc:
                    out.append("ExtractorInternal:" + type(exc).__name__)
        except Exception as exc:
            out.append("ExtractorInternal:" + type(exc).__name__)
    try:
        for unit in comp.getCompilationUnits():
            for m in unit:
                out.append(type(m).__name__)
    except Exception as exc:
        out.append("ExtractorInternal:" + type(exc).__name__)
    return sorted(set(out))


def parse_meta(text):
    meta = {"name": None, "tags": None, "type": None}
    for m in META_RE.finditer(text[:4000]):
        if meta[m.group(1)] is None:
            meta[m.group(1)] = m.group(2)
    return meta


def classify(relpath):
    """Classify one corpus file. Returns the per-file record dict."""
    rec = {
        "path": relpath,
        "chapter": relpath.split("/")[0],
        "name": None,
        "tags": None,
        "type": None,
        "status": None,
        "kinds": [],
        "adapter_blockers": [],
        "unlockable": False,
        "n_modules": 0,
        "error": None,
    }
    full = os.path.join(_CORPUS, relpath)
    try:
        with open(full, "rb") as f:
            data = f.read()
    except OSError as exc:
        rec["status"] = "error"
        rec["error"] = "OSError: %s" % exc
        return rec
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as exc:
        rec["status"] = "error"
        rec["error"] = "NotUtf8: %s" % exc
        return rec

    rec.update(parse_meta(text))

    if INCLUDE_RE.search(text):
        rec["status"] = "skip_include"
        rec["error"] = "multi-file test (`include directive)"
        return rec

    # The extract.py pipeline, in-process (same calls process_file makes).
    signal.alarm(FILE_TIMEOUT_S)
    try:
        from pyslang.syntax import SyntaxTree
        from pyslang.ast import Compilation
        extract._SOURCE_BYTES = data
        tree = SyntaxTree.fromText(text, name=relpath)
        comp = Compilation()
        comp.addSyntaxTree(tree)
        sm = tree.sourceManager
        design = extract.convert_design(sm, comp)
        rec["n_modules"] = sum(
            1 for m in design["modules"] if m.get("kind") == "Module")
        rec["kinds"] = sorted(set(kinds_in(design)))
        rec["status"] = "clean" if not rec["kinds"] else "partial"
        rec["adapter_blockers"] = adapter_design_blockers(sm, comp)
    except FileTimeout as exc:
        rec["status"] = "error"
        rec["error"] = "Timeout: %s" % exc
        return rec
    except Exception as exc:
        rec["status"] = "error"
        rec["error"] = "%s: %s" % (type(exc).__name__, str(exc)[:200])
        return rec
    finally:
        signal.alarm(0)

    rec["unlockable"] = (
        rec["status"] == "partial"
        and not rec["adapter_blockers"]
        and rec["n_modules"] >= 1
    )
    return rec


# ---------------------------------------------------------------------------
# Orchestration
# ---------------------------------------------------------------------------

def find_files(corpus):
    paths = []
    for entry in sorted(os.listdir(corpus)):
        if not entry.startswith("chapter-"):
            continue
        d = os.path.join(corpus, entry)
        if not os.path.isdir(d):
            continue
        for fn in sorted(os.listdir(d)):
            if fn.endswith(".sv"):
                paths.append(entry + "/" + fn)
    return paths


def run_pool(paths, corpus, jobs):
    results = []
    with Pool(jobs, initializer=_init_worker, initargs=(corpus,),
              maxtasksperchild=500) as pool:
        n = len(paths)
        for i, rec in enumerate(
                pool.imap_unordered(classify, paths, chunksize=32)):
            results.append(rec)
            if (i + 1) % 2000 == 0:
                print("  ... %d/%d" % (i + 1, n), flush=True)
    results.sort(key=lambda r: r["path"])
    return results


def chapter_num(ch):
    try:
        return int(ch.split("-")[1])
    except (IndexError, ValueError):
        return 999


def summarize(records):
    by_status = Counter(r["status"] for r in records)
    clean_by_type = Counter(
        (r["type"] or "(none)") for r in records if r["status"] == "clean")
    total_by_type = Counter((r["type"] or "(none)") for r in records)
    blockers = Counter()
    for r in records:
        if r["status"] == "partial":
            for k in r["kinds"]:
                blockers[k] += 1
    per_chapter = {}
    for r in records:
        ch = per_chapter.setdefault(
            r["chapter"], {"total": 0, "clean": 0, "partial": 0,
                           "error": 0, "skip_include": 0, "unlockable": 0})
        ch["total"] += 1
        ch[r["status"]] += 1
        if r["unlockable"]:
            ch["unlockable"] += 1
    deep = {}
    for chap in DEEP_DIVE_CHAPTERS:
        sim = [r for r in records
               if r["chapter"] == chap and r["type"] == "simulation"]
        part = [r for r in sim if r["status"] == "partial"]
        unlock = [r for r in part if r["unlockable"]]
        residual = Counter()
        for r in part:
            if not r["unlockable"]:
                for k in r["adapter_blockers"]:
                    residual[k] += 1
        deep[chap] = {
            "simulation_tests": len(sim),
            "clean": sum(1 for r in sim if r["status"] == "clean"),
            "partial": len(part),
            "unlockable": len(unlock),
            "blocked_by_more": len(part) - len(unlock),
            "top_residual_blockers": residual.most_common(20),
        }
    internal = [r["path"] for r in records
                if any(k.startswith("ExtractorInternal:")
                       for k in r["kinds"])]
    return {
        "by_status": dict(by_status),
        "clean_by_type": {t: [clean_by_type[t], total_by_type[t]]
                          for t in sorted(total_by_type)},
        "blocker_files": blockers.most_common(),
        "per_chapter": {ch: per_chapter[ch] for ch in
                        sorted(per_chapter, key=chapter_num)},
        "deep_dive": deep,
        "unlockable_total": sum(1 for r in records if r["unlockable"]),
        "unlockable_simulation": sum(
            1 for r in records
            if r["unlockable"] and r["type"] == "simulation"),
        "extractor_internal_files": internal[:50],
    }


def key_of(rec):
    return (rec["status"], tuple(rec["kinds"]),
            tuple(rec["adapter_blockers"]), rec["unlockable"])


def do_recheck(corpus, jobs):
    with open(CENSUS_JSON, "r", encoding="utf-8") as f:
        stored = json.load(f)
    records = {r["path"]: r for r in stored["records"]}
    paths = sorted(records)
    rng = random.Random(SEED)
    sample = rng.sample(paths, min(SAMPLE_SIZE, len(paths)))
    print("recheck: re-running %d files (seed %d)" % (len(sample), SEED))
    fresh = run_pool(sample, corpus, jobs)
    bad = 0
    for rec in fresh:
        old = records[rec["path"]]
        if key_of(rec) != key_of(old):
            bad += 1
            print("MISMATCH %s\n  stored: %r\n  fresh:  %r"
                  % (rec["path"], key_of(old), key_of(rec)))
    if bad:
        print("recheck FAILED: %d/%d mismatches" % (bad, len(sample)))
        return 1
    print("recheck OK: %d/%d identical classifications" %
          (len(sample), len(sample)))
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(prog="census.py", description=__doc__)
    ap.add_argument("--corpus", default=DEFAULT_CORPUS)
    ap.add_argument("--jobs", type=int, default=32)
    ap.add_argument("--limit", type=int, default=0,
                    help="only the first N files (smoke runs; no outputs "
                         "written unless --write)")
    ap.add_argument("--write", action="store_true",
                    help="write outputs even with --limit")
    ap.add_argument("--recheck", action="store_true")
    args = ap.parse_args(argv)

    if args.recheck:
        return do_recheck(args.corpus, args.jobs)

    t0 = time.time()
    paths = find_files(args.corpus)
    if args.limit:
        paths = paths[:args.limit]
    print("census: %d files, %d jobs" % (len(paths), args.jobs), flush=True)
    records = run_pool(paths, args.corpus, args.jobs)
    summary = summarize(records)
    elapsed = time.time() - t0
    summary["elapsed_seconds"] = round(elapsed, 1)
    summary["corpus"] = args.corpus
    summary["seed"] = SEED

    print(json.dumps({k: v for k, v in summary.items()
                      if k in ("by_status", "unlockable_total",
                               "unlockable_simulation", "elapsed_seconds")},
                     indent=2))
    print("top blockers:")
    for k, n in summary["blocker_files"][:15]:
        print("  %6d  %s" % (n, k))
    for chap, d in summary["deep_dive"].items():
        print("%s: sim=%d clean=%d partial=%d unlockable=%d more=%d"
              % (chap, d["simulation_tests"], d["clean"], d["partial"],
                 d["unlockable"], d["blocked_by_more"]))

    if args.limit and not args.write:
        print("(smoke run: outputs not written)")
        return 0

    os.makedirs(OUT_DIR, exist_ok=True)
    with open(CENSUS_JSON, "w", encoding="utf-8", newline="\n") as f:
        json.dump({"schema": "sv-census-1", "summary": summary,
                   "records": records}, f, indent=1)
        f.write("\n")
    unlock = sorted(
        r["path"] for r in records
        if r["unlockable"] and r["type"] == "simulation"
        and r["chapter"] in DEEP_DIVE_CHAPTERS)
    with open(UNLOCKABLE_TXT, "w", encoding="utf-8", newline="\n") as f:
        for p in unlock:
            f.write(p + "\n")
    print("wrote %s (%d records) and %s (%d files)"
          % (CENSUS_JSON, len(records), UNLOCKABLE_TXT, len(unlock)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
