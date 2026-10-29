#!/usr/bin/env python3
"""Three-way audit of the ls-sv differential corpus: model vs pinned Xcelium vs Icarus.

Xcelium is the REFERENCE simulator for ls-sv (Thomas, 2026-10-29), but it is not
available everywhere, so this script never runs it: it reads the PINNED traces in
`harness/sv/xcelium_golden.json` (docs/sv-xcelium-reference.md). For every
SIMULATED row of `harness/sv/cases2.json` (the loud-refusal rows run no simulator)
it lines up three traces

  * the MODEL  (the Lean runner, one trace per accepted schedule), read from the
    `prep/` directory that `xcelium_batch.py prepare` wrote (or computed on the
    spot for a missing row, through the optional `--lean-wrapper`);
  * XCELIUM    (the golden file; a row whose content hash no longer matches its
    DUT/testbench is reported STALE and gets no verdict);
  * ICARUS     (run locally, `iverilog -g2012` + `vvp`, exactly the way
    `diff_test2.run_iverilog` does; results are cached in `<workdir>/icarus.json`),

and reports, SEPARATELY and never merged, three notions of "equal":

  exact      the trace lines are identical (to the row's first accepted schedule);
  schedule   identical to the trace of SOME accepted schedule (`accept_sigmas`),
             but not to the first: equality "up to the harness's own accepted
             schedules";
  xk0        identical except in cycle 0, and there only where one side has an
             x/z and the other a known bit (the LRM's time-zero race window);

plus one diagnostic layer that is NOT an equivalence, `xk`: every differing bit
is x/z on exactly one side (any cycle) -- one of the two simulators is more
pessimistic -- split by direction.

Each row gets ONE class, from the model-vs-Xcelium verdict and the Icarus trace:

  model==X  +icarus-agrees | +icarus-differs (declared / undeclared) | +no-icarus
  model!=X  icarus==model (Xcelium departs from both) | icarus==X (the model
            departs from both simulators) | three-way split | no-icarus
  X-not-run (Xcelium could not take the row) | stale

and every `oracle_disagreement` / `icarus_unavailable` declaration gets a verdict
against the golden trace (the Xcelium-as-reference rule):

  oracle_disagreement (Icarus departs from the model)
     CONFIRMED                    Xcelium == model  (Icarus is the outlier)
     CONTRADICTED:X==icarus       Xcelium sides with Icarus
     CONTRADICTED:neither         Xcelium equals neither the model nor Icarus
     (plus a check that the declaration's recorded sim/lean traces still equal
     the fresh Icarus trace and the model trace)
  icarus_unavailable (Icarus cannot simulate the row)
     CONFIRMED (xcelium simulates it, == model) | model!=X | X-not-run

Rows that differ are grouped into CLUSTERS: every differing (cycle, signal) cell is routed by
`SIGNAL_CAUSES` (DUT file, signal) to one cause, and declared rows are clustered by what Xcelium
says about their declaration. A cell no entry claims is reported as UNCLUSTERED, so a new cause
cannot hide; a row with several causes is a member of several clusters.

Usage:
  python3 harness/sv/xcelium_compare.py --workdir W [--lean-wrapper CMD]
        [--json OUT.json] [--markdown OUT.md] [--case NAME ...]
        [--recheck-model N [--seed S]] [--jobs 4]

`W` is the work directory of `xcelium_batch.py prepare` (model traces + testbenches).
With a complete `W/prep/` the script needs no Lean and no Xcelium, only `iverilog`.
`--recheck-model N` re-runs the model on N random rows (needs `lake`; use the Lean
slot wrapper) and checks the stored model traces still reproduce.
Exit code 0 always, unless the inputs are unusable (2): this is a report, not a gate.
"""

import argparse
import collections
import concurrent.futures
import json
import os
import random
import re
import sys
import tempfile
import shutil

HARNESS_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HARNESS_DIR)
import diff_test2  # noqa: E402
import xcelium_batch as B  # noqa: E402
import xcelium_golden as G  # noqa: E402
from oracle_disagreements import HarnessError, SimulatorError, canonical_tool_output  # noqa: E402

REPO = diff_test2.REPO

# --------------------------------------------------------------------------
# Causes and clusters. A DIFFERING row is attributed cell by cell: every differing
# (cycle, signal) is routed by (DUT file name, signal name) to ONE cause, the
# construct that produces it. The routing table was written by reading the DUTs
# (docs/sv-xcelium-audit.md section 4); a differing cell no entry claims is
# reported as UNCLUSTERED, so a new cause cannot hide. A row with several causes
# belongs to several clusters (the audit says so; its unique-row count is separate).
#
# Declared rows are clustered by what Xcelium says about the declaration.
# --------------------------------------------------------------------------
CAUSES = collections.OrderedDict([
    ("P1", ("model_ne_xcelium", "partly out-of-range part-select READ with a constant base",
            "Xcelium returns all x for the whole select; the model (and Icarus) return the in-range bits "
            "and x only for the out-of-range ones")),
    ("P2", ("model_ne_xcelium", "partly out-of-range part-select READ with a run-time base",
            "the same all-x result for a signal-valued base (no BNDWRN warning is raised)")),
    ("P3", ("model_ne_xcelium", "partly out-of-range part-select WRITE (procedural)",
            "Xcelium drops the whole write; the model writes the in-range bits")),
    ("H1", ("model_ne_xcelium", "narrower plain-signal actual into a wider input port",
            "the model zero-extends (as Icarus); in Xcelium the formal's high bits stay unknown (CUVMPW)")),
    ("T1", ("declared_departure_contradicted", "run-time bit-select index wider than 32 bits",
            "Xcelium reads the low 32 bits of the index (BIGWBS), like Icarus; the model gives x")),
])
# (file regex, signal regex, cause); first match wins.
SIGNAL_CAUSES = [
    (r"partsel",             r"ov_hi|ov_lo|ov_rng",            "P1"),
    (r"partsel",             r"dyn_up|dyn_dn",                 "P2"),
    (r"partsel",             r"w_hi|w_lo",                     "P3"),
    (r"array_oob",           r"over",                          "P1"),
    (r"array_oob",           r"m_flat",                        "P3"),
    (r"array_oob_part",      r"d_hi|r_lo|r_hi",                "P1"),
    (r"array_oob_part",      r"w_flat",                        "P3"),
    (r"array_oob_lsbwrite",  r"w_flat|v",                      "P3"),
    (r"const_wrap",          r"o_u|o_sub|o_rng",               "P1"),
    (r"param_types",         r"o_b5|o_sb",                     "P1"),
    (r"label_kminus",        r"p|q",                           "P1"),
    (r"label_n0",            r"o2",                            "P1"),
    (r"label_param",         r"o2",                            "P1"),
    (r"bits_labels",         r"o1",                            "P1"),
    (r"array_param_labels",  r"w",                             "P1"),
    (r"dyn32",               r"minus2|minus2_dn|m32|o32|d32",  "P2"),
    (r"hier_width",          r"in_narrow",                     "H1"),
    (r"fold_pcase",          r"o3",                            "T1"),
]
# Declared-row clusters. `DECL_CONFIRMED` routes a CONFIRMED oracle_disagreement by its
# declaration id; the contradicted ones are routed in `row_clusters`.
CLUSTERS_DECL = collections.OrderedDict([
    ("D1", ("icarus_ne_xcelium_model_agrees_xcelium", "Icarus reads untouched bits of a partly driven variable as z",
            "model and Xcelium keep the variable's initial x (declared, CONFIRMED)")),
    ("D2", ("icarus_ne_xcelium_model_agrees_xcelium", "Icarus linearizes an out-of-range INNER packed-array index",
            "model and Xcelium check each dimension on its own (declared, CONFIRMED)")),
    ("D3", ("icarus_ne_xcelium_model_agrees_xcelium", "Icarus pads a nested unbased-unsized fill in a port actual",
            "model and Xcelium take the port width as the context (declared, CONFIRMED)")),
    ("D4", ("icarus_ne_xcelium_model_agrees_xcelium", "Icarus always_comb misses a re-trigger through a copy/port/bit-split",
            "model and Xcelium settle (declared, CONFIRMED; an LRM-permitted tool split)")),
    ("DX1", ("declared_departure_contradicted", "declared Icarus departure; Xcelium equals neither Icarus nor the model",
             "the model-vs-Xcelium difference is cause P1 / P3, not the declared construct; Xcelium does not "
             "reproduce Icarus's lowering")),
    ("DX2", ("declared_departure_contradicted", "declared Icarus departure; Xcelium equals Icarus, but only through P1",
             "the Xcelium trace is the model's with the partly out-of-range select forced to all-x; the row "
             "does not separate Icarus's -: lowering from P1")),
    ("U1", ("other", "rows Icarus 12 cannot simulate, simulated by Xcelium",
            "all of them equal the model: previously unverified rows are now Xcelium-verified")),
])
DECL_CONFIRMED = [
    (r"iverilog-(partial-variable|noncanonical-variable|packed-member-.*|packed-union-.*|nested-member-.*|"
     r"typedef-nested-concat|fixed-array-noncanonical-slice|concat-target-undriven)-?.*init", "D1"),
    (r"iverilog-packed-inner-index-linearized", "D2"),
    (r"iverilog-port-fill-self-determined", "D3"),
    (r"iverilog-comb-.*-sensitivity", "D4"),
]


def parse_cycle(line):
    parts = line.split(" ")
    if len(parts) < 2 or parts[0] != "CYCLE":
        return None, collections.OrderedDict()
    sigs = collections.OrderedDict()
    for p in parts[2:]:
        k, _, v = p.partition("=")
        sigs[k] = v
    return int(parts[1]), sigs


def char_kind(a, b):
    """Kind of one differing bit position; `a` is the first operand's bit."""
    ua, ub = a in "xz", b in "xz"
    if ua and not ub:
        return "A_unknown"      # the first operand has x/z, the second a known bit
    if ub and not ua:
        return "B_unknown"
    if ua and ub:
        return "xz"
    return "value"


def diff_detail(a_lines, b_lines):
    """Structured difference of two traces (`a` first, `b` second). Returns None
    when identical, else a dict:
      cycles   sorted list of differing cycle indices ('missing' cycles included)
      length   (len a, len b) when the cycle counts differ
      signals  ordered list of differing signal names
      kinds    set of bit kinds {A_unknown, B_unknown, xz, value, width, name}
      first    (cycle, signal, a value, b value) of the first differing signal
      all      list of (cycle, signal, a value, b value) for every differing signal
    """
    if a_lines == b_lines:
        return None
    cycles, signals, kinds, allv = [], [], set(), []
    n = max(len(a_lines), len(b_lines))
    for i in range(n):
        al = a_lines[i] if i < len(a_lines) else None
        bl = b_lines[i] if i < len(b_lines) else None
        if al == bl:
            continue
        cycles.append(i)
        if al is None or bl is None:
            kinds.add("missing")
            allv.append((i, "<cycle>", al, bl))
            continue
        _, sa = parse_cycle(al)
        _, sb = parse_cycle(bl)
        for name in list(sa) + [k for k in sb if k not in sa]:
            va, vb = sa.get(name), sb.get(name)
            if va == vb:
                continue
            if va is None or vb is None:
                kinds.add("name")
            elif len(va) != len(vb):
                kinds.add("width")
            else:
                for ca, cb in zip(va, vb):
                    if ca != cb:
                        kinds.add(char_kind(ca, cb))
            if name not in signals:
                signals.append(name)
            allv.append((i, name, va, vb))
    return dict(cycles=cycles, length=(len(a_lines), len(b_lines)) if len(a_lines) != len(b_lines) else None,
                signals=signals, kinds=kinds, first=allv[0] if allv else None, all=allv)


def only_unknown_kinds(d, allowed):
    return d is not None and d["kinds"] <= allowed and d["length"] is None


def xk0_equal(d):
    """Equal up to x-vs-known at cycle 0 only."""
    return (d is not None and d["cycles"] == [0] and d["length"] is None
            and d["kinds"] and d["kinds"] <= {"A_unknown", "B_unknown"})


def xk_direction(d):
    """For a difference in which every differing bit is x/z on exactly one side:
    'A-only' (the first operand is the pessimistic one), 'B-only' or 'both'.
    None when some differing bit is a value difference (or x vs z, width, ...)."""
    if d is None or d["length"] is not None or not d["kinds"]:
        return None
    k = d["kinds"]
    if k == {"A_unknown"}:
        return "A-only"
    if k == {"B_unknown"}:
        return "B-only"
    if k == {"A_unknown", "B_unknown"}:
        return "both"
    return None


# ------------------------------------------------------------------ icarus --

def run_icarus(dut_abs, tb_text, workdir):
    """('ok', cycles, None) | ('compile-fail' / 'run-fail', None, summary)."""
    try:
        lines = diff_test2.run_iverilog(dut_abs, tb_text, workdir)
        return "ok", lines, None
    except SimulatorError as exc:
        text = canonical_tool_output((exc.stdout or "") + "\n" + (exc.stderr or ""))
        text = text.replace(dut_abs, "<dut>").replace(workdir, "<work>")
        keep = [ln.strip() for ln in text.splitlines() if ln.strip()]
        return ("compile-fail" if exc.stage == "compile" else "run-fail"), None, \
            "rc=%s %s" % (exc.returncode, (keep[0] if keep else "(no output)")[:200])
    except Exception as exc:  # timeouts and the like
        return "run-fail", None, "%s: %s" % (type(exc).__name__, str(exc)[:200])


def icarus_for(rows, prep, workdir, jobs, cases_by_name):
    cache_path = os.path.join(workdir, "icarus.json")
    cache = {}
    if os.path.exists(cache_path):
        with open(cache_path) as f:
            cache = json.load(f)
    todo = [n for n in rows if prep[n]["hash"] not in cache]
    tmp_root = tempfile.mkdtemp(prefix="xcmp_icarus_")

    def work(n):
        rec = prep[n]
        wd = os.path.join(tmp_root, n)
        return n, run_icarus(os.path.join(REPO, rec["dut"]), rec["tb"], wd)

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        for n, (st, lines, why) in ex.map(work, todo):
            cache[prep[n]["hash"]] = dict(status=st, cycles=lines, why=why)
    shutil.rmtree(tmp_root, ignore_errors=True)
    if todo:
        tmp = cache_path + ".tmp"
        with open(tmp, "w") as f:
            json.dump(cache, f, sort_keys=True)
        os.replace(tmp, cache_path)
    return {n: cache[prep[n]["hash"]] for n in rows}


# ------------------------------------------------------------ classification --

def trace_eq(models, accept, trace):
    """(`exact`, `schedule`): equal to the first accepted schedule's trace /
    equal to a LATER accepted schedule's trace (only when not exact)."""
    if trace is None:
        return None, None
    if models[accept[0]] == trace:
        return True, None
    for sg in accept[1:]:
        if models[sg] == trace:
            return False, sg
    return False, None


def classify(rec):
    """Fill rec['verdict'] and rec['class']. `rec` has model/xcelium/icarus/case."""
    case = rec["case"]
    accept = rec["accept"]
    models = rec["model"]
    X = rec["xcelium"]
    I = rec["icarus"]
    m0 = models[accept[0]]
    v = {}
    if X["status"] != "ok" or X["stale"]:
        v["mx"] = "stale" if X["stale"] else "x-not-run"
    else:
        xt = X["cycles"]
        ex, sg = trace_eq(models, accept, xt)
        v["mx_exact"] = ex
        v["mx_schedule"] = sg
        d = diff_detail(xt, m0)       # A = Xcelium, B = model
        v["mx_detail"] = d
        if ex:
            v["mx"] = "equal"
            v["mx_layer"] = "exact"
        elif sg:
            v["mx"] = "equal"
            v["mx_layer"] = "schedule"
        elif xk0_equal(diff_detail(xt, m0)):
            v["mx"] = "differ"
            v["mx_layer"] = "xk0"
        else:
            v["mx"] = "differ"
            v["mx_layer"] = None
        if v["mx"] == "differ":
            v["xk_dir"] = xk_direction(d)       # A = Xcelium, B = model
            v["xk0"] = xk0_equal(d)
    # Icarus relations
    if I["status"] == "ok":
        it = I["cycles"]
        ie, isg = trace_eq(models, accept, it)
        v["mi"] = "equal" if (ie or isg) else "differ"
        if X["status"] == "ok" and not X["stale"]:
            v["xi"] = "equal" if X["cycles"] == it else "differ"
    else:
        v["mi"] = "no-icarus"
        v["xi"] = "no-icarus"
    # class
    if v["mx"] in ("stale", "x-not-run"):
        cls = v["mx"]
    elif v["mx"] == "equal":
        if v["mi"] == "no-icarus":
            cls = "model==X, no Icarus trace"
        elif v["mi"] == "equal":
            cls = "model==X, Icarus agrees"
        else:
            cls = "model==X, Icarus differs (declared)" if "oracle_disagreement" in case \
                else "model==X, Icarus differs (UNDECLARED)"
    else:
        if v["mi"] == "no-icarus":
            cls = "model!=X, no Icarus trace"
        elif v["mi"] == "equal":
            cls = "model!=X, Icarus==model (Xcelium departs from both)"
        elif v["xi"] == "equal":
            cls = "model!=X, Icarus==X (model departs from both)"
        else:
            cls = "model!=X, three-way split"
    rec["verdict"] = v
    rec["class"] = cls
    # declarations
    rec["declaration"] = declaration_verdict(rec)


def declaration_verdict(rec):
    case = rec["case"]
    v = rec["verdict"]
    X = rec["xcelium"]
    I = rec["icarus"]
    models = rec["model"]
    accept = rec["accept"]
    out = None
    if "oracle_disagreement" in case:
        od = case["oracle_disagreement"]
        notes = []
        sg = od.get("sigma", accept[0])
        if I["status"] != "ok":
            notes.append("Icarus did not run (%s)" % I["status"])
        elif I["cycles"] != od.get("sim_trace"):
            notes.append("recorded sim_trace no longer equals the fresh Icarus trace")
        if models.get(sg) != od.get("lean_trace"):
            notes.append("recorded lean_trace no longer equals the model trace")
        if X["status"] != "ok" or X["stale"]:
            verdict = "UNKNOWN:%s" % ("stale" if X["stale"] else "x-not-run")
        else:
            xt = X["cycles"]
            if xt == od.get("lean_trace"):
                verdict = "CONFIRMED"
            elif xt == od.get("sim_trace"):
                verdict = "CONTRADICTED:X==icarus"
            else:
                verdict = "CONTRADICTED:neither"
        claims_xcelium = "Xcelium" in (od.get("observed", "") + od.get("reference", ""))
        out = dict(kind="oracle_disagreement", id=od["id"], verdict=verdict, notes=notes,
                   text_claims_xcelium=claims_xcelium, sigma=sg)
    elif "icarus_unavailable" in case:
        iu = case["icarus_unavailable"]
        if X["status"] != "ok" or X["stale"]:
            verdict = "UNKNOWN:%s" % ("stale" if X["stale"] else "x-not-run")
        elif v["mx"] == "equal":
            verdict = "CONFIRMED"
        else:
            verdict = "model!=X"
        out = dict(kind="icarus_unavailable", id=iu["id"], verdict=verdict, notes=[],
                   text_claims_xcelium=False)
    return out


# ------------------------------------------------------------------- driver --

def load_inputs(args):
    with open(diff_test2.CASES_JSON) as f:
        cases = [c for c in json.load(f)["cases"] if "refusal" not in c]
    golden = G.load(args.golden)
    if golden is None:
        raise SystemExit("no golden file at %s" % (args.golden or G.GOLDEN_JSON))
    if args.case:
        cases = [c for c in cases if c["name"] in args.case]
    return cases, golden


def build(args):
    cases, golden = load_inputs(args)
    B.install_lean_wrapper(args.lean_wrapper)
    os.makedirs(args.workdir, exist_ok=True)
    prep = {}
    for c in cases:
        pf = B.prep_file(args.workdir, c["name"])
        rec = None
        if os.path.exists(pf):
            with open(pf) as f:
                rec = json.load(f)
        dut = B.dut_path(c)
        sig = B.inputs_sig(c, dut, dut + ".json")
        if rec is None or rec.get("inputs_sig") != sig or "error" in rec:
            if not args.lean_wrapper and not args.allow_lean:
                raise SystemExit("row %s: no fresh model trace in %s/prep (run `xcelium_batch.py prepare` "
                                 "or pass --lean-wrapper / --allow-lean)" % (c["name"], args.workdir))
            rec, st = B.prepare_row(c, args.workdir, True, True)
            if "error" in rec:
                raise SystemExit("row %s: model failed: %s" % (c["name"], rec["error"][:300]))
        prep[c["name"]] = rec
    names = [c["name"] for c in cases]
    ic = icarus_for(names, prep, args.workdir, args.jobs, {c["name"]: c for c in cases})
    rows = collections.OrderedDict()
    for c in cases:
        n = c["name"]
        p = prep[n]
        e = golden["rows"].get(n)
        accept = c.get("accept_sigmas", ["src"])
        if e is None:
            X = dict(status="none", cycles=None, stale=False, warnings=[], message="not pinned")
        else:
            stale = e.get("hash") != p["hash"]
            X = dict(status=e.get("status"), cycles=e.get("cycles"), stale=stale,
                     warnings=e.get("warnings", []), message=e.get("message"))
        rec = dict(name=n, case=c, accept=accept, model=p["model"], xcelium=X, icarus=ic[n],
                   tb=p["tb"], dut=p["dut"], ports=p.get("ports", []))
        classify(rec)
        rows[n] = rec
    return rows, golden


def recheck_model(args, rows):
    """Re-run the model on a random sample and compare with the stored traces."""
    B.install_lean_wrapper(args.lean_wrapper)
    rnd = random.Random(args.seed)
    names = sorted(rows)
    sample = rnd.sample(names, min(args.recheck_model, len(names)))
    for must in args.recheck_must:
        if must in rows and must not in sample:
            sample.append(must)
    res = {}
    for n in sample:
        c = rows[n]["case"]
        dut = B.dut_path(c)
        out = {}
        for sg in rows[n]["accept"]:
            _, lines = diff_test2.run_lean(dut + ".json", n, sg)
            out[sg] = lines
        res[n] = "REPRODUCED" if out == rows[n]["model"] else "CHANGED"
        print("recheck-model %-28s %s" % (n, res[n]), flush=True)
    return res


# ------------------------------------------------------------------ reporting --

def file_base(case):
    return case.get("file", case["top"])


def cell_cause(case, signal):
    fb = file_base(case)
    for frx, srx, cause in SIGNAL_CAUSES:
        if re.fullmatch(frx, fb) and re.fullmatch(srx, signal):
            return cause
    return None


def row_cells(rec):
    """The differing cells (cycle, signal, xcelium, model, cause) of a model!=X row."""
    d = rec["verdict"].get("mx_detail")
    if not d:
        return []
    return [(c, s, xv, mv, cell_cause(rec["case"], s)) for c, s, xv, mv in d["all"]]


def allx(v):
    return v is not None and v != "" and set(v) == {"x"}


def row_clusters(rec):
    """Cluster ids of a row, in order of first appearance; [] for a clean row."""
    out = []

    def add(c):
        if c not in out:
            out.append(c)

    v = rec["verdict"]
    if v["mx"] == "differ":
        for _c, _s, _x, _m, cause in row_cells(rec):
            add(cause or "UNCLUSTERED")
    decl = rec["declaration"]
    if decl and decl["kind"] == "oracle_disagreement":
        if decl["verdict"] == "CONFIRMED":
            for rx, cid in DECL_CONFIRMED:
                if re.fullmatch(rx, decl["id"]):
                    add(cid)
                    break
            else:
                add("UNCLUSTERED")
        elif decl["verdict"] == "CONTRADICTED:neither":
            add("DX1")
        elif decl["verdict"] == "CONTRADICTED:X==icarus":
            if all(allx(xv) for _c, _s, xv, _m, _k in row_cells(rec)):
                add("DX2")
    if (v["mx"] == "equal" and v["mi"] == "no-icarus"):
        add("U1")
    return out


def lookup_cell(rec, trace, cyc, sig):
    if trace is None or cyc >= len(trace):
        return None
    return parse_cycle(trace[cyc])[1].get(sig)


def first_cell_for(rec, cid):
    """(cycle, signal, stimulus, model, xcelium, icarus) of the first cell of `rec`
    that belongs to cluster `cid`, or None."""
    case = rec["case"]
    m0 = rec["model"][rec["accept"][0]]
    X = rec["xcelium"]["cycles"]
    I = rec["icarus"]["cycles"] if rec["icarus"]["status"] == "ok" else None
    cell = None
    if cid in CAUSES or cid in ("DX1", "DX2"):
        for c, s, xv, mv, cause in row_cells(rec):
            if cid in ("DX1", "DX2") or cause == cid:
                cell = (c, s)
                break
    elif cid in ("D1", "D2", "D3", "D4"):
        d = diff_detail(I, m0) if I is not None else None
        if d:
            cell = (d["all"][0][0], d["all"][0][1])
    elif cid == "U1":
        outs = [p[0] for p in rec.get("ports", []) if p[1] == "out"]
        cell = (0, outs[0] if outs else case["signals"][-1])
    if cell is None:
        return None
    c, s = cell
    stim = case["stimulus"][c] if c < len(case["stimulus"]) else {}
    ins = ", ".join("%s=%s" % (k, b) for k, b in stim.items())
    return dict(row=rec["name"], cycle=c, signal=s, stimulus=ins,
                model=lookup_cell(rec, m0, c, s), xcelium=lookup_cell(rec, X, c, s),
                icarus=lookup_cell(rec, I, c, s) if I is not None else "(%s: %s)" % (rec["icarus"]["status"], rec["icarus"]["why"]))


def build_clusters(rows):
    """{cid: dict(kind, title, summary, rows, first, cells, allx_cells)}"""
    meta = collections.OrderedDict()
    for cid, (kind, title, summary) in CAUSES.items():
        meta[cid] = (kind, title, summary)
    for cid, (kind, title, summary) in CLUSTERS_DECL.items():
        meta[cid] = (kind, title, summary)
    meta["UNCLUSTERED"] = ("other", "differing cells no routing entry claims", "NEW CAUSE: extend SIGNAL_CAUSES")
    out = collections.OrderedDict((cid, dict(kind=m[0], title=m[1], summary=m[2], rows=[], first=None,
                                             cells=0, allx_cells=0, classes=collections.Counter(),
                                             warnings=collections.Counter())) for cid, m in meta.items())
    for rec in rows.values():
        cl = row_clusters(rec)
        for cid in cl:
            o = out[cid]
            o["rows"].append(rec["name"])
            o["classes"][rec["class"]] += 1
            for w in rec["xcelium"]["warnings"]:
                o["warnings"][w.split(":")[-1]] += 1
            if o["first"] is None:
                o["first"] = first_cell_for(rec, cid)
        for c, s, xv, mv, cause in row_cells(rec):
            o = out[cause or "UNCLUSTERED"]
            o["cells"] += 1
            o["allx_cells"] += 1 if allx(xv) else 0
    return out


def evidence(rows):
    """Cell-level checks that back the cause descriptions (printed, never gating).
    P1/P2: the pinned Xcelium value of every attributed cell is all-x.
    P3:    the distinct pinned Xcelium values of each written signal over the WHOLE
           trace (a dropped write leaves the baseline value in every cycle).
    H1:    the differing bits form a leading prefix and are x in Xcelium.
    T1:    the pinned Xcelium value equals the Icarus value in every cell."""
    out = collections.OrderedDict()
    tally = collections.defaultdict(lambda: [0, 0])
    p3 = collections.OrderedDict()
    h1 = []
    t1 = [0, 0]
    for rec in rows.values():
        if rec["verdict"]["mx"] != "differ":
            continue
        X = rec["xcelium"]["cycles"]
        I = rec["icarus"]["cycles"] if rec["icarus"]["status"] == "ok" else None
        for c, s, xv, mv, cause in row_cells(rec):
            if cause in ("P1", "P2"):
                tally[cause][0] += 1
                tally[cause][1] += 1 if allx(xv) else 0
            elif cause == "P3":
                p3.setdefault((rec["name"], s), None)
            elif cause == "H1":
                diffpos = [i for i, (a, b) in enumerate(zip(xv, mv)) if a != b]
                ok = bool(diffpos) and diffpos == list(range(len(diffpos))) and all(xv[i] == "x" for i in diffpos)
                h1.append(ok)
            elif cause == "T1":
                t1[0] += 1
                t1[1] += 1 if (I is not None and lookup_cell(rec, I, c, s) == xv) else 0
    for (name, sig) in p3:
        vals = sorted({parse_cycle(l)[1].get(sig) for l in rows[name]["xcelium"]["cycles"]})
        p3[(name, sig)] = vals
    out["P1/P2 cells with an all-x Xcelium value (cells, all-x)"] = {k: tuple(v) for k, v in sorted(tally.items())}
    out["P3 distinct Xcelium values of each overhung target over the whole trace"] = \
        {"%s.%s" % k: (v if len(v) <= 8 else v[:8] + ["..."]) for k, v in p3.items()}
    out["H1 cells whose differing bits are a leading x prefix (cells, ok)"] = (len(h1), sum(h1))
    out["T1 cells where Xcelium equals Icarus (cells, equal)"] = tuple(t1)
    return out


def summarize(rows, golden):
    S = collections.OrderedDict()
    S["xcelium_version"] = (golden.get("simulator") or {}).get("version")
    S["rows"] = len(rows)
    cnt = collections.Counter(r["class"] for r in rows.values())
    S["classes"] = dict(cnt)
    layer = collections.Counter(r["verdict"].get("mx_layer") for r in rows.values()
                                if r["verdict"]["mx"] == "equal")
    S["equal_layers"] = dict(layer)
    S["differ"] = sum(1 for r in rows.values() if r["verdict"]["mx"] == "differ")
    xk = collections.Counter(r["verdict"].get("xk_dir") for r in rows.values()
                             if r["verdict"]["mx"] == "differ")
    S["differ_xk_direction"] = {str(k): v for k, v in xk.items()}
    S["differ_xk0"] = sum(1 for r in rows.values() if r["verdict"].get("xk0"))
    S["differ_unknown_only"] = sum(
        1 for r in rows.values() if r["verdict"]["mx"] == "differ"
        and r["verdict"]["mx_detail"]["length"] is None
        and r["verdict"]["mx_detail"]["kinds"] <= {"A_unknown", "B_unknown", "xz"})
    S["differ_persisting"] = sum(1 for r in rows.values() if r["verdict"]["mx"] == "differ"
                                 and len(r["verdict"]["mx_detail"]["cycles"]) >= 2)
    S["differ_cycle0_only"] = sum(1 for r in rows.values() if r["verdict"]["mx"] == "differ"
                                  and r["verdict"]["mx_detail"]["cycles"] == [0])
    S["differ_first_cycle"] = dict(collections.Counter(
        r["verdict"]["mx_detail"]["cycles"][0] for r in rows.values() if r["verdict"]["mx"] == "differ"))
    S["icarus_status"] = dict(collections.Counter(r["icarus"]["status"] for r in rows.values()))
    S["xcelium_status"] = dict(collections.Counter(r["xcelium"]["status"] for r in rows.values()))
    S["xcelium_stale"] = sum(1 for r in rows.values() if r["xcelium"]["stale"])
    S["declarations"] = {"%s %s" % k: v for k, v in collections.Counter(
        (r["declaration"]["kind"], r["declaration"]["verdict"]) for r in rows.values()
        if r["declaration"]).items()}
    S["warnings"] = dict(collections.Counter(w for r in rows.values() for w in r["xcelium"]["warnings"]))
    S["warnings_on_differ"] = dict(collections.Counter(
        w for r in rows.values() if r["verdict"]["mx"] == "differ" for w in r["xcelium"]["warnings"]))
    return S


def md_table(headers, rows):
    out = ["| " + " | ".join(headers) + " |", "|" + "|".join("---" for _ in headers) + "|"]
    for r in rows:
        out.append("| " + " | ".join(str(x).replace("|", "\\|") for x in r) + " |")
    return "\n".join(out)


def fmt_cell(f):
    if not f:
        return "-"
    return "`%s` cyc %d `%s` [%s]: model `%s`, Xcelium `%s`, Icarus `%s`" % (
        f["row"], f["cycle"], f["signal"], f["stimulus"], f["model"], f["xcelium"], f["icarus"])


def report_markdown(rows, golden, S, clusters):
    out = []
    out.append("### Classes\n")
    out.append(md_table(["class", "rows"], sorted(S["classes"].items(), key=lambda kv: -kv[1])))
    out.append("\n### Declarations\n")
    drows = []
    for r in rows.values():
        d = r["declaration"]
        if d and d["kind"] == "oracle_disagreement":
            drows.append([r["name"], d["id"], d["verdict"], "yes" if d["text_claims_xcelium"] else "no",
                          "; ".join(d["notes"]) or "-"])
    out.append(md_table(["row", "declaration", "verdict", "text names Xcelium", "notes"], drows))
    out.append("\n### Clusters\n")
    crow = []
    for cid, o in clusters.items():
        if not o["rows"]:
            continue
        crow.append([cid, o["kind"], len(o["rows"]), o["title"], ", ".join(o["rows"]), fmt_cell(o["first"])])
    out.append(md_table(["cluster", "kind", "rows", "cause", "members", "first difference"], crow))
    out.append("\n### Differing rows\n")
    drow = []
    for r in rows.values():
        if r["verdict"]["mx"] != "differ":
            continue
        d = r["verdict"]["mx_detail"]
        drow.append([r["name"], ",".join(w.split(":")[-1] for w in r["xcelium"]["warnings"]) or "-",
                     ",".join(row_clusters(r)), r["class"], ",".join(map(str, d["cycles"][:12])) +
                     (",..." if len(d["cycles"]) > 12 else ""), ",".join(d["signals"])])
    out.append(md_table(["row", "Xcelium warnings", "clusters", "class", "differing cycles", "differing signals"], drow))
    return "\n".join(out) + "\n"


def text_report(rows, golden, S, clusters):
    print("Xcelium %s; %d simulated rows (stale pins: %d)" % (S["xcelium_version"], S["rows"], S["xcelium_stale"]))
    print("xcelium status:", S["xcelium_status"], " icarus status:", S["icarus_status"])
    print("\nCLASSES")
    for k, v in sorted(S["classes"].items(), key=lambda kv: -kv[1]):
        print("  %4d  %s" % (v, k))
    print("\nEQUIVALENCE LAYERS (model vs Xcelium): equal-layers=%s; differ=%d; differ-only-by-x-vs-known-in-cycle-0 (xk0)=%d; "
          "differ-in-cycle-0-only=%d; differ-in-two-or-more-cycles=%d; first differing cycle histogram=%s; "
          "differ-only-where-a-side-is-x/z (no known-value difference)=%d"
          % (S["equal_layers"], S["differ"], S["differ_xk0"], S["differ_cycle0_only"], S["differ_persisting"],
             S["differ_first_cycle"], S["differ_unknown_only"]))
    print("x-direction of the differing rows (A = Xcelium unknown where the model is known, B = the reverse): %s"
          % S["differ_xk_direction"])
    print("Xcelium warnings (all rows): %s ; (differing rows): %s" % (S["warnings"], S["warnings_on_differ"]))
    print("\nDECLARATIONS")
    for k, v in sorted(S["declarations"].items()):
        print("  %3d  %s" % (v, k))
    for r in rows.values():
        d = r["declaration"]
        if d and d["kind"] == "oracle_disagreement":
            print("    %-34s %-26s %s" % (r["name"], d["verdict"], "; ".join(d["notes"])))
    print("\nCLUSTERS (a row with several causes is in several clusters)")
    for cid, o in clusters.items():
        if o["rows"]:
            print("  %-12s %-44s %3d rows  cells=%d (all-x in Xcelium: %d)" % (cid, o["kind"], len(o["rows"]), o["cells"], o["allx_cells"]))
            print("      %s" % o["title"])
            print("      rows: %s" % ", ".join(o["rows"]))
            print("      classes: %s ; Xcelium warnings on these rows: %s" % (dict(o["classes"]), dict(o["warnings"])))
            print("      first: %s" % fmt_cell(o["first"]))
    print("\nEVIDENCE")
    for k, v in evidence(rows).items():
        print("  %s: %s" % (k, v))
    print("\nDIFFERING ROWS")
    for r in rows.values():
        if r["verdict"]["mx"] != "differ":
            continue
        d = r["verdict"]["mx_detail"]
        print("  %-26s clusters=%-16s warn=%-7s cyc=%s sigs=%s kinds=%s"
              % (r["name"], ",".join(row_clusters(r)),
                 ",".join(w.split(":")[-1] for w in r["xcelium"]["warnings"]) or "-",
                 d["cycles"][:6], d["signals"], sorted(d["kinds"])))


def jsonable(rows, golden, clusters):
    out = {}
    for n, r in rows.items():
        v = dict(r["verdict"])
        d = v.pop("mx_detail", None)
        if d:
            v["diff"] = dict(cycles=d["cycles"], signals=d["signals"], kinds=sorted(d["kinds"]),
                             first=list(d["first"]) if d["first"] else None)
        out[n] = dict(class_=r["class"], verdict=v, declaration=r["declaration"],
                      clusters=row_clusters(r), xcelium_status=r["xcelium"]["status"],
                      xcelium_warnings=r["xcelium"]["warnings"], icarus_status=r["icarus"]["status"],
                      icarus_why=r["icarus"]["why"], accept=r["accept"])
    return dict(rows=out, clusters={k: dict(o, classes=dict(o["classes"]), warnings=dict(o["warnings"]))
                                    for k, o in clusters.items() if o["rows"]})


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--workdir", required=True, help="xcelium_batch.py work dir (prep/, icarus.json)")
    ap.add_argument("--golden", default=None, help="golden file (default: harness/sv/xcelium_golden.json)")
    ap.add_argument("--lean-wrapper", default=None, help="command prefix for every `lake` call")
    ap.add_argument("--allow-lean", action="store_true", help="compute missing/stale model traces (needs lake)")
    ap.add_argument("--case", nargs="*", default=None)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--json", default=None)
    ap.add_argument("--markdown", default=None)
    ap.add_argument("--recheck-model", type=int, default=0, metavar="N")
    ap.add_argument("--recheck-must", nargs="*", default=[])
    ap.add_argument("--seed", type=int, default=20261029)
    args = ap.parse_args()
    try:
        rows, golden = build(args)
    except (HarnessError, OSError) as exc:
        print("xcelium_compare: %s" % exc)
        return 2
    S = summarize(rows, golden)
    clusters = build_clusters(rows)
    text_report(rows, golden, S, clusters)
    if args.json:
        with open(args.json, "w") as f:
            json.dump(dict(summary=S, **jsonable(rows, golden, clusters)), f, indent=1, sort_keys=True)
    if args.markdown:
        with open(args.markdown, "w") as f:
            f.write(report_markdown(rows, golden, S, clusters))
    if args.recheck_model:
        recheck_model(args, rows)
    return 0


if __name__ == "__main__":
    sys.exit(main())
