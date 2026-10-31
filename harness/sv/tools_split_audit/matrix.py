#!/usr/bin/env python3
import json, os, sys, collections, re
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get("AUDIT_DIR") or os.path.join(HERE, "out")
def load(cid):
    r = json.load(open(os.path.join(DATA, "results", cid + ".json")))
    case = json.load(open(os.path.join(DATA, "cases", cid, "case.json")))
    p = os.path.join(DATA, "results", cid + ".xcelium.json")
    x = json.load(open(p)) if os.path.exists(p) else None
    return r, case, x
def outs_of(r, case):
    ins = {p[0] for p in r.get("ports", []) if p[1] == "in"}
    return [s for s in case["signals"] if s not in ins]
def tr(cycles, outs):
    d = collections.OrderedDict()
    for l in cycles:
        for kv in l.split()[2:]:
            k, v = kv.split("=")
            if k in outs: d.setdefault(k, []).append(v)
    return ";".join(f"{k}=" + ",".join(v) for k, v in d.items())
def row(cid):
    r, case, x = load(cid)
    outs = outs_of(r, case)
    cells = {}
    s = r["slang"]
    cells["slang"] = ("REJECT" if s["errors"] else "ok")
    for t in ["icarus", "verilator", "yosys"]:
        e = r.get(t, {})
        st = e.get("status")
        if st in ("compile-error", "error"): cells[t] = "REJECT"
        elif st and st.startswith("ok") and e.get("cycles"): cells[t] = tr(e["cycles"], outs)
        elif st and st.startswith("ok"): cells[t] = "ok(" + (e.get("msg") or "no trace")[:40] + ")"
        else: cells[t] = str(st)
    if x is None: cells["xcelium"] = "-"
    elif x["rc"] == 124: cells["xcelium"] = "HANG"
    elif x["rc"] != 0 or not x["cycles"]: cells["xcelium"] = "REJECT"
    else: cells["xcelium"] = tr(x["cycles"], outs)
    return cells
if __name__ == "__main__":
    for cid in sys.argv[1:]:
        c = row(cid)
        groups = {}
        letters = {}
        out = []
        for t in ["slang", "icarus", "verilator", "yosys", "xcelium"]:
            v = c[t]
            if v in ("ok", "REJECT", "HANG", "-") or v.startswith("ok(") or v in ("timeout", "netlist-sim-timeout"):
                out.append(f"{t}={v}")
            else:
                if v not in letters: letters[v] = chr(ord('A') + len(letters))
                out.append(f"{t}={letters[v]}")
        print(f"{cid:22} " + "  ".join(out))
        for v, l in letters.items(): print(f"{'':24}{l}: {v[:260]}")
