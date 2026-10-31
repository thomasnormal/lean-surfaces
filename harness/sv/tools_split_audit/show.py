#!/usr/bin/env python3
import json, sys, os, re, collections
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get("AUDIT_DIR") or os.path.join(HERE, "out")
def compact(cycles, only=None):
    d = collections.OrderedDict()
    for l in cycles:
        for kv in l.split()[2:]:
            k, v = kv.split("=")
            d.setdefault(k, []).append(v)
    return d
def trace(tool, r, outs):
    if "cycles" not in r: return ""
    d = compact(r["cycles"])
    return "; ".join(f"{k}={' '.join(v)}" for k, v in d.items() if (not outs or k in outs))
def show(cid, full=False):
    r = json.load(open(os.path.join(DATA, "results", cid + ".json")))
    case = json.load(open(os.path.join(DATA, "cases", cid, "case.json")))
    outs = [s for s in case["signals"]]
    print("=" * 100); print(cid, "|", r.get("claim") or "", "| row:", r.get("row"), "| ls-sv:", r.get("ls_sv_refusal"))
    s = r["slang"]
    print("  slang    :", "ERROR " + " || ".join(e[:230] for e in s["errors"][:3]) if s["errors"] else "no error" + (" (warnings: " + " || ".join(w[:150] for w in s["warnings"][:3]) + ")" if s["warnings"] else ""))
    for t in ["icarus", "verilator", "yosys"]:
        x = r.get(t, {})
        line = x.get("status", "?")
        if "msg" in x and x["msg"]:
            m = " / ".join(p for p in x["msg"].replace("\n", " / ").split(" / ") if not p.startswith("- ") and "$finish" not in p).strip()
            if m: line += " | " + m[:300]
        if x.get("diags"): line += " | diags " + ",".join(x["diags"])
        if x.get("warnings"): line += " | warn " + " ; ".join(x["warnings"])[:300]
        tr = trace(t, x, outs)
        if tr: line += "\n               " + tr[:700 if not full else 5000]
        print(f"  {t:9}: {line}")
def xc(cid):
    p = os.path.join(DATA, "results", cid + ".xcelium.json")
    if not os.path.exists(p): print("  xcelium  : (not run)"); return
    x = json.load(open(p))
    case = json.load(open(os.path.join(DATA, "cases", cid, "case.json")))
    tr = trace("x", x, case["signals"])
    st = "ok" if x["cycles"] and x["rc"] == 0 else ("TIMEOUT(300s)" if x["rc"] == 124 else "rc=%d" % x["rc"])
    d = " ; ".join(re.sub(r"^xm\w+: ", "", y) for y in x["diag"][:3])
    print(f"  xcelium  : {st}" + (" | " + d[:420] if d else "") + ("\n               " + tr[:700] if tr else ""))
for c in sys.argv[1:]:
    show(c)
    xc(c)
