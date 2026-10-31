import json, os, subprocess, sys, re
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get("AUDIT_DIR") or os.path.join(HERE, "out"); WT = os.environ["WT"]
def walk(x, acc):
    if isinstance(x, dict):
        if x.get("kind") == "Unsupported": acc.append(x.get("sv_kind"))
        for v in x.values(): walk(v, acc)
    elif isinstance(x, list):
        for v in x: walk(v, acc)
out = {}
for cid in sorted(os.listdir(os.path.join(DATA, "cases"))):
    case = json.load(open(os.path.join(DATA, "cases", cid, "case.json")))
    files = sorted(os.path.join(DATA, "cases", cid, f) for f in os.listdir(os.path.join(DATA, "cases", cid)) if f.endswith(".sv"))
    o = os.path.join(DATA, "ext", cid + ".json")
    if os.path.exists(o): os.remove(o)
    p = subprocess.run(["python3.12", f"{WT}/extractors/sv/extract.py", "--top", case["top"], "-o", o, *files], capture_output=True, text=True, timeout=120)
    if os.path.exists(o):
        acc = []; walk(json.load(open(o)), acc)
        out[cid] = {"rc": p.returncode, "unsupported": sorted(set(a for a in acc if a)), "n": len(acc), "stderr": p.stderr.strip()[-300:]}
    else:
        out[cid] = {"rc": p.returncode, "unsupported": None, "stderr": (p.stderr + p.stdout).strip()[-300:]}
    print(cid, out[cid]["rc"], out[cid]["unsupported"], (out[cid]["stderr"][:120].replace("\n", " ") if out[cid]["rc"] else ""), flush=True)
json.dump(out, open(os.path.join(DATA, "ext_all.json"), "w"), indent=1)
