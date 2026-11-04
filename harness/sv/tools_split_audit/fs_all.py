import json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get("AUDIT_DIR") or os.path.join(HERE, "out"); WT = os.environ["WT"]
out = {}
for cid in sorted(os.listdir(os.path.join(DATA, "cases"))):
    case = json.load(open(os.path.join(DATA, "cases", cid, "case.json")))
    files = sorted(os.path.join(DATA, "cases", cid, f) for f in os.listdir(os.path.join(DATA, "cases", cid)) if f.endswith(".sv"))
    pts = [a for k, v in (case.get("params") or {}).items() for a in ("--point", f"{k}={v}")]
    p = subprocess.run(["python3.12", f"{WT}/svgolf/score/fourstate.py", *files, "--top", case["top"], *pts], capture_output=True, text=True, timeout=120, cwd=f"{WT}/svgolf")
    try:
        d = json.loads(p.stdout)
        out[cid] = {"passed": d.get("passed"), "findings": [f[:140] for f in d.get("findings", [])][:3], "diag": [x[:90] for x in d.get("diagnostics", [])][:2], "source": d.get("source")}
    except Exception:
        out[cid] = {"passed": None, "raw": (p.stdout + p.stderr)[-300:]}
    o = out[cid]
    print(f"{cid:22} passed={o.get('passed')} {('REJ:' + '; '.join(o.get('findings', []) + o.get('diag', [])))[:200] if o.get('passed') is False else ''}")
json.dump(out, open(os.path.join(DATA, "fs_all.json"), "w"), indent=1)
