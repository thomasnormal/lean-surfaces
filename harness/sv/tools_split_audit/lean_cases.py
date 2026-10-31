#!/usr/bin/env python3
"""lean_cases.py : write $AUDIT_DIR/lean_cases.json (the cases2.json-shaped file runner2.lean reads) for the audit cases."""
import json, os
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get("AUDIT_DIR") or os.path.join(HERE, "out")
cases = []
for cid in sorted(os.listdir(os.path.join(DATA, "cases"))):
    c = json.load(open(os.path.join(DATA, "cases", cid, "case.json")))
    e = {"name": cid, "example": "audit/" + cid, "top": c["top"], "signals": c["signals"], "stimulus": c["stimulus"]}
    if "clock" in c: e["clock"] = c["clock"]
    if c.get("params"): e["params"] = c["params"]
    cases.append(e)
json.dump({"fuel": 2000, "cases": cases}, open(os.path.join(DATA, "lean_cases.json"), "w"), indent=1)
print(len(cases), "cases")
