#!/usr/bin/env python3
"""lean_parse.py OUT.txt : turn the stdout of lean_batch.sh into $AUDIT_DIR/lean_all.json (the `run2` column of report.py):
`runs` when runner2 printed its CYCLE lines, else the first ERROR line (a loud refusal or timeout)."""
import json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get("AUDIT_DIR") or os.path.join(HERE, "out")
text = open(sys.argv[1]).read()
out = {}
for m in re.finditer(r"@@@CASE (\S+)\n(.*?)@@@RC (\S+)", text, re.S):
    cid, body, rc = m.group(1), m.group(2), m.group(3)
    if rc == "noenvelope":
        out[cid] = "no envelope"
    elif rc == "0" and "CYCLE " in body:
        out[cid] = "runs"
    else:
        err = [l for l in body.splitlines() if l.startswith("ERROR")]
        out[cid] = ("REFUSES: " + re.sub(r"\s+", " ", err[0])[6:100]) if err else f"rc={rc}"
json.dump(out, open(os.path.join(DATA, "lean_all.json"), "w"), indent=1)
print(len(out), "cases")
