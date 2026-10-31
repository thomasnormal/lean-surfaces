#!/usr/bin/env python3
"""xc.py CASE... : run the cases' tb.sv + dut files on Xcelium (vip-ng, fleet refsim gate), ONE xrun at a time in
one ssh session, remote dir removed at the end. Writes results/<case>.xcelium.json."""
import json, os, subprocess, sys, tarfile, io, re, time
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get("AUDIT_DIR") or os.path.join(HERE, "out")
ids = sys.argv[1:]
buf = io.BytesIO()
with tarfile.open(fileobj=buf, mode="w") as tf:
    for cid in ids:
        wd = os.path.join(DATA, "work", cid)
        for fn in sorted(os.listdir(wd)):
            if fn == "tb.sv" or (fn.endswith(".sv") and fn not in ("tb.sv", "tb_v.sv", "tb_net.sv")):
                tf.add(os.path.join(wd, fn), arcname=f"{cid}/{fn}")
remote = r'''
set -u
REFSIM=${REFSIM:-/var/tmp/thomas-ahle/fleet2/bin/refsim}
D=$(mktemp -d /tmp/wprc-xc.XXXXXX)
trap 'rm -rf "$D"' EXIT
cd "$D"
tar xf -
for c in %s; do
  cd "$D/$c"
  duts=$(ls *.sv | grep -v '^tb.sv$')
  echo "@@@CASE $c"
  timeout 300 $REFSIM -sv -q -timescale 1ns/1ns -xmlibdirname "$D/$c/xcelium.d" $duts tb.sv > out.txt 2>&1
  echo "@@@RC $?"
  head -c 6000 out.txt
  echo "@@@END"
  rm -rf "$D/$c/xcelium.d" "$D/$c/xrun.history" "$D/$c/xrun.log" 2>/dev/null
  cd "$D"
done
''' % " ".join(ids)
t0 = time.time()
# one ssh session: the script reads the tar from a base64 here-document, runs the cases one at a time, cleans up
import base64
b64 = base64.b64encode(buf.getvalue()).decode()
script = "set -u\nREFSIM=${REFSIM:-/var/tmp/thomas-ahle/fleet2/bin/refsim}\nD=$(mktemp -d /tmp/wprc-xc.XXXXXX)\ntrap 'rm -rf \"$D\"' EXIT\ncd \"$D\"\nbase64 -d <<'B64EOF' | tar xf -\n" + b64 + "\nB64EOF\n" + remote.split("cd \"$D\"\ntar xf -\n", 1)[1]
p = subprocess.run(["ssh", "-o", "BatchMode=yes", "vip-ng", "bash -s"], input=script.encode(), capture_output=True, timeout=3300)
out = p.stdout.decode(errors="replace")
sys.stderr.write(f"ssh rc={p.returncode} {time.time()-t0:.0f}s stderr={p.stderr.decode(errors='replace')[:300]}\n")
for m in re.finditer(r"@@@CASE (\S+)\n@@@RC (\d+)\n(.*?)@@@END", out, re.S):
    cid, rc, log = m.group(1), int(m.group(2)), m.group(3)
    cycles = [l.strip() for l in log.splitlines() if l.startswith("CYCLE ")]
    diag = [re.sub(r"\s+", " ", l.strip())[:200] for l in log.splitlines() if re.match(r"\s*(xmvlog|xmelab|xmsim|xrun|ncvlog)?[:\s]*\*[EWF],", l) or "*E," in l or "*F," in l or "*W," in l]
    res = {"rc": rc, "cycles": cycles, "diag": diag[:12], "log_tail": "" if cycles and not diag else log[-1200:]}
    json.dump(res, open(os.path.join(DATA, "results", cid + ".xcelium.json"), "w"), indent=1)
    print(cid, "rc", rc, "cycles", len(cycles), "diag", len(diag))
