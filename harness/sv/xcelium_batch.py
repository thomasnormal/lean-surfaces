#!/usr/bin/env python3
"""Capture the Xcelium reference traces of the ls-sv differential corpus as
PINNED DATA (`harness/sv/xcelium_golden.json`).

Xcelium is the reference simulator for ls-sv, but it is not available
everywhere and nothing may require it: this tool is the ONE place that talks
to it. Its output is a data file that `diff_test2.py --golden` compares the
model against on any machine. Procedure and etiquette: docs/sv-xcelium-reference.md.

For every SIMULATED row of `cases2.json` (rows with a `refusal` run no
simulator and are skipped) the tool regenerates EXACTLY the testbench and DUT
file `diff_test2.py` would run -- it imports and calls `diff_test2.run_lean`
(which also yields the model trace) and `gen_tb2.generate_tb2`, no logic is
forked -- hashes (row name, DUT source text, testbench text, parameter
overrides, xrun flags), ships the work to vip-ng in batches, runs each case
through the fleet gate (`/var/tmp/thomas-ahle/fleet2/bin/refsim`) ONE AT A
TIME with its own `-xmlibdirname`, and collects the `CYCLE` lines.

  prepare   Lean side (needs `lake`): per row, `run_lean` for the port list +
            the model trace, the testbench, the hash. Writes
            <workdir>/prep/<row>.json. Resumable. Run it under the machine's
            Lean slot (--lean-wrapper), it is the slow phase (~9 s per row).
  run       Xcelium side (needs ssh to vip-ng, no Lean): the pending rows (no
            golden entry, hash changed, or a retryable status) in batches of
            --batch-size per ssh session. Each batch is staged under
            /tmp/ta-xref/<label>/<batch id>/ on vip-ng, started DETACHED, and
            polled, so a dropped connection loses nothing: re-running the same
            command re-attaches (or re-fetches finished results). The golden
            file is rewritten atomically after every batch (resumable).
            --follow keeps going while a concurrent `prepare` is still
            producing rows.
  verify    Re-run a sample of pinned rows (default 10) and check the traces
            reproduce; does not touch the golden file.
  status    Counts: prepared rows, pinned rows by status, stale / unpinned.

Usage (refresh everything; see the doc for the exact commands):
  python3 harness/sv/xcelium_batch.py prepare --workdir W [--lean-wrapper CMD]
  python3 harness/sv/xcelium_batch.py run     --workdir W [--follow]
  python3 harness/sv/xcelium_batch.py verify  --workdir W --sample 10
"""

import argparse
import hashlib
import io
import json
import os
import random
import re
import shlex
import subprocess
import sys
import tarfile
import time

HARNESS_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HARNESS_DIR)
import diff_test2  # noqa: E402
import gen_tb2  # noqa: E402
import xcelium_golden as G  # noqa: E402
from oracle_disagreements import HarnessError  # noqa: E402

REPO = diff_test2.REPO
HOST = "vip-ng"
REFSIM = "/var/tmp/thomas-ahle/fleet2/bin/refsim"
REMOTE_ROOT = "/tmp/ta-xref"
SSH = ["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=20",
       "-o", "ServerAliveInterval=15", "-o", "ServerAliveCountMax=4"]
NAME_OK = re.compile(r"^[A-Za-z0-9_.-]+$")
LABEL_OK = re.compile(r"^[A-Za-z0-9_.-]+$")
# Statuses `run` re-attempts without --retry-failed (transient by nature).
RETRYABLE = ("timeout",)

DIAG = re.compile(r"^(xmvlog|xmvhdl|xmelab|xmsim|xrun|xmsdfc)[^:\n]*: \*([EFW]),(\w+)")


def log(msg):
    print("[%s] %s" % (time.strftime("%H:%M:%S"), msg), flush=True)


# ----------------------------------------------------------------- prepare --

def simulated_rows(cases):
    return [c for c in cases if "refusal" not in c]


def dut_path(case):
    return os.path.join(REPO, "Examples", "system-verilog", case["example"],
                        case.get("file", case["top"]) + ".sv")


def inputs_sig(case, dut, envelope):
    h = hashlib.sha256()
    for blob in (open(dut, "rb").read(), open(envelope, "rb").read(),
                 json.dumps(case, sort_keys=True).encode()):
        h.update(hashlib.sha256(blob).digest())
    return h.hexdigest()


def install_lean_wrapper(wrapper):
    """Route every `lake` call of `diff_test2.run_lean` through `wrapper` (a
    shell word list, e.g. the machine's Lean slot script). The slot wait counts
    towards the call's timeout, so it is lifted."""
    if not wrapper:
        return
    original = diff_test2.run_cmd
    prefix = shlex.split(wrapper)

    def wrapped(cmd, cwd, timeout):
        if cmd and cmd[0] == "lake":
            return original(prefix + cmd, cwd, timeout * 8)
        return original(cmd, cwd, timeout)
    diff_test2.run_cmd = wrapped


def prep_file(workdir, name):
    return os.path.join(workdir, "prep", name + ".json")


def load_prep(workdir):
    out = {}
    d = os.path.join(workdir, "prep")
    if os.path.isdir(d):
        for fn in sorted(os.listdir(d)):
            if fn.endswith(".json"):
                with open(os.path.join(d, fn)) as f:
                    out[fn[:-5]] = json.load(f)
    return out


def prepare_row(case, workdir, force, retry_errors):
    name = case["name"]
    if not NAME_OK.match(name):
        raise HarnessError("row name %r is not a safe file name" % name)
    dut = dut_path(case)
    envelope = dut + ".json"
    sig = inputs_sig(case, dut, envelope)
    pf = prep_file(workdir, name)
    if os.path.exists(pf) and not force:
        with open(pf) as f:
            old = json.load(f)
        if old.get("inputs_sig") == sig and ("error" not in old or not retry_errors):
            return old, "cached"
    rec = {"name": name, "inputs_sig": sig,
           "dut": os.path.relpath(dut, REPO), "params": case.get("params") or {}}
    try:
        sigmas = case.get("accept_sigmas", ["src"])
        model = {}
        ports = None
        for sg in sigmas:
            ports, lines = diff_test2.run_lean(envelope, name, sg)
            model[sg] = lines
        tb = gen_tb2.generate_tb2(case["top"], ports, case)
        rec.update(ports=[list(p) for p in ports], tb=tb, model=model,
                   hash=G.row_hash(name, G.read_text(dut), tb, case.get("params")))
        status = "prepared"
    except (HarnessError, gen_tb2.TbError, OSError, subprocess.TimeoutExpired) as exc:
        rec["error"] = str(exc)[-2500:]
        status = "ERROR"
    os.makedirs(os.path.dirname(pf), exist_ok=True)
    tmp = pf + ".tmp"
    with open(tmp, "w") as f:
        json.dump(rec, f, indent=1, sort_keys=True)
    os.replace(tmp, pf)
    return rec, status


def cmd_prepare(args):
    install_lean_wrapper(args.lean_wrapper)
    with open(diff_test2.CASES_JSON) as f:
        cases = simulated_rows(json.load(f)["cases"])
    if args.case:
        cases = [c for c in cases if c["name"] in args.case]
    os.makedirs(args.workdir, exist_ok=True)
    done_marker = os.path.join(args.workdir, "prepare.done")
    if os.path.exists(done_marker):
        os.remove(done_marker)
    t0 = time.time()
    counts = {}
    for i, case in enumerate(cases):
        rec, status = prepare_row(case, args.workdir, args.force, args.retry_errors)
        counts[status] = counts.get(status, 0) + 1
        if status != "cached" or i % 50 == 0:
            log("prepare %3d/%d %-28s %s%s" % (i + 1, len(cases), case["name"], status,
                                              (": " + rec["error"].splitlines()[0][:160]) if "error" in rec else ""))
    open(done_marker, "w").write("done\n")
    log("prepare finished in %.0fs: %s" % (time.time() - t0, counts))
    return 0


# ------------------------------------------------------------------- ssh ----

def ssh(host, remote_cmd, stdin=None, timeout=300, retries=8):
    """One ssh round trip; retried with backoff while the CONNECTION fails
    (exit 255 / timeout). Returns (rc, stdout bytes, stderr bytes)."""
    delay = 5
    for attempt in range(retries):
        try:
            feed = {"input": stdin} if stdin is not None else {"stdin": subprocess.DEVNULL}
            p = subprocess.run(SSH + [host, remote_cmd], stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, timeout=timeout, **feed)
            if p.returncode != 255:
                return p.returncode, p.stdout, p.stderr
            why = "ssh exit 255: " + p.stderr.decode("utf-8", "replace").strip()[-200:]
        except subprocess.TimeoutExpired:
            why = "ssh timed out after %ss" % timeout
        log("  %s (attempt %d/%d); retrying in %ds" % (why, attempt + 1, retries, delay))
        time.sleep(delay)
        delay = min(delay * 2, 120)
    raise RuntimeError("%s unreachable after %d attempts (%s)" % (host, retries, why))


def remote_version(host):
    rc, out, err = ssh(host, "%s -version" % REFSIM, timeout=300)
    text = out.decode("utf-8", "replace").strip()
    if rc != 0 or not text:
        raise RuntimeError("`refsim -version` failed (%d): %s %s"
                           % (rc, text, err.decode("utf-8", "replace")))
    line = [ln for ln in text.splitlines() if ln.strip()][-1]
    return line, " ".join(line.split()[1:]) if line.startswith("TOOL:") else line


# ------------------------------------------------------------- one batch ----

def build_batch(items):
    """`items`: list of (name, dut_abs_path, tb_text). Returns (tar bytes,
    order list of (id, name))."""
    buf = io.BytesIO()
    order = []
    with tarfile.open(fileobj=buf, mode="w") as tar:
        def add(path, data, mode=0o644):
            info = tarfile.TarInfo(path)
            info.size = len(data)
            info.mode = mode
            info.mtime = 0
            tar.addfile(info, io.BytesIO(data))
        lines = []
        for i, (name, dut, tb) in enumerate(items):
            cid = "c%03d" % i
            fn = os.path.basename(dut)
            with open(dut, "rb") as f:
                add("%s/%s" % (cid, fn), f.read())
            add("%s/tb.sv" % cid, tb.encode("utf-8", "surrogateescape"))
            lines.append("%s %s %s" % (cid, fn, name))
            order.append((cid, name))
        add("order.txt", ("\n".join(lines) + "\n").encode())
        add("run.sh", DRIVER.encode(), 0o755)
    return buf.getvalue(), order


DRIVER = r'''#!/bin/bash
# Generated by harness/sv/xcelium_batch.py. Runs this batch's cases ONE AT A TIME
# through the fleet gate; resumable (a finished case has res/<id>.rc).
cd "$(dirname "$(readlink -f "$0")")" || exit 1
exec 9> lock
flock -n 9 || { echo "another driver of this batch holds the lock" >> driver.log; exit 0; }
echo $$ > pid
REFSIM=/var/tmp/thomas-ahle/fleet2/bin/refsim
mkdir -p res
while read -r id dut name; do
  [ -f "res/$id.rc" ] && continue
  (
    cd "$id" || exit 97
    t0=$(date +%s%N)
    "$REFSIM" -sv -q -timescale 1ns/1ns -xmlibdirname "$PWD/xcelium.d" "$dut" tb.sv \
        > "../res/$id.out" 2> "../res/$id.err" < /dev/null
    rc=$?
    t1=$(date +%s%N)
    echo "$rc $(( (t1 - t0) / 1000000 ))" > "../res/$id.rc.tmp"
    mv "../res/$id.rc.tmp" "../res/$id.rc"
    rm -rf xcelium.d
  )
  echo "$id" >> progress
done < order.txt
touch DONE
'''


def classify(rc, out, err, workdir_remote):
    """(status, cycles, message, warnings) of one xrun run."""
    text = out + ("\n" + err if err.strip() else "")
    text = text.replace(workdir_remote, "<work>")
    cycles = G_cycle_lines(out)
    diags = []
    warns = []
    for ln in text.splitlines():
        m = DIAG.match(ln)
        if m:
            (warns if m.group(2) == "W" else diags).append(ln.rstrip())
    warn_codes = []
    for ln in warns:
        m = DIAG.match(ln)
        code = "%s:%s" % (m.group(1), m.group(3))
        if code not in warn_codes:
            warn_codes.append(code)
    started = "xcelium> run" in text or bool(cycles)
    finished = "Simulation complete via $finish" in text
    if rc in (124, 137, 143):
        return "timeout", cycles, "refsim wall cap hit (exit %d)" % rc, warn_codes
    if rc != 0 and not started:
        msg = "\n".join(diags[:6]) or "xrun exit %d before simulation: %s" % (rc, text.strip()[-300:])
        return "xrun-compile-error", cycles, msg, warn_codes
    if rc != 0:
        msg = "\n".join(diags[:6]) or "xrun exit %d during simulation" % rc
        return "runtime-error", cycles, msg, warn_codes
    if not finished:
        return ("runtime-error", cycles,
                "xrun exited 0 without reaching $finish" + ("; " + "; ".join(diags[:3]) if diags else ""),
                warn_codes)
    return "ok", cycles, None, warn_codes


def G_cycle_lines(text):
    return diff_test2.cycle_lines(text)


def execute_batch(host, label, items, poll, workdir):
    """Run one batch on the host. `items`: list of (name, dut_abs_path,
    tb_text). Returns {name: {status, cycles, message, warnings, rc, ms}}.
    Idempotent per batch id: re-running attaches to / re-fetches an earlier
    start of the same batch."""
    tar_bytes, order = build_batch(items)
    bid = "b" + hashlib.sha256(tar_bytes).hexdigest()[:12]
    if not LABEL_OK.match(label):
        raise RuntimeError("unsafe label %r" % label)
    rdir = "%s/%s/%s" % (REMOTE_ROOT, label, bid)
    state = ssh(host, "cd %s 2>/dev/null || { echo none; exit 0; }; "
                "if [ -f DONE ]; then echo done; "
                "elif [ -f pid ] && kill -0 $(cat pid) 2>/dev/null; then echo running; "
                "else echo stopped; fi" % rdir)[1].decode().strip()
    if state in ("none", "stopped"):
        # (re)stage: extract over any partial dir, then start detached.
        rc, _, err = ssh(host, "mkdir -p %s && cd %s && tar xf - && "
                         "(nohup setsid bash run.sh > driver.log 2>&1 < /dev/null &) ; sleep 1; echo started"
                         % (rdir, rdir), stdin=tar_bytes, timeout=600)
        if rc != 0:
            raise RuntimeError("could not stage/start batch %s: %s" % (bid, err.decode("utf-8", "replace")))
        log("  batch %s: %d cases staged and started on %s:%s" % (bid, len(items), host, rdir))
    else:
        log("  batch %s: already %s on the host; attaching" % (bid, state))
    t_start = time.time()
    last = -1
    dead_before = False
    while True:
        rc, out, _ = ssh(host, "cd %s && { if [ -f DONE ]; then echo DONE; else echo RUN; fi; "
                         "cat progress 2>/dev/null | wc -l; "
                         "if [ ! -f DONE ] && ! { [ -f pid ] && kill -0 $(cat pid) 2>/dev/null; }; "
                         "then echo DEAD; fi; }" % rdir)
        words = out.decode().split()
        done_flag = words[0] == "DONE"
        n = int(words[1]) if len(words) > 1 and words[1].isdigit() else 0
        if n != last:
            log("  batch %s: %d/%d cases finished (%.0fs)" % (bid, n, len(items), time.time() - t_start))
            last = n
        if done_flag:
            break
        dead = "DEAD" in words and not done_flag
        if dead and dead_before:
            # The driver died without finishing (e.g. the host rebooted): restart it; it skips
            # finished cases, and its flock keeps two drivers from ever overlapping.
            log("  batch %s: driver not running; restarting (finished cases are kept)" % bid)
            ssh(host, "cd %s && (nohup setsid bash run.sh > driver.log 2>&1 < /dev/null &) ; sleep 1" % rdir)
            dead = False
        dead_before = dead
        time.sleep(poll)
    rc, data, err = ssh(host, "cd %s && tar cf - res" % rdir, timeout=600)
    if rc != 0:
        raise RuntimeError("could not fetch results of %s: %s" % (bid, err.decode("utf-8", "replace")))
    files = {}
    with tarfile.open(fileobj=io.BytesIO(data)) as tar:
        for m in tar.getmembers():
            if m.isfile():
                files[os.path.basename(m.name)] = tar.extractfile(m).read().decode("utf-8", "replace")
    results = {}
    for cid, name in order:
        rcline = files.get(cid + ".rc")
        if rcline is None:
            results[name] = dict(status="runtime-error", cycles=[], warnings=[], rc=None, ms=None,
                                 message="no result file fetched for this case (driver incomplete)")
            continue
        rcode, ms = [int(x) for x in rcline.split()]
        status, cycles, message, warns = classify(rcode, files.get(cid + ".out", ""),
                                                 files.get(cid + ".err", ""), rdir)
        results[name] = dict(status=status, cycles=cycles, message=message, warnings=warns,
                             rc=rcode, ms=ms)
    # Results are in hand: keep the raw tool output locally, then clean OUR remote dir.
    rawdir = os.path.join(workdir, "raw")
    os.makedirs(rawdir, exist_ok=True)
    for cid, name in order:
        for ext in ("out", "err"):
            with open(os.path.join(rawdir, "%s.%s" % (name, ext)), "w") as f:
                f.write(files.get("%s.%s" % (cid, ext), ""))
    ssh(host, "case %s in %s/%s/b*) rm -rf %s ;; esac" % (rdir, REMOTE_ROOT, label, rdir))
    return results


# --------------------------------------------------------------- golden -----

def current_hash(rec):
    """The hash of a prepared row against the DUT file as it is NOW."""
    dut = os.path.join(REPO, rec["dut"])
    return G.row_hash(rec["name"], G.read_text(dut), rec["tb"], rec["params"])


def entry_of(rec_hash, res):
    e = {"hash": rec_hash, "status": res["status"], "cycles": res["cycles"]}
    if res.get("message"):
        e["message"] = res["message"]
    if res.get("warnings"):
        e["warnings"] = res["warnings"]
    return e


def pending_rows(golden, prep, retry_failed, only=None):
    out = []
    for name in sorted(prep):
        if only and name not in only:
            continue
        rec = prep[name]
        if "error" in rec:
            continue
        h = current_hash(rec)
        e = golden["rows"].get(name)
        if e is None or e.get("hash") != h:
            out.append(name)
        elif e["status"] in RETRYABLE or (retry_failed and e["status"] != G.STATUS_OK):
            out.append(name)
    return out


def record_prep_errors(golden, prep):
    changed = False
    for name, rec in prep.items():
        if "error" in rec:
            e = {"hash": None, "status": "no-testbench", "cycles": [], "message": rec["error"][-600:]}
            if golden["rows"].get(name) != e:
                golden["rows"][name] = e
                changed = True
    return changed


def ensure_version(golden, args):
    raw, short = remote_version(args.host)
    sim = golden.get("simulator") or {}
    if golden["rows"] and sim.get("version") and sim["version"] != short:
        if not args.rebase:
            raise SystemExit("the golden file was captured with Xcelium %s but %s has %s: "
                             "pass --rebase to re-run EVERY row with the new version (a pin "
                             "must not mix versions)" % (sim["version"], args.host, short))
        log("version change %s -> %s: rebasing (every row is re-run)" % (sim["version"], short))
        golden["rows"] = {}
    golden["simulator"] = {
        "name": "Xcelium",
        "version": short,
        "version_raw": raw,
        "host": "%s via %s" % (args.host, REFSIM),
        "invocation": "refsim " + " ".join(G.XRUN_FLAGS) + " -xmlibdirname <case>/xcelium.d <dut>.sv tb.sv",
        "protocol": "one xrun per row, one at a time; stdout CYCLE lines pinned",
    }
    return short


def cmd_run(args):
    golden = G.load(args.golden) or G.empty_golden()
    short = ensure_version(golden, args)
    t0 = time.time()
    done_marker = os.path.join(args.workdir, "prepare.done")
    n_run = 0
    stats = {}
    if not os.path.isdir(os.path.join(args.workdir, "prep")) and not args.follow:
        raise SystemExit("no %s/prep: run `xcelium_batch.py prepare --workdir %s` first"
                         % (args.workdir, args.workdir))
    while True:
        prep = load_prep(args.workdir)
        if record_prep_errors(golden, prep):
            G.save(golden, args.golden)
        pending = pending_rows(golden, prep, args.retry_failed, set(args.case) if args.case else None)
        if args.limit is not None:
            pending = pending[:max(0, args.limit - n_run)]
        preparing = args.follow and not os.path.exists(done_marker)
        if not pending:
            if preparing:
                time.sleep(30)
                continue
            break
        if len(pending) < args.batch_size and preparing:
            time.sleep(30)
            continue
        batch = pending[:args.batch_size]
        items = [(n, os.path.join(REPO, prep[n]["dut"]), prep[n]["tb"]) for n in batch]
        log("batch of %d (%d pending): %s ... %s" % (len(batch), len(pending), batch[0], batch[-1]))
        results = execute_batch(args.host, args.label, items, args.poll, args.workdir)
        for n in batch:
            res = results[n]
            golden["rows"][n] = entry_of(current_hash(prep[n]), res)
            stats[res["status"]] = stats.get(res["status"], 0) + 1
            with open(os.path.join(args.workdir, "run-log.jsonl"), "a") as f:
                f.write(json.dumps({"row": n, "status": res["status"], "rc": res["rc"],
                                    "ms": res["ms"], "xcelium": short}) + "\n")
        G.save(golden, args.golden)
        n_run += len(batch)
        log("golden saved (%d rows pinned); this run: %s" % (len(golden["rows"]), stats))
        if args.limit is not None and n_run >= args.limit:
            break
    log("run finished: %d rows run in %.0fs; %s" % (n_run, time.time() - t0, stats))
    return 0


def cmd_verify(args):
    golden = G.load(args.golden)
    if golden is None:
        raise SystemExit("no golden file at %s" % (args.golden or G.GOLDEN_JSON))
    prep = load_prep(args.workdir)
    ok_rows = sorted(n for n, e in golden["rows"].items()
                     if e["status"] == G.STATUS_OK and n in prep and "error" not in prep[n]
                     and e["hash"] == current_hash(prep[n]))
    rng = random.Random(args.seed)
    sample = sorted(rng.sample(ok_rows, min(args.sample, len(ok_rows))))
    if args.case:
        sample = [n for n in args.case if n in ok_rows]
    raw, short = remote_version(args.host)
    pinned = (golden.get("simulator") or {}).get("version")
    log("verify %d rows %s (Xcelium %s now, %s pinned)" % (len(sample), sample, short, pinned))
    items = [(n, os.path.join(REPO, prep[n]["dut"]), prep[n]["tb"]) for n in sample]
    t0 = time.time()
    results = execute_batch(args.host, args.label, items, args.poll, args.workdir)
    bad = 0
    for n in sample:
        same = results[n]["status"] == "ok" and results[n]["cycles"] == golden["rows"][n]["cycles"]
        print("%-28s %s  (%d cycles)" % (n, "REPRODUCED" if same else "DIFFERENT",
                                         len(golden["rows"][n]["cycles"])))
        bad += not same
    log("verify: %d/%d reproduced identically in %.0fs" % (len(sample) - bad, len(sample), time.time() - t0))
    return 1 if bad else 0


def cmd_status(args):
    golden = G.load(args.golden)
    prep = load_prep(args.workdir) if args.workdir and os.path.isdir(os.path.join(args.workdir, "prep")) else {}
    with open(diff_test2.CASES_JSON) as f:
        sim = simulated_rows(json.load(f)["cases"])
    print("simulated rows in cases2.json: %d" % len(sim))
    print("prepared (workdir): %d, with errors: %d" % (len(prep), sum("error" in r for r in prep.values())))
    if golden is None:
        print("no golden file")
        return 0
    print("pinned: %d rows, simulator %s" % (len(golden["rows"]), golden["simulator"].get("version")))
    by = {}
    for e in golden["rows"].values():
        by[e["status"]] = by.get(e["status"], 0) + 1
    for k in sorted(by):
        print("  %-20s %d" % (k, by[k]))
    names = {c["name"] for c in sim}
    print("simulated rows not pinned: %d" % len(names - set(golden["rows"])))
    print("pinned rows no longer in the corpus: %d" % len(set(golden["rows"]) - names))
    stale = [n for n, r in prep.items() if "error" not in r and n in golden["rows"]
             and golden["rows"][n]["hash"] != current_hash(r)]
    print("pinned rows stale against the prepared sources: %d %s" % (len(stale), stale[:10]))
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)

    def common(p, run=False):
        p.add_argument("--workdir", required=True,
                       help="scratch dir for prep files / raw tool output (not pinned)")
        p.add_argument("--golden", default=None, help="golden file (default: harness/sv/xcelium_golden.json)")
        p.add_argument("--case", nargs="*", default=None, help="only these rows")
        if run:
            p.add_argument("--host", default=HOST)
            p.add_argument("--label", default="ls-sv-golden",
                           help="remote dir name under %s (yours alone)" % REMOTE_ROOT)
            p.add_argument("--poll", type=int, default=20, help="seconds between progress polls")

    p = sub.add_parser("prepare")
    common(p)
    p.add_argument("--lean-wrapper", default=os.environ.get("SV_LEAN_WRAPPER"),
                   help="command prefixed to every lake call (e.g. the Lean slot script)")
    p.add_argument("--force", action="store_true")
    p.add_argument("--retry-errors", action=argparse.BooleanOptionalAction, default=True)
    p.set_defaults(fn=cmd_prepare)

    p = sub.add_parser("run")
    common(p, run=True)
    p.add_argument("--batch-size", type=int, default=40)
    p.add_argument("--follow", action="store_true", help="wait for a concurrent `prepare`")
    p.add_argument("--retry-failed", action="store_true", help="re-run pinned non-ok rows too")
    p.add_argument("--rebase", action="store_true", help="re-run everything after an Xcelium version change")
    p.add_argument("--limit", type=int, default=None, help="stop after N rows (testing)")
    p.set_defaults(fn=cmd_run)

    p = sub.add_parser("verify")
    common(p, run=True)
    p.add_argument("--sample", type=int, default=10)
    p.add_argument("--seed", type=int, default=0)
    p.set_defaults(fn=cmd_verify)

    p = sub.add_parser("status")
    p.add_argument("--workdir", default=None)
    p.add_argument("--golden", default=None)
    p.set_defaults(fn=cmd_status)

    args = ap.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
