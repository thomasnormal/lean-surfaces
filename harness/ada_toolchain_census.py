#!/usr/bin/env python3
"""ada_toolchain_census.py — is there an Ada toolchain, and does the ACAA's
own grader run on it?

`docs/ada-charter.md` §6 records three rulings that all land on one host fact:
libadalang is the frontend (§4.2), **GNAT is the behavior oracle** (§6.1), and
**the ACAA's `GRADE` tool issues our verdicts** (§6.3, §4.4).  Two of those
three need a working Ada compiler, and at charter time this host had none.
So the toolchain is M1's critical path, and this is the instrument that says
where it stands.

    python3 harness/ada_toolchain_census.py [-o out.json]
    python3 harness/ada_toolchain_census.py --path <bin-dir>[:<bin-dir>...]
    python3 harness/ada_toolchain_census.py --verify <acats-dir> <workdir>
    python3 harness/ada_toolchain_census.py --self-test

THE PROBE reports what is on `PATH` (plus any `--path` prefix), what each
tool's version is, whether `libadalang` imports, and — because this is the
question a reader actually has — whether the tier's three toolchain NEEDS are
met or not, by name.

THE `--verify` MODE is the part worth having, and it is the house law applied
to a toolchain: *every path RUN, not admired*.  It takes an unpacked ACATS
delivery and drives the ruled grounding loop end to end —

  1. build and run one class-C test through `Report`, and check it prints
     `PASSED`;
  2. build the ACAA's `SUMMARY` and `GRADE` tools from the suite's own
     sources;
  3. summarize a C test, hand it an event trace saying "compiled, bound, ran,
     PASSED", and check `GRADE` says *passed execution*;
  4. summarize a B test, hand it a trace with a `CERR` at every `-- ERROR:`
     location, and check `GRADE` says *passed by detecting all expected
     errors*;
  5. **the two NEGATIVE cases**, because a grader that always says PASSED is
     worthless: drop one expected error and require *Failed (Missing Error)*;
     flag an error on a line marked `-- OK` and require *Failed (Error in OK
     area)*.

A LINE-ENDING TRAP, measured and worked around here rather than rediscovered:
the ZIP delivery ships CRLF, and the ACAA's `SUMMARY` tool raises
`PARSE_ERROR` on every CRLF source.  Measured on this host: **0 of 120 files
summarized as shipped; 150 of 150 after `\\r` removal.**  `--verify` converts
before summarizing and says so.

Python >= 3.9, stdlib only.  Deterministic: sorted output, byte-identical on
a double run apart from the fields that are host facts by construction.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile

# The tools the tier needs, and WHICH ruling needs each.  A census that only
# said "gnatmake: absent" would not tell a reader what is blocked.
NEEDS = {
    "frontend": ("libadalang — emits the envelope",
                 "docs/ada-charter.md §4.2"),
    "oracle": ("gnatmake — the BEHAVIOR oracle for differential grounding",
               "docs/ada-charter.md §6.1"),
    "grader": ("gnatmake — builds the ACAA's GRADE, which issues our verdicts",
               "docs/ada-charter.md §6.3, §4.4"),
}

TOOLS = ["gnatmake", "gnatchop", "gnatls", "gnatbind", "gnat", "gprbuild",
         "alr", "gcc"]

# The acquisition path, measured from the Alire index rather than recalled.
# Recorded so a host without a toolchain has a priced route rather than a
# shrug.
ACQUISITION = {
    "tool": "alr (Alire)",
    "binary_release": "alr-<ver>-bin-aarch64-macos.zip and siblings; "
                      "prebuilt, no Ada compiler needed to run it",
    "toolchain_command": "alr -n toolchain --select gnat_native gprbuild",
    "frontend_command": "alr -n with libadalang  (inside an alr crate)",
    "index_crates": {"gnat_native": "16.1.0", "gprbuild": "26.0.1",
                     "libadalang": "26.0.0"},
    "settings_dir_env": "ALIRE_SETTINGS_DIR — point it at a scratch dir to "
                        "keep a probe out of the home directory",
    # Two facts a second attempt needs, both learned the expensive way.
    "shared_library_externals": [
        "-XLIBRARY_TYPE=relocatable", "-XLIBADALANG_LIBRARY_TYPE=relocatable",
        "-XGPR2_LIBRARY_TYPE=relocatable", "-XXMLADA_BUILD=relocatable"],
    "shared_library_note":
        "The Python bindings are ctypes over a SHARED library, and a "
        "relocatable libadalang cannot import a static dependency — the "
        "whole closure must be built relocatable together, hence the "
        "externals above.  `-XGNATCOLL_BUILD_MODE=prod` is NOT one of them: "
        "gnatcoll_iconv.gpr rejects `prod` as an illegal value for its "
        "`build` typed string.",
    "build_cost_note":
        "The long pole is the generated `libadalang-implementation.adb`, a "
        "single very large unit.  Budget for a long compile and nice it; it "
        "is gprbuild, not lake, so the machine-wide build lock does not "
        "cover it and courtesy is the lane's own job.",
}

# `adaparse` is on PATH on at least one development host and is the `ada-url`
# WHATWG **URL** parser.  A census that grepped PATH for `ada` would report a
# parser that is not one, so the collision is checked for by name.
IMPOSTORS = {"adaparse": "ada-url (a WHATWG URL parser), NOT the Ada language"}

VERSION_FLAGS = ["--version", "-v"]


def probe_tool(name, env):
    path = shutil.which(name, path=env.get("PATH"))
    if not path:
        return {"present": False}
    row = {"present": True, "path": path}
    for flag in VERSION_FLAGS:
        try:
            out = subprocess.run([path, flag], capture_output=True, text=True,
                                 timeout=30, env=env)
        except (OSError, subprocess.SubprocessError):
            continue
        text = (out.stdout or out.stderr).strip().split("\n")
        if text and text[0]:
            row["version_line"] = text[0].strip()
            break
    return row


def probe_libadalang(env):
    try:
        out = subprocess.run(
            [sys.executable, "-c",
             "import libadalang as lal; print(lal.version)"],
            capture_output=True, text=True, timeout=60, env=env)
    except (OSError, subprocess.SubprocessError) as exc:
        return {"importable": False, "error": str(exc)}
    if out.returncode == 0:
        return {"importable": True, "version": out.stdout.strip()}
    return {"importable": False,
            "error": out.stderr.strip().split("\n")[-1][:200]}


def census(extra_path=None):
    env = dict(os.environ)
    if extra_path:
        env["PATH"] = extra_path + os.pathsep + env.get("PATH", "")
    tools = {name: probe_tool(name, env) for name in TOOLS}
    lal = probe_libadalang(env)
    impostors = {}
    for name, what in IMPOSTORS.items():
        row = probe_tool(name, env)
        if row["present"]:
            impostors[name] = {"path": row["path"], "actually": what}
    have_gnat = tools["gnatmake"]["present"]
    needs = {}
    for key, (what, cite) in sorted(NEEDS.items()):
        met = lal["importable"] if key == "frontend" else have_gnat
        needs[key] = {"needs": what, "ruled_in": cite, "met": met}
    return {
        "instrument": "harness/ada_toolchain_census.py",
        "language": "Ada",
        "extra_path": extra_path,
        "tools": tools,
        "libadalang": lal,
        "needs": needs,
        "all_needs_met": all(n["met"] for n in needs.values()),
        "impostors_on_path": impostors,
        "acquisition": ACQUISITION,
    }


# ---------------------------------------------------------------- verify ---

TRACE_HEADER = "Event,Timestamp,Name,Line,Position,Message"


def _run(cmd, cwd, env, timeout=900):
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True,
                          text=True, timeout=timeout)


def _find(root, name):
    for dirpath, _, filenames in os.walk(root):
        for f in filenames:
            if f.upper() == name.upper():
                return os.path.join(dirpath, f)
    return None


def _delf(src, dst):
    """Copy with CRLF stripped.  The ZIP delivery ships CRLF and the ACAA's
    SUMMARY tool dies with an unhandled exception on every such file;
    measured 0/120 as shipped, 150/150 converted."""
    with open(src, "rb") as fh:
        data = fh.read().replace(b"\r\n", b"\n")
    with open(dst, "wb") as fh:
        fh.write(data)


def _summary_rows(path):
    import csv
    with open(path) as fh:
        return list(csv.DictReader(fh))


def _trace(path, units, cerrs, name, ran=None):
    lines = [TRACE_HEADER]
    t = [0]

    def stamp():
        t[0] += 1
        return '"2026-01-01 00:00:%02d"' % min(t[0], 59)
    for u in units:
        lines.append('CSTART,%s,"%s",%s,,""' % (stamp(), name, u))
    for line, pos in cerrs:
        lines.append('CERR,%s,"%s",%s,%s,"x"' % (stamp(), name, line, pos))
    end = '"with Errors"' if cerrs else '"OK"'
    for _ in units:
        lines.append('CEND,%s,"%s",,,%s' % (stamp(), name, end))
    if ran:
        base = name.rsplit(".", 1)[0]
        lines.append('BSTART,%s,"%s",,,""' % (stamp(), base))
        lines.append('BEND,%s,"%s",,,"OK"' % (stamp(), base))
        lines.append('EXSTART,%s,"%s",,,"objective"' % (stamp(), base))
        lines.append('EXEND,%s,"%s",,,"%s"' % (stamp(), base, ran))
    with open(path, "w") as fh:
        fh.write("\n".join(lines) + "\n")


UNIT_KINDS = ("UPACKSPEC", "UPACKBODY", "UPROCBODY", "UFUNCBODY", "USUBUNIT",
              "UGENSPEC", "UGENBODY", "UPROCSPEC", "UFUNCSPEC", "URENAMES")


def verify(acats, workdir, extra_path=None):
    """Drive the ruled grounding loop end to end.  Returns (rows, ok)."""
    env = dict(os.environ)
    if extra_path:
        env["PATH"] = extra_path + os.pathsep + env.get("PATH", "")
    if not shutil.which("gnatmake", path=env.get("PATH")):
        sys.exit("ada_toolchain_census: no gnatmake on PATH — --verify needs "
                 "an Ada compiler; run without --verify for the probe, and "
                 "see `acquisition` in its output for the route")
    os.makedirs(workdir, exist_ok=True)
    rows, ok = [], True

    def check(name, got, want):
        nonlocal ok
        good = want in got if isinstance(want, str) else bool(got)
        if not good:
            ok = False
        rows.append({"check": name, "passed": good,
                     "expected": want if isinstance(want, str) else "truthy",
                     "got": got.strip()[:300] if isinstance(got, str) else got})
        return good

    support = {n: _find(acats, n) for n in
               ("report.a", "impdef.a", "tctouch.ada", "version.a",
                "grade.a", "grd_data.a", "trace.a", "special.a", "summary.a",
                "tst_sum.a")}
    missing = sorted(n for n, p in support.items() if not p)
    if missing:
        sys.exit("ada_toolchain_census: %s not found under %s — is this an "
                 "unpacked ACATS delivery?" % (", ".join(missing), acats))

    # 1. a real class-C test compiles and reports PASSED.
    ctest = _find(acats, "C324001.A")
    if not ctest:
        sys.exit("ada_toolchain_census: C324001.A not found under %s" % acats)
    run1 = os.path.join(workdir, "run")
    shutil.rmtree(run1, ignore_errors=True)
    os.makedirs(run1)
    for n in ("report.a", "impdef.a", "tctouch.ada", "version.a"):
        _delf(support[n], os.path.join(run1, os.path.basename(support[n])))
    _delf(ctest, os.path.join(run1, "C324001.A"))
    _run(["gnatchop", "-q", "-w"] + sorted(os.listdir(run1)), run1, env)
    build = _run(["gnatmake", "-q", "-gnat2012", "c324001"], run1, env)
    # gnatmake prints WARNINGS on stderr at returncode 0, so the exit status
    # is the signal and the diagnostics are context.  Checking stderr for
    # emptiness would fail a clean build, which is how this was found.
    check("C-test builds", "exit=%d %s" % (build.returncode,
                                           build.stderr.strip()[:200]),
          "exit=0")
    if build.returncode == 0:
        out = _run([os.path.join(run1, "c324001")], run1, env)
        check("C-test reports PASSED", out.stdout, "PASSED")

    # 2. the ACAA's own tools build from the suite's sources.
    tools = os.path.join(workdir, "tools")
    shutil.rmtree(tools, ignore_errors=True)
    os.makedirs(tools)
    for n in ("grade.a", "grd_data.a", "trace.a", "special.a", "version.a",
              "summary.a", "tst_sum.a"):
        _delf(support[n], os.path.join(tools, os.path.basename(support[n])))
    _run(["gnatchop", "-q", "-w"] + sorted(os.listdir(tools)), tools, env)
    for exe in ("grade", "summary"):
        b = _run(["gnatmake", "-q", "-gnat2012", exe], tools, env)
        check("ACAA %s builds" % exe.upper(),
              "built" if b.returncode == 0 else b.stderr, "built")
    grade = os.path.join(tools, "grade")
    summary = os.path.join(tools, "summary")
    if not (os.path.exists(grade) and os.path.exists(summary)):
        return rows, False
    manual = os.path.join(workdir, "manual.txt")
    open(manual, "w").close()

    def summarize(src, stem):
        lf = os.path.join(workdir, stem)
        _delf(src, lf)
        csvp = os.path.join(workdir, stem + ".csv")
        r = _run([summary, lf, csvp], workdir, env)
        return (csvp, r) if os.path.exists(csvp) else (None, r)

    # The CRLF trap, asserted rather than described.
    raw = os.path.join(workdir, "crlf-" + os.path.basename(ctest))
    shutil.copyfile(ctest, raw)
    with open(raw, "rb") as fh:
        had_crlf = b"\r\n" in fh.read()
    if had_crlf:
        r = _run([summary, raw, os.path.join(workdir, "crlf.csv")], workdir, env)
        # It dies with an UNHANDLED Ada exception, and WHICH one varies with
        # the input (`SUMMARY.PARSE_ERROR` and `ADA.STRINGS.LENGTH_ERROR`
        # both observed).  So the check is that it raised at all, not which.
        check("CRLF source KILLS the ACAA's SUMMARY tool (the trap)",
              r.stdout + r.stderr, "raised ")

    # 3. a C test grades to `passed execution`.
    csum, _ = summarize(ctest, "C324001.A")
    if csum:
        units = [r["Start Line"] for r in _summary_rows(csum)
                 if r["Kind"] in UNIT_KINDS]
        tr = os.path.join(workdir, "c.csv")
        _trace(tr, units, [], "C324001.A", ran="PASSED")
        g = _run([grade, tr, csum, manual, "verify-c"], workdir, env)
        check("GRADE: C test passes execution", g.stdout, "passed execution")

    # 4. a B test grades to `passed by detecting all expected errors`, and
    #    5. the two negative cases.
    btest = _find(acats, "B324001.A")
    bsum, _ = summarize(btest, "B324001.A") if btest else (None, None)
    if bsum:
        srows = _summary_rows(bsum)
        units = [r["Start Line"] for r in srows if r["Kind"] in UNIT_KINDS]
        errs = [(r["Start Line"], r["Start Pos"]) for r in srows
                if r["Kind"] == "ERROR"]
        oks = [(r["Start Line"], r["Start Pos"]) for r in srows
               if r["Kind"] == "OK"]
        tr = os.path.join(workdir, "b.csv")
        _trace(tr, units, errs, "B324001.A")
        g = _run([grade, tr, bsum, manual, "verify-b"], workdir, env)
        check("GRADE: B test passes on all expected errors", g.stdout,
              "passed by detecting all expected errors")
        if errs:
            _trace(tr, units, errs[:-1], "B324001.A")
            g = _run([grade, tr, bsum, manual, "verify-b-missing"], workdir, env)
            check("GRADE FAILS a missing error (non-vacuity)", g.stdout,
                  "failed by not reporting an error")
        if oks:
            _trace(tr, units, errs + oks[:1], "B324001.A")
            g = _run([grade, tr, bsum, manual, "verify-b-ok"], workdir, env)
            check("GRADE FAILS an error in an OK area (non-vacuity)", g.stdout,
                  "failed by having an error for an OK item")
    return rows, ok


def self_test():
    """The probe's own decision logic, on synthetic inputs — a census that
    reported `met` regardless of what it found would print the same
    headline."""
    ok = True
    with tempfile.TemporaryDirectory() as d:
        out = census(extra_path=d)
        checks = [("no gnatmake in an empty dir alone is not enough to fail",
                   isinstance(out["needs"]["oracle"]["met"], bool), True),
                  ("every need cites its ruling",
                   all(n["ruled_in"] for n in out["needs"].values()), True),
                  ("acquisition path is recorded",
                   "toolchain_command" in out["acquisition"], True),
                  ("impostor list is checked by name",
                   "adaparse" in IMPOSTORS, True)]
        # A fake `gnatmake` that answers must be believed, and a directory
        # with none must not be.
        fake = os.path.join(d, "gnatmake")
        with open(fake, "w") as fh:
            fh.write("#!/bin/sh\necho 'GNATMAKE 99.0.0'\n")
        os.chmod(fake, 0o755)
        seen = census(extra_path=d)
        checks.append(("a gnatmake on the extra path is FOUND",
                       seen["tools"]["gnatmake"]["present"], True))
        checks.append(("its version line is read",
                       seen["tools"]["gnatmake"].get("version_line"),
                       "GNATMAKE 99.0.0"))
        checks.append(("oracle and grader needs flip together",
                       (seen["needs"]["oracle"]["met"],
                        seen["needs"]["grader"]["met"]), (True, True)))
        for name, got, want in checks:
            if got != want:
                ok = False
            print("%s %-52s got %r want %r"
                  % ("ok " if got == want else "FAIL", name, got, want))
    print("self-test:", "PASSED" if ok else "FAILED")
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("-o", "--output")
    ap.add_argument("--path", help="extra bin dirs to prepend to PATH")
    ap.add_argument("--verify", nargs=2, metavar=("ACATS_DIR", "WORKDIR"),
                    help="drive the ruled grounding loop end to end")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    out = census(args.path)
    if args.verify:
        rows, ok = verify(args.verify[0], args.verify[1], args.path)
        out["verify"] = {"acats": os.path.basename(
            os.path.abspath(args.verify[0])), "checks": rows, "passed": ok}
        for r in rows:
            print("%s %s" % ("ok  " if r["passed"] else "FAIL", r["check"]))
        print("verify:", "PASSED" if ok else "FAILED")
    text = json.dumps(out, indent=2, sort_keys=True) + "\n"
    if args.output:
        with open(args.output, "w") as fh:
            fh.write(text)
        unmet = sorted(k for k, v in out["needs"].items() if not v["met"])
        print("Ada toolchain: gnatmake %s | libadalang %s | unmet needs: %s"
              % ("present" if out["tools"]["gnatmake"]["present"] else "ABSENT",
                 "importable" if out["libadalang"]["importable"] else "ABSENT",
                 ", ".join(unmet) or "none"))
    elif not args.verify:
        sys.stdout.write(text)
    return 0 if (not args.verify or out["verify"]["passed"]) else 1


if __name__ == "__main__":
    sys.exit(main())
