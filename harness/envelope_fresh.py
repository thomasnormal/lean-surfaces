#!/usr/bin/env python3
"""ENVELOPE FRESHNESS: does every committed envelope still regenerate?

A lab's `.py` is edited and its `.json` envelope is left a day stale, and the
model goes blind to the new functions while every census passes -- because
**a census of every site that mentions a name cannot find a step that mentions
nothing.** The missing step lives in a different PIPELINE STAGE, not a
different file. Nothing gated that, and mtime cannot: a fresh clone randomizes
it. The only test is re-extract and compare.

THE FRONTEND PIN IS THE LOAD-BEARING FIELD, and it is why this file exists
rather than a one-liner per tier. Measured on the python tier, 61 pairs, twice:

    interpreter          byte-identical   stamp-only   CONTENT DRIFT
    python3.14.5                4             53             4
    python3.9.19 (pinned)      55              4             2

Same corpus, same script, same comparison -- **different interpreter, different
verdict.** The envelopes stamp their frontend, so under the wrong one this
becomes *a version detector wearing a freshness label*, reporting 53 false
stamp rows and TWO FALSE CONTENT DRIFTS.

> Ignoring the stamp is not sufficient: a different frontend changes CONTENT,
> not just the stamp. So the pin is CHECKED BEFORE ANYTHING IS COMPARED, and
> its absence is a REFUSAL -- never a comparison made anyway.

FOUR FIELDS PER TIER, and the fourth is the one people forget:
    corpus    where the envelopes are
    extract   how to regenerate one
    frontend  WHAT MUST BE TRUE of the extracting frontend, checked first
    stamp     which keys are stamp and are excluded from the comparison
An under-specified comparison set is how two people get two verdicts from one
corpus, which is exactly what the table above shows.

Usage:  envelope_fresh.py --tier python [root]
        envelope_fresh.py --list
        envelope_fresh.py --self-test
Exit:   0 fresh   1 stale   3 instrument refusal (incl. absent frontend)
"""

from __future__ import annotations

import argparse
import copy
import glob
import json
import os
import shutil
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# `frontend.expect` is a dict of key -> required value inside the envelope's own
# stamp; `probe` yields the same keys from the LIVE toolchain. A tier whose
# envelopes record a FAMILY (sv: `pyslang-11`) pins the family, not the exact
# version -- which is why a point release stops being an event.
MANIFESTS = {
    "python": {
        "corpus": "Examples/python/*/*.json",
        "schema_key": "schema_version",
        # NO MIRROR: this extractor ABSOLUTIZES `source_file` in its output, so
        # running it anywhere but the repo root rewrites the very field being
        # compared -- measured, all 61 pairs went STALE on one key.  It also
        # honours --out, so nothing is written into the tree.
        "mirror": False,
        # SINGLE-SCHEMA TIER: one command serves every envelope, which is why
        # this entry worked from the day it was written -- and why copying its
        # SHAPE to a multi-schema tier produced an entry that had never
        # extracted one real envelope.
        "extract": {"*": {"argv": ["{frontend}", "{repo}/extractors/python/extract.py",
                                   "{src}", "--out", "{out}",
                                   "--companion-dir", "{tmp}"],
                          "out": "{out}"}},
        "frontend": {
            "kind": "interpreter",
            "candidates": ["python3.9"],
            "expect": {"name": "cpython-ast", "version": "3.9.19"},
        },
        "stamp": ["frontend"],
    },
    "sv": {
        "corpus": "Examples/system-verilog/**/*.sv.json",
        "schema_key": "schema_version",
        # MIRROR REQUIRED, for two independent reasons: the recorded path
        # string is part of the envelope (sv_round_trip found this the
        # expensive way), and an sv-0.1 invocation writes `<source>.json`
        # BESIDE its input -- which without a mirror is inside the repository.
        "mirror": True,
        # TWO SCHEMAS, TWO COMMANDS.  sv-0.1 takes a bare invocation and writes
        # `<source>.json` BESIDE the source; sv-0.2 is symbolic and requires
        # `--top` with `-o`.  A single static argv cannot express that, and the
        # first version of this entry was rejected by the extractor for all six
        # sv-0.1 envelopes.
        "extract": {
            "sv-0.1": {"argv": ["{frontend}", "{repo}/extractors/sv/extract.py", "{src}"],
                       "out": "{src}.json"},
            "sv-0.2": {"argv": ["{frontend}", "{repo}/extractors/sv/extract.py",
                                "--top", "{top}", "{srcs}", "-o", "{out}"],
                       "out": "{out}"},
        },
        "frontend": {
            "kind": "interpreter-module",
            "candidates": ["python3.12", "python3"],
            "module": "pyslang",
            "expect": {"name": "pyslang", "family": "pyslang-11"},
        },
        "stamp": ["frontend"],
    },
}


class Refuse(Exception):
    """The instrument cannot answer; never a freshness verdict."""


# AN ABSENT EXECUTABLE RAISES, IT DOES NOT RETURN.  The first cut let
# FileNotFoundError escape, so the pinned-frontend-absent path CRASHED where it
# was supposed to REFUSE -- found by exercising that path rather than writing
# it, which is the only way this class of bug is ever found.
def _probe(argv: list) -> str | None:
    try:
        r = subprocess.run(argv, capture_output=True, text=True)
    except OSError:
        return None
    return r.stdout.strip() if r.returncode == 0 else None


def _interp_version(exe: str) -> str | None:
    return _probe([exe, "-c", "import sys;print('%d.%d.%d' % sys.version_info[:3])"])


def _module_major(exe: str, mod: str) -> str | None:
    return _probe([exe, "-c", "import %s;print(%s.__version__)" % (mod, mod)])


def resolve_frontend(man: dict) -> str:
    """The executable that satisfies the pin, or Refuse. CHECKED BEFORE COMPARING."""
    f = man["frontend"]
    want = f["expect"]
    tried = []
    for exe in f["candidates"]:
        if f["kind"] == "interpreter":
            got = _interp_version(exe)
            tried.append("%s -> %s" % (exe, got or "absent"))
            if got == want.get("version"):
                return exe
        elif f["kind"] == "interpreter-module":
            got = _module_major(exe, f["module"])
            fam = ("%s-%s" % (f["module"], got.split(".")[0])) if got else None
            tried.append("%s -> %s" % (exe, fam or "no %s" % f["module"]))
            if fam == want.get("family"):
                return exe
    raise Refuse(
        "the pinned frontend is not available: need %s, tried [%s].\n"
        "  REFUSING rather than comparing: a different frontend changes envelope\n"
        "  CONTENT, not just the stamp. A comparison made anyway is\n"
        "  a version detector wearing a freshness label." % (want, "; ".join(tried) or "nothing"))


def _strip(env: dict, stamp: list) -> dict:
    e = copy.deepcopy(env)
    for k in stamp:
        e.pop(k, None)
    return e


def _recorded_sources(env: dict) -> list:
    """The source paths AS THE ENVELOPE RECORDS THEM, both shapes.

    sv-0.1 and python record `source_file`: a string.  sv-0.2 records
    `source_files`: a LIST OF DICTS, `{"path": ..., "sha256": ...}`.  Reading
    only the string key rowed twelve live sv-0.2 envelopes NOT-LIVE -- and
    NOT-LIVE reads as benign, so a genuinely stale envelope among them would
    have been SILENTLY EXCUSED.  Two instruments, one corpus, two verdicts:
    the failure this file's own docstring names.

    THE RECORDED STRING IS RETURNED, never a resolved absolute path: the path
    as written is part of the envelope's content, so re-extraction must be
    given the same spelling or the comparison differs by the path alone.
    """
    out = []
    one = env.get("source_file")
    if isinstance(one, str) and one:
        out.append(one)
    many = env.get("source_files")
    if isinstance(many, list):
        for item in many:
            if isinstance(item, dict):
                p = item.get("path")
            else:
                p = item
            if isinstance(p, str) and p:
                out.append(p)
    return out


def _resolve(recorded: str, envpath: str, root: str) -> str | None:
    """The file a recorded path names in THIS tree, or None."""
    if os.path.isabs(recorded):
        # An absolute path is a run from another machine: it can never be
        # mirrored faithfully here.  That is the genuine NOT-LIVE case.
        return recorded if os.path.isfile(recorded) else None
    cand = os.path.join(root, recorded)
    if os.path.isfile(cand):
        return cand
    sib = os.path.join(os.path.dirname(envpath), os.path.basename(recorded))
    return sib if os.path.isfile(sib) else None


def _argv_for(man: dict, env: dict) -> dict | None:
    """The extract recipe for THIS envelope's schema, or None if unhandled."""
    table = man["extract"]
    if isinstance(table, list):                 # legacy single-command form
        return {"argv": table, "out": "{out}"}
    schema = env.get(man.get("schema_key", "schema_version"))
    return table.get(schema) or table.get("*")


def check_tier(man: dict, root: str, frontend: str) -> tuple[int, list]:
    rows = []
    for envpath in sorted(glob.glob(os.path.join(root, man["corpus"]), recursive=True)):
        rel = os.path.relpath(envpath, root)
        try:
            env = json.load(open(envpath, encoding="utf-8"))
        except Exception as e:                                  # noqa: BLE001
            rows.append(("UNREADABLE", rel, str(e))); continue

        recorded = _recorded_sources(env)
        if not recorded:
            rows.append(("NOT-LIVE", rel, "the envelope records no source")); continue
        resolved = [_resolve(r, envpath, root) for r in recorded]
        if all(r is None for r in resolved):
            rows.append(("NOT-LIVE", rel, "recorded sources are not in this tree")); continue
        if any(r is None for r in resolved):
            # PARTIAL IS NOT BENIGN: some sources present and some absent means
            # the envelope cannot be faithfully re-extracted, and calling that
            # NOT-LIVE would excuse it.
            missing = [c for c, r in zip(recorded, resolved) if r is None]
            rows.append(("SOURCES-MISSING", rel, "absent: %s" % ", ".join(missing[:3])))
            continue

        recipe = _argv_for(man, env)
        if recipe is None:
            rows.append(("NO-RECIPE", rel, "no extract command for schema %r"
                         % env.get(man.get("schema_key", "schema_version"))))
            continue

        # A MIRROR OF THE RECORDED LAYOUT.  The extractor is run with the paths
        # SPELLED AS THE ENVELOPE RECORDS THEM, inside a scratch tree, so the
        # path string in the output matches -- and so nothing is ever written
        # into the repository, including the `<source>.json` an sv-0.1
        # invocation drops beside its input.
        tmp = tempfile.mkdtemp(prefix="envfresh.")
        # WHETHER TO MIRROR IS A PER-TIER FACT, not a universal one: it depends
        # on whether the extractor rewrites the recorded path and on where it
        # puts its output.  The manifest is where per-tier facts live.
        cwd = tmp if man.get("mirror") else root
        if man.get("mirror"):
            for rec, real in zip(recorded, resolved):
                dst = os.path.join(tmp, rec)
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                shutil.copyfile(real, dst)
        # THE SCRIPT IS ABSOLUTE, THE SOURCES ARE NOT.  Extraction runs with
        # cwd=mirror so the recorded path strings reproduce; that same cwd
        # makes a repo-relative extractor path unopenable, which turned all 61
        # python pairs into EXTRACT-FAILED the moment the mirror landed.
        subst = {"frontend": frontend, "repo": os.path.abspath(root),
                 "src": recorded[0], "out": os.path.join(tmp, "_out.json"),
                 "tmp": tmp, "top": str(env.get("top") or "")}
        argv = []
        for part in recipe["argv"]:
            if part == "{srcs}":
                argv.extend(recorded)
            else:
                argv.append(part.format(**subst))
        outp = recipe["out"].format(**subst)
        if not os.path.isabs(outp):
            outp = os.path.join(tmp, outp)
        r = subprocess.run(argv, capture_output=True, text=True, cwd=cwd)
        if r.returncode != 0 or not os.path.isfile(outp):
            tail = (r.stderr or "").strip().splitlines()
            rows.append(("EXTRACT-FAILED", rel, tail[-1] if tail else "rc=%d" % r.returncode))
            continue
        new_env = json.load(open(outp, encoding="utf-8"))
        if _strip(env, man["stamp"]) == _strip(new_env, man["stamp"]):
            rows.append(("FRESH", rel, ""))
        else:
            rows.append(("STALE", rel, "content differs from a re-extraction"))
    bad = sum(1 for v, _, _ in rows
              if v in ("STALE", "EXTRACT-FAILED", "UNREADABLE", "SOURCES-MISSING", "NO-RECIPE"))
    return bad, rows


def _report(tier: str, rows: list, bad: int) -> None:
    for verdict, rel, note in rows:
        if verdict != "FRESH":
            print("%-14s %s%s" % (verdict, rel, ("  -- " + note) if note else ""))
    counts = {}
    for v, _, _ in rows:
        counts[v] = counts.get(v, 0) + 1
    print("envelope_fresh[%s]: %s" % (tier, ", ".join(
        "%s %d" % (k, counts[k]) for k in sorted(counts))))
    if bad:
        print("  A STALE envelope is a pipeline stage nobody re-ran: regenerate it with the")
        print("  tier's extractor and commit the result beside its source.")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--tier")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("root", nargs="?", default=REPO)
    a = ap.parse_args(argv)
    if a.self_test:
        return self_test()
    if a.list:
        for t, m in sorted(MANIFESTS.items()):
            print("%-8s corpus=%-34s frontend=%s" % (t, m["corpus"], m["frontend"]["expect"]))
        return 0
    if not a.tier or a.tier not in MANIFESTS:
        print("envelope_fresh: --tier must be one of: %s" % ", ".join(sorted(MANIFESTS)),
              file=sys.stderr)
        return 3
    man = MANIFESTS[a.tier]
    try:
        frontend = resolve_frontend(man)
    except Refuse as e:
        print("envelope_fresh[%s]: REFUSING -- %s" % (a.tier, e), file=sys.stderr)
        return 3
    print("envelope_fresh[%s]: frontend %s satisfies %s" % (a.tier, frontend, man["frontend"]["expect"]))
    bad, rows = check_tier(man, a.root, frontend)
    _report(a.tier, rows, bad)
    return 1 if bad else 0


# ---------------------------------------------------------------- self-test
#
# A SYNTHETIC TIER, deliberately: what is under test is the harness -- the pin,
# the stamp exclusion, the verdicts -- not any lane's extractor. Driving it
# from a real corpus would make this slow, and red for reasons that belong to
# the tier rather than to the code being tested.
def _fixture(tmp: str, envelope: dict, source: str = "x = 1\n") -> dict:
    """A one-pair corpus plus a fake extractor that regenerates it."""
    os.makedirs(os.path.join(tmp, "Examples", "fake", "a"), exist_ok=True)
    src = os.path.join(tmp, "Examples", "fake", "a", "a.py")
    open(src, "w").write(source)
    open(os.path.join(tmp, "Examples", "fake", "a", "a.json"), "w").write(
        json.dumps(envelope, indent=2))
    ex = os.path.join(tmp, "fake_extract.py")
    open(ex, "w").write(
        "import json,sys\n"
        "src=sys.argv[1]; out=sys.argv[sys.argv.index('--out')+1]\n"
        "json.dump({'frontend':{'name':'fake','version':'9.9.9'},\n"
        "           'source_file':'Examples/fake/a/a.py',\n"
        "           'body':open(src).read()}, open(out,'w'), indent=2)\n")
    return {
        "corpus": "Examples/fake/*/*.json",
        "extract": [sys.executable, ex, "{src}", "--out", "{out}"],
        "frontend": {"kind": "interpreter", "candidates": [sys.executable],
                     "expect": {"version": "%d.%d.%d" % sys.version_info[:3]}},
        "stamp": ["frontend"],
    }


def self_test() -> int:
    ok = bad = 0

    def check(name, got, want):
        nonlocal ok, bad
        if got == want:
            ok += 1; print("  ok   %s" % name)
        else:
            bad += 1; print("  FAIL %s: got %r want %r" % (name, got, want))

    live = {"frontend": {"name": "fake", "version": "9.9.9"},
            "source_file": "Examples/fake/a/a.py", "body": "x = 1\n"}

    # 1. FRESH: the committed envelope still regenerates.
    with tempfile.TemporaryDirectory() as t:
        man = _fixture(t, live)
        n, rows = check_tier(man, t, resolve_frontend(man))
        check("a fresh envelope passes", n, 0)
        check("  ...and is reported FRESH", rows[0][0], "FRESH")

    # 2. STALE: the source moved on and the envelope did not -- the defect.
    with tempfile.TemporaryDirectory() as t:
        man = _fixture(t, live, source="x = 1\ndef added(): pass\n")
        n, rows = check_tier(man, t, resolve_frontend(man))
        check("an envelope left behind is STALE", n, 1)
        check("  ...named as STALE", rows[0][0], "STALE")

    # 3. THE STAMP IS EXCLUDED: differing ONLY in the stamp is not staleness.
    #    Without this the python tier reads 53 of 61 stale on a fresh clone.
    with tempfile.TemporaryDirectory() as t:
        stamped = dict(live, frontend={"name": "fake", "version": "0.0.1"})
        man = _fixture(t, stamped)
        n, rows = check_tier(man, t, resolve_frontend(man))
        check("a stamp-only difference is FRESH", rows[0][0], "FRESH")
        check("  ...so it is not a failure", n, 0)

    # 4. THE PIN, ABSENT -- EXERCISED, not written. This is the path that turns
    #    the gate into a version detector if it is ever allowed to proceed.
    with tempfile.TemporaryDirectory() as t:
        man = _fixture(t, live)
        man["frontend"] = {"kind": "interpreter",
                           "candidates": ["python9.9-does-not-exist"],
                           "expect": {"version": "9.9.9"}}
        try:
            resolve_frontend(man)
            check("an absent frontend REFUSES", "compared anyway", "refused")
        except Refuse as e:
            check("an absent frontend REFUSES", "refused", "refused")
            check("  ...naming what it needed", "9.9.9" in str(e), True)
            check("  ...and what it tried", "python9.9-does-not-exist" in str(e), True)
            check("  ...saying why it did not compare",
                  "version detector" in str(e), True)

    # 5. A WRONG-VERSION frontend refuses too: present is not the same as pinned.
    with tempfile.TemporaryDirectory() as t:
        man = _fixture(t, live)
        man["frontend"]["expect"] = {"version": "0.0.0"}
        try:
            resolve_frontend(man)
            check("a MISMATCHED frontend refuses", "compared anyway", "refused")
        except Refuse:
            check("a MISMATCHED frontend refuses", "refused", "refused")

    # 6. NOT-LIVE is not a failure: a source outside this tree records a run
    #    that cannot be repeated here (SV's three CV32E40P phase-1 envelopes).
    with tempfile.TemporaryDirectory() as t:
        man = _fixture(t, dict(live, source_file="/nowhere/absent.py"))
        os.remove(os.path.join(t, "Examples", "fake", "a", "a.py"))
        n, rows = check_tier(man, t, resolve_frontend(man))
        check("an off-tree source is NOT-LIVE", rows[0][0], "NOT-LIVE")
        check("  ...and does not fail the gate", n, 0)

    # 7. THE SHAPE THAT WAS WRONG: sv-0.2 records `source_files`, a LIST OF
    #    DICTS.  Reading only the string key rowed twelve live envelopes
    #    NOT-LIVE -- benign-looking, so a stale one among them was excused.
    check("a string source_file is read",
          _recorded_sources({"source_file": "a/b.sv"}), ["a/b.sv"])
    check("a LIST OF DICTS is read too",
          _recorded_sources({"source_files": [{"path": "a/x.sv", "sha256": "z"},
                                              {"path": "a/y.sv"}]}),
          ["a/x.sv", "a/y.sv"])
    check("  ...and a list of plain strings",
          _recorded_sources({"source_files": ["a/x.sv"]}), ["a/x.sv"])
    check("an envelope with neither records nothing",
          _recorded_sources({"top": "m"}), [])

    # 8. SCHEMA DISPATCH: one static argv cannot serve two schemas.
    man2 = {"schema_key": "schema_version",
            "extract": {"sv-0.1": {"argv": ["one"], "out": "{out}"},
                        "sv-0.2": {"argv": ["two"], "out": "{out}"}}}
    check("sv-0.1 gets its own command",
          _argv_for(man2, {"schema_version": "sv-0.1"})["argv"], ["one"])
    check("sv-0.2 gets a different one",
          _argv_for(man2, {"schema_version": "sv-0.2"})["argv"], ["two"])
    check("an unknown schema has NO recipe",
          _argv_for(man2, {"schema_version": "sv-9.9"}), None)
    check("a single-schema tier still works",
          _argv_for({"extract": {"*": {"argv": ["any"], "out": "{out}"}}}, {})["argv"], ["any"])

    # 9. A TWO-SCHEMA TIER, EXTRACTED END TO END.  A manifest entry that has
    #    never extracted one envelope is the unexercised-gate shape, so the
    #    dispatch is exercised rather than asserted -- synthetically, because
    #    the real sv corpus needs pyslang, which this box does not have.
    with tempfile.TemporaryDirectory() as t:
        man = _fixture(t, live)
        ex = os.path.join(t, "two_schema.py")
        open(ex, "w").write(
            "import json,sys\n"
            "mode=sys.argv[1]; src=sys.argv[2]; out=sys.argv[sys.argv.index('--out')+1]\n"
            "json.dump({'frontend':{'name':'fake','version':'9.9.9'},'schema':mode,\n"
            "           'source_file':'Examples/fake/a/a.py','body':open(src).read()},\n"
            "          open(out,'w'), indent=2)\n")
        man["schema_key"] = "schema"
        man["extract"] = {"A": {"argv": [sys.executable, ex, "A", "{src}", "--out", "{out}"], "out": "{out}"},
                          "B": {"argv": [sys.executable, ex, "B", "{src}", "--out", "{out}"], "out": "{out}"}}
        env = json.load(open(os.path.join(t, "Examples", "fake", "a", "a.json")))
        for mode in ("A", "B"):
            env["schema"] = mode
            open(os.path.join(t, "Examples", "fake", "a", "a.json"), "w").write(json.dumps(env, indent=2))
            n, r = check_tier(man, t, resolve_frontend(man))
            check("schema %s extracts and matches" % mode, (r[0][0], n), ("FRESH", 0))
        env["schema"] = "C"
        open(os.path.join(t, "Examples", "fake", "a", "a.json"), "w").write(json.dumps(env, indent=2))
        n, r = check_tier(man, t, resolve_frontend(man))
        check("an unhandled schema is NO-RECIPE", r[0][0], "NO-RECIPE")
        check("  ...and fails the gate", n, 1)

    # 10. PARTIAL SOURCES ARE NOT BENIGN: some present, some absent means the
    #     envelope cannot be faithfully re-extracted, and NOT-LIVE would excuse it.
    with tempfile.TemporaryDirectory() as t:
        man = _fixture(t, dict(live, source_files=[{"path": "Examples/fake/a/a.py"},
                                                   {"path": "Examples/fake/a/gone.py"}]))
        n, r = check_tier(man, t, resolve_frontend(man))
        check("a partially-present source set FAILS", r[0][0], "SOURCES-MISSING")
        check("  ...and is not excused", n, 1)

    print("self-test: %d ok, %d failed" % (ok, bad))
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
