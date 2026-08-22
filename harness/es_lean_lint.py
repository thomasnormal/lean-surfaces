#!/usr/bin/env python3
"""es_lean_lint.py — catch the doc-comment-attachment trap BEFORE `lake build`.

In this toolchain a `/-- … -/` doc comment attaches only to a DECLARATION.
Put one before `mutual`, `#guard`, or `set_option … in theorem` and the
file does not parse — with an error that names the following token and not
the comment, so the cause is a line or twenty above the report.

`docs/backlog.md` records it three times (§L66 for `mutual` and `#guard`,
§L82 for the general law, AGENTS.md for the `set_option` case) and this
lane still hit it a fourth time. A law that is known and still costs a
compile every inch is a law that wants a GATE, not more discipline.

    python3 harness/es_lean_lint.py [PATH ...]     # default: the ES lane
    python3 harness/es_lean_lint.py --self-test

Exit 1 and name every offending line; exit 0 when clean. Stdlib only.
"""

import sys
from pathlib import Path

# Commands a doc comment may NOT attach to.  EVERY ENTRY WAS DETERMINED BY
# RUNNING THE TOOLCHAIN, not by reading: the first version of this list also
# held `example`, which is LEGAL — `example` appears in Lean's own
# "expected: …" token list and `/-- doc -/ example : True := trivial`
# compiles.  That false positive fired on `harness/es/float_probe.lean`,
# which is on master and green, so the lint would have accused a passing
# file on its first run.  Verified illegal on v4.33.0-rc1:
BAD_FOLLOWERS = ("#guard", "mutual", "#print", "#check", "#eval",
                 "open", "namespace")

DEFAULT_PATHS = ["LeanModels/Es", "Examples/es", "harness/es"]


def offenders(text):
    """Yield (line-number, following-token) for each misattached doc comment."""
    lines = text.split("\n")
    out = []
    i = 0
    while i < len(lines):
        if lines[i].lstrip().startswith("/--"):
            j = i
            # find the closing `-/` (a one-line doc comment closes on its own line)
            while j < len(lines) and not lines[j].rstrip().endswith("-/"):
                j += 1
            k = j + 1
            # skip blank lines: a doc comment separated by blanks still attaches
            while k < len(lines) and not lines[k].strip():
                k += 1
            if k < len(lines):
                head = lines[k].lstrip().split(" ")[0].split("(")[0]
                if head in BAD_FOLLOWERS:
                    out.append((i + 1, head))
            i = j + 1
        else:
            i += 1
    return out


def check(paths):
    files = []
    for p in paths:
        p = Path(p)
        if p.is_dir():
            files += sorted(p.rglob("*.lean"))
        elif p.is_file():
            files.append(p)
    bad = 0
    for f in files:
        for ln, tok in offenders(f.read_text(encoding="utf-8")):
            print(f"{f}:{ln}: a `/-- -/` doc comment cannot attach to `{tok}` "
                  f"— use a plain `/- -/` block comment", file=sys.stderr)
            bad += 1
    if bad:
        print(f"es_lean_lint: {bad} misattached doc comment(s) in {len(files)} file(s)",
              file=sys.stderr)
        return 1
    print(f"es_lean_lint: {len(files)} files clean")
    return 0


def self_test():
    bad = "/-- doc -/\n#guard true\n"
    assert offenders(bad) == [(1, "#guard")], offenders(bad)
    bad2 = "/-- doc\nspanning -/\nmutual\n"
    assert offenders(bad2) == [(1, "mutual")], offenders(bad2)
    bad3 = "/-- doc -/\n\n\n#guard true\n"          # blanks do not save it
    assert offenders(bad3) == [(1, "#guard")], offenders(bad3)
    ok1 = "/-- doc -/\ndef f := 1\n"
    assert offenders(ok1) == [], offenders(ok1)
    ok2 = "/- plain -/\n#guard true\n"              # the correct spelling
    assert offenders(ok2) == [], offenders(ok2)
    ok3 = "/-! section -/\n#guard true\n"           # section comments are fine
    assert offenders(ok3) == [], offenders(ok3)
    # `example` IS a legal attachment point — the false positive this list
    # shipped with once.  Pinned so it cannot come back.
    ok4 = "/-- doc -/\nexample : True := trivial\n"
    assert offenders(ok4) == [], offenders(ok4)
    print("  ok: a doc comment before #guard is caught")
    print("  ok: a doc comment before `mutual` is caught")
    print("  ok: intervening blank lines do not hide it")
    print("  ok: a doc comment before a real declaration is NOT flagged")
    print("  ok: `/- -/` and `/-! -/` are NOT flagged")
    print("  ok: `example` is NOT flagged (it is a legal attachment point)")
    return 0


if __name__ == "__main__":
    args = sys.argv[1:]
    if args and args[0] == "--self-test":
        sys.exit(self_test())
    sys.exit(check(args or DEFAULT_PATHS))
