#!/usr/bin/env python3
"""c_profile_probe.py — measure a C host against the tier's ABSTRACT profile.

The C tier does not pin ONE machine as its oracle.  It pins the FACTS the
corpus depends on, as a schema, and every host that runs the tier must
SATISFY the schema.  This is the `#guard` of the C lane: a host that
diverges on a depended-on fact is refused by name, loudly, rather than
quietly producing a second set of numbers.

    python3 harness/c_profile_probe.py                     # this host
    python3 harness/c_profile_probe.py --target <triple>   # a cross target
    python3 harness/c_profile_probe.py -o docs/c-profile.json
    python3 harness/c_profile_probe.py --check docs/c-profile.json

WHY CONSTANT FOLDING AND NOT EXECUTION.  Every fact below is decided by
`_Static_assert` under `clang -target <triple> -fsyntax-only`.  clang folds
the constant expression for the TARGET's ABI, so one laptop can certify a
host it cannot execute — which is the whole reason a two-host schema is
checkable at all.  Nothing here runs a cross-compiled binary.

DEPENDED-ON vs MEASURED.  A fact is `depends: true` when `tools/ctwin/
sunfish.c` has a construct whose MEANING changes if the fact changes; each
one carries its witness.  Facts that are merely true are recorded anyway,
because the argument that they are not depended on is itself a claim that
should be re-checkable when the corpus moves.

Python >= 3.9, stdlib only.  Deterministic; a double run is byte-identical.
"""

import argparse
import json
import re
import os
import subprocess
import sys

STD = "-std=c23"

# (id, C constant expression that must hold, depends?, witness / why,
#  Annex J.3 item this is the implementation's answer to)
#
# THE J.3 COLUMN IS THE POINT OF THE PROFILE.  C23 Annex J.3 is the
# standard's own numbered list of implementation-defined behavior; a profile
# fact is this implementation's ANSWER to one of its questions.  Where a fact
# answers no J.3 question the column says so and why — `unsigned_wraps` is
# standard-GUARANTEED (6.3.1.3p2), not implementation-defined, and is recorded
# only so the tier does not refuse it while refusing signed overflow.
FACTS = [
    ("char_bit_8", "CHAR_BIT == 8", True,
     "pos_seal memcpy's the 120-byte board into uint64_t w[15]; 120 bytes is "
     "15 words only if a byte is 8 bits (sunfish.c L199-201)",
     "J.3.5(1) — the number of bits in a byte (3.7)"),
    ("int_32", "sizeof(int) == 4", True,
     "PACK_VM packs (uint32_t)(int) into the high half of a uint64_t and "
     "VM_VAL unpacks it; the move-ordering key is exact only at 32 bits "
     "(L649-652)",
     "J.3.14(1) — the values of the <limits.h>/<stdint.h> macros (5.2.5.3, "
     "7.22).  J.3.6 has no entry for integer SIZES"),
    ("long_64", "sizeof(long) == 8", True,
     "TABLE_SIZE and the node counters are long (L83, L496-497)",
     "J.3.14(1) — as int_32"),
    ("long_long_64", "sizeof(long long) == 8", False,
     "reached only through uint64_t, which <stdint.h> fixes exactly",
     "J.3.14(1) — as int_32"),
    ("pointer_64", "sizeof(void *) == 8", False,
     "no integer<->pointer cast in the corpus (0 sites), so no observable "
     "depends on the width; the model needs it for sizeof only",
     "J.3.8 (Arrays and pointers) — but its entries are about "
     "integer<->pointer conversion, which the corpus never does"),
    ("short_16", "sizeof(short) == 2", False, "unused by the corpus",
     "J.3.14(1) — as int_32"),
    ("twos_complement", "INT_MIN == -INT_MAX - 1", True,
     "C23 6.2.6.2p6 NOTE 2 mandates it; the signed-overflow UB boundary the "
     "tier arms is stated against it.  This is the one place -std=c23 IS "
     "load-bearing for the value model: C17 permitted sign-magnitude and "
     "ones' complement too",
     "NONE — C23 REMOVED it from J.3.  C17's integers list had five entries "
     "and C23's J.3.6 has four; the deleted sign-representation item is the "
     "auditable trace of the two's-complement mandate"),
    ("char_signed", "(char)-1 < 0", True,
     "the board is char b[120] and CLS[(int)p->b[j]] indexes a 128-entry "
     "table by it (L346); every board byte is ASCII < 128, so no VALUE "
     "changes — but the in-bounds ARGUMENT is a function of the sign",
     "J.3.5(5) — which of signed char / unsigned char has the same range, "
     "representation and behavior as plain char (6.2.5, 6.3.1.1)"),
    ("unsigned_wraps", "(unsigned)-1 == UINT_MAX", True,
     "mix64's x *= 0xff51afd7ed558ccdULL is deliberate defined wraparound "
     "(L192-193); standard-guaranteed, recorded because the tier must NOT "
     "refuse it while refusing signed overflow",
     "NONE — this is DEFINED behavior (6.3.1.3p2), not implementation-"
     "defined.  Recorded as a fact so the wrap/refuse split stays checkable"),
    ("int_to_uint32_modulo", "(uint32_t)(-1) == 0xFFFFFFFFu", True,
     "PACK_VM biases a signed val by (uint32_t)(val) ^ 0x80000000u (L649)",
     "NONE — conversion TO an unsigned type is defined modulo (6.3.1.3p2), "
     "and has been since C89"),
    ("uint_to_int_wraps", "(int)0x80000000u == INT_MIN", True,
     "VM_VAL converts the unbiased key back with (int)(... ^ 0x80000000u) "
     "(L652).  CORRECTED at M2 inch 2: this entry previously claimed C23 "
     "6.3.1.3 MANDATES the two's-complement result and that -std=c23 was "
     "load-bearing for it.  It does not.  N3220 6.3.1.3p3 is word-for-word "
     "identical to C11/C17 — 'either the result is implementation-defined or "
     "an implementation-defined signal is raised' — and J.3.6(3) still lists "
     "it.  So this is DEPENDED-ON IMPLEMENTATION-DEFINED behavior, which is "
     "exactly what this profile exists to pin, and the pin is the "
     "measurement below rather than a sentence in the standard",
     "J.3.6(3) — the result of, or the signal raised by, converting an "
     "integer to a signed type when the value cannot be represented "
     "(6.3.1.3p3)"),
    ("little_endian",
     "__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__", False,
     "pos_seal hashes the board THROUGH uint64_t words, so h is "
     "endian-dependent — but h is never observable: pos_eq uses it only as "
     "a fast reject in front of a full memcmp (L209-217) and the bucket "
     "layout it induces is unobservable by the file's own argument "
     "(L403-405).  Measured, deliberately NOT depended on",
     "NONE — byte order is not in J.3; it is a consequence of the "
     "object-representation rules (6.2.6.1) that the standard leaves "
     "unspecified rather than implementation-defined"),
    ("arithmetic_right_shift", "(-1 >> 1) == -1", False,
     "the corpus has ZERO signed right shifts — all 6 >> sites are on "
     "uint64_t (L192-194, L652-653).  Measured so the claim stays checkable",
     "J.3.6(4) — 'the results of some bitwise operations on signed "
     "integers' (6.5.1), a catch-all that does NOT name shifts; the precise "
     "citation is normative 6.5.8p5"),
]

# Facts read off the preprocessor rather than folded.
MACRO_FACTS = ["__STDC_VERSION__", "__CHAR_BIT__", "__SIZEOF_INT__",
               "__SIZEOF_LONG__", "__SIZEOF_POINTER__", "__BYTE_ORDER__",
               "__STDC_IEC_60559_BFP__", "__CHAR_UNSIGNED__"]


def clang(args, stdin=None):
    return subprocess.run(["clang"] + args, capture_output=True, text=True,
                          input=stdin)


def target_args(target):
    return ["-target", target] if target else []


def probe_macros(target):
    out = clang(target_args(target) + [STD, "-dM", "-E", "-x", "c", "-"],
                stdin="")
    if out.returncode != 0:
        sys.exit("c_profile_probe: clang could not preprocess for target %r:\n%s"
                 % (target or "<native>", out.stderr[:1000]))
    seen = {}
    for line in out.stdout.splitlines():
        parts = line.split(None, 2)
        if len(parts) >= 2 and parts[0] == "#define":
            seen[parts[1]] = parts[2] if len(parts) > 2 else ""
    return {m: seen.get(m) for m in MACRO_FACTS}


def probe_fact(target, expr):
    """Decide one constant expression for `target`, by folding it."""
    src = ("#include <limits.h>\n#include <stdint.h>\n"
           "_Static_assert(%s, \"fact\");\n" % expr)
    out = clang(target_args(target) + [STD, "-fsyntax-only", "-x", "c", "-"],
                stdin=src)
    if out.returncode == 0:
        return True
    # A failed _Static_assert is the NEGATIVE answer.  Anything else -- an
    # unknown target, a missing header -- is an instrument fault and must not
    # be reported as "the host differs".
    if "static assertion failed" in out.stderr or "static_assert failed" in out.stderr:
        return False
    sys.exit("c_profile_probe: probing %r for target %r failed for a reason "
             "that is NOT a false assertion; refusing to report it as a "
             "profile difference:\n%s" % (expr, target or "<native>",
                                          out.stderr[:1000]))


def probe(target):
    return {
        "target": target or "<native>",
        "std": STD,
        "macros": probe_macros(target),
        "facts": {f: probe_fact(target, expr) for f, expr, _, _, _ in FACTS},
    }


def build_profile(targets):
    hosts = [probe(t) for t in targets]
    facts = []
    for fid, expr, depends, why, j3 in FACTS:
        holds = {h["target"]: h["facts"][fid] for h in hosts}
        facts.append({"id": fid, "expr": expr, "depended_on": depends,
                      "j3": j3,
                      "why": why, "holds": holds,
                      "agreed": len(set(holds.values())) == 1,
                      "required": all(holds.values())})
    return {"instrument": "harness/c_profile_probe.py", "std": STD,
            "kind": "abstract profile — a schema hosts satisfy, not one "
                    "pinned machine",
            "corpus": "tools/ctwin/sunfish.c (sunfish repo)",
            "corpus_sha256":
                "7d5e0ff8782f804844f383d6f72314dbf948f8e3a26f4033794d6357140b77d7",
            "hosts": hosts, "facts": facts}


def check(profile, target):
    """The #guard: does THIS host satisfy every depended-on fact?"""
    bad = []
    for f in profile["facts"]:
        if not f["depended_on"]:
            continue
        got = probe_fact(target, f["expr"])
        if got != f["required"]:
            bad.append((f["id"], f["expr"], f["required"], got, f["why"]))
    name = target or "<native>"
    if bad:
        print("c_profile_probe: %s FAILS the abstract profile on %d "
              "depended-on fact(s):" % (name, len(bad)))
        for fid, expr, want, got, why in bad:
            print("  %-24s %s  (required %s, host says %s)" % (fid, expr, want, got))
            print("      %s" % why)
        return 1
    n = sum(1 for f in profile["facts"] if f["depended_on"])
    print("c_profile_probe: %s satisfies all %d depended-on facts" % (name, n))
    return 0


LEAN_VALUE = "LeanModels/C/C23/Value.lean"

# Each profile fact, and what it forces the Lean `IntTy` literals to say.
# (fact id, C expression it asserts, [(IntTy def name, signed, bits)])
LEAN_BINDING = [
    ("char_bit_8", "CHAR_BIT == 8", [("char_", None, 8), ("uchar", False, 8)]),
    ("short_16", "sizeof(short) == 2", [("short_", True, 16), ("ushort", False, 16)]),
    ("int_32", "sizeof(int) == 4", [("int_", True, 32), ("uint", False, 32)]),
    ("long_64", "sizeof(long) == 8", [("long_", True, 64), ("ulong", False, 64)]),
    ("char_signed", "(char)-1 < 0", [("char_", True, 8)]),
]


def read_lean_widths(path):
    """Parse `def <name> : IntTy := ⟨<signed>, <bits>⟩` out of the value model.

    Deliberately a PARSE and not an import: the point is to compare the
    committed Lean literals against the committed JSON, with no toolchain in
    the loop, so the check runs anywhere the two files do."""
    try:
        text = open(path, "r", errors="replace").read()
    except OSError as e:
        sys.exit("c_profile_probe --check-lean: cannot read %s: %s" % (path, e))
    found = {}
    for m in re.finditer(
            r"def\s+(\w+)\s*:\s*IntTy\s*:=\s*[\u27e8<]\s*(true|false)\s*,\s*(\d+)\s*[\u27e9>]",
            text):
        found[m.group(1)] = (m.group(2) == "true", int(m.group(3)))
    if not found:
        sys.exit("c_profile_probe --check-lean: parsed ZERO IntTy definitions from "
                 "%s — the check would pass vacuously, which is worse than failing"
                 % path)
    return found


def check_lean(profile, path):
    """THE GAP THIS CLOSES: `--check` gates a HOST against the JSON and never
    reads a Lean file, so the value model's widths were hand-transcribed with
    nothing comparing them to the profile they cite.  This compares them."""
    widths = read_lean_widths(path)
    facts = {f["id"]: f for f in profile["facts"]}
    bad, checked = [], 0
    for fid, expr, bindings in LEAN_BINDING:
        if fid not in facts:
            bad.append("profile has no fact %r, but the Lean widths depend on it" % fid)
            continue
        if not facts[fid].get("required", True):
            continue
        for name, signed, bits in bindings:
            if name not in widths:
                bad.append("%s: no `def %s : IntTy` found" % (fid, name))
                continue
            gotSigned, gotBits = widths[name]
            checked += 1
            if gotBits != bits:
                bad.append("%s (%s) forces %s to %d bits, Lean says %d"
                           % (fid, expr, name, bits, gotBits))
            if signed is not None and gotSigned != signed:
                bad.append("%s (%s) forces %s signed=%s, Lean says %s"
                           % (fid, expr, name, signed, gotSigned))
    if bad:
        print("c_profile_probe --check-lean: %s DISAGREES with the profile on "
              "%d point(s):" % (path, len(bad)))
        for b in bad:
            print("  " + b)
        return 1
    print("c_profile_probe --check-lean: %s agrees with the profile on all %d "
          "width/signedness points (%d IntTy defs parsed)"
          % (path, checked, len(widths)))
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--target", action="append", default=[],
                    help="a clang target triple; repeatable. Default: native")
    ap.add_argument("-o", "--output", help="write the profile JSON here")
    ap.add_argument("--check", metavar="JSON",
                    help="gate a host against an existing profile")
    ap.add_argument("--check-lean", metavar="JSON", dest="check_lean",
                    help="gate the Lean value model's IntTy literals against the profile")
    args = ap.parse_args()

    if args.check_lean:
        with open(args.check_lean) as fh:
            return check_lean(json.load(fh), LEAN_VALUE)

    if args.check:
        with open(args.check) as fh:
            profile = json.load(fh)
        return check(profile, args.target[0] if args.target else None)

    profile = build_profile(args.target or [None])
    text = json.dumps(profile, indent=2, sort_keys=True) + "\n"
    if args.output:
        with open(args.output, "w") as fh:
            fh.write(text)
        dis = [f["id"] for f in profile["facts"] if not f["agreed"]]
        print("wrote %s (%d hosts, %d facts, %d depended-on)"
              % (args.output, len(profile["hosts"]), len(profile["facts"]),
                 sum(1 for f in profile["facts"] if f["depended_on"])))
        if dis:
            print("HOSTS DISAGREE on: %s" % ", ".join(dis))
        else:
            print("all hosts agree on every fact")
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
