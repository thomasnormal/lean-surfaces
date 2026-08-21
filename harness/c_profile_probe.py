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
import os
import subprocess
import sys

STD = "-std=c23"

# (id, C constant expression that must hold, depends?, witness / why)
FACTS = [
    ("char_bit_8", "CHAR_BIT == 8", True,
     "pos_seal memcpy's the 120-byte board into uint64_t w[15]; 120 bytes is "
     "15 words only if a byte is 8 bits (sunfish.c L199-201)"),
    ("int_32", "sizeof(int) == 4", True,
     "PACK_VM packs (uint32_t)(int) into the high half of a uint64_t and "
     "VM_VAL unpacks it; the move-ordering key is exact only at 32 bits "
     "(L649-652)"),
    ("long_64", "sizeof(long) == 8", True,
     "TABLE_SIZE and the node counters are long (L83, L496-497)"),
    ("long_long_64", "sizeof(long long) == 8", False,
     "reached only through uint64_t, which <stdint.h> fixes exactly"),
    ("pointer_64", "sizeof(void *) == 8", False,
     "no integer<->pointer cast in the corpus (0 sites), so no observable "
     "depends on the width; the model needs it for sizeof only"),
    ("short_16", "sizeof(short) == 2", False, "unused by the corpus"),
    ("twos_complement", "INT_MIN == -INT_MAX - 1", True,
     "C23 6.2.6.2 mandates it; the signed-overflow UB boundary the tier "
     "arms is stated against it"),
    ("char_signed", "(char)-1 < 0", True,
     "the board is char b[120] and CLS[(int)p->b[j]] indexes a 128-entry "
     "table by it (L346); every board byte is ASCII < 128, so no VALUE "
     "changes — but the in-bounds ARGUMENT is a function of the sign"),
    ("unsigned_wraps", "(unsigned)-1 == UINT_MAX", True,
     "mix64's x *= 0xff51afd7ed558ccdULL is deliberate defined wraparound "
     "(L192-193); standard-guaranteed, recorded because the tier must NOT "
     "refuse it while refusing signed overflow"),
    ("int_to_uint32_modulo", "(uint32_t)(-1) == 0xFFFFFFFFu", True,
     "PACK_VM biases a signed val by (uint32_t)(val) ^ 0x80000000u (L649)"),
    ("uint_to_int_wraps", "(int)0x80000000u == INT_MIN", True,
     "VM_VAL converts the unbiased key back with (int)(... ^ 0x80000000u) "
     "(L652).  C23 6.3.1.3 MANDATES the two's-complement result; under C17 "
     "this was implementation-defined, so the -std=c23 pin is load-bearing "
     "for the move ordering, not a formality"),
    ("little_endian",
     "__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__", False,
     "pos_seal hashes the board THROUGH uint64_t words, so h is "
     "endian-dependent — but h is never observable: pos_eq uses it only as "
     "a fast reject in front of a full memcmp (L209-217) and the bucket "
     "layout it induces is unobservable by the file's own argument "
     "(L403-405).  Measured, deliberately NOT depended on"),
    ("arithmetic_right_shift", "(-1 >> 1) == -1", False,
     "the corpus has ZERO signed right shifts — all 6 >> sites are on "
     "uint64_t (L192-194, L652-653).  Measured so the claim stays checkable"),
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
        "facts": {f: probe_fact(target, expr) for f, expr, _, _ in FACTS},
    }


def build_profile(targets):
    hosts = [probe(t) for t in targets]
    facts = []
    for fid, expr, depends, why in FACTS:
        holds = {h["target"]: h["facts"][fid] for h in hosts}
        facts.append({"id": fid, "expr": expr, "depended_on": depends,
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


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--target", action="append", default=[],
                    help="a clang target triple; repeatable. Default: native")
    ap.add_argument("-o", "--output", help="write the profile JSON here")
    ap.add_argument("--check", metavar="JSON",
                    help="gate a host against an existing profile")
    args = ap.parse_args()

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
