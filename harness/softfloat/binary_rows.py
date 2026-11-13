#!/usr/bin/env python3
"""binary_rows.py -- the differential rows of LeanModels/SoftFloat/Binary/Tests.lean.

    python3 harness/softfloat/binary_rows.py --write LeanModels/SoftFloat/Binary/Tests.lean
    python3 harness/softfloat/binary_rows.py --check LeanModels/SoftFloat/Binary/Tests.lean

Every row is a value of the binary-format library at binary16 or binary32 (`decode`, `classify`, the encoders,
`divide` under all five rounding-direction attributes) against a value computed HERE, by one of three sources, named
on the row's comment block:

  struct   CPython's `struct` packing/unpacking ('<e' binary16, '<f' binary32), the exact value read as a
           `fractions.Fraction`;
  hw       the host FPU's binary32 division through numpy (numpy float32 arrays), its rounding direction set with
           C `fesetround` (roundTiesToEven, roundTowardPositive, roundTowardNegative, roundTowardZero); binary16
           division through numpy float16 (a binary32 hardware quotient rounded to binary16 by numpy, ties to even:
           correctly rounded, since 24 >= 2 * 11 + 2) and, independently, through CPython (a binary64 quotient packed
           by struct '<e'); for roundTiesToEven at binary16 both must agree;
  ref      `Ref` below: an exact `fractions.Fraction` model of §4.3/§7.4 written for these rows. It is checked against
           `hw` on every row where `hw` exists (the script stops on a disagreement), and is the ONLY source of the
           roundTiesToAway rows (no host facility rounds to nearest, ties away, in arithmetic) and of binary16 under
           the three directed attributes: for those rows NO ORACLE RESULT IS CLAIMED.

A NaN result is the library's canonical quiet NaN (a policy: §6.2.3 says a NaN result *should* carry an input
payload); the row only claims that the host's result is a NaN too (asserted here). The quiet/signaling class of a
NaN pattern is §6.2.1's encoding (the first trailing-significand bit), a definition: no oracle result is claimed.

`--check` regenerates the file and fails when it differs; it needs the same Python, numpy and machine kind as the
header records (the oracle versions are printed into the file). Deterministic: the random operands come from a fixed
seed. Needs numpy (Homebrew's python3.12 has it); stdlib otherwise.
"""
import ctypes
import math
import platform
import random
import struct
import sys
import warnings
from fractions import Fraction as Fr

import numpy as np

warnings.simplefilter("ignore")

MODES = ["nearestTiesToEven", "nearestTiesToAway", "towardPositive", "towardNegative", "towardZero"]
FE_BITS = {"nearestTiesToEven": 0x0, "towardPositive": 0x00400000, "towardNegative": 0x00800000,
           "towardZero": 0x00C00000}   # AArch64 FPCR.RMode, the values of <fenv.h> on this machine kind


class Fmt:
    def __init__(self, name, w, p, code):
        self.name, self.w, self.p, self.code = name, w, p, code
        self.t = p - 1
        self.k = 1 + w + self.t
        self.emax = 2 ** (w - 1) - 1
        self.emin = 1 - self.emax
        self.qmin = self.emin - self.t
        self.max_units = (2 ** p - 1) * 2 ** (2 * self.emax - 1)

    def lit(self, x):
        return f"0x{x:0{self.k // 4}X}#{self.k}"


B16 = Fmt("binary16", 5, 11, "e")
B32 = Fmt("binary32", 8, 24, "f")


class Ref:
    """Exact model: decode (§3.4), round an exact nonzero rational (§4.3, §7.4, §7.5), divide (§5.4.1, §6, §7)."""

    @staticmethod
    def fields(f, x):
        return x >> (f.w + f.t), (x >> f.t) & (2 ** f.w - 1), x & (2 ** f.t - 1)

    @staticmethod
    def decode(f, x):
        s, e, t = Ref.fields(f, x)
        if e == 2 ** f.w - 1:
            return ("nan", t < 2 ** (f.t - 1)) if t else ("inf", s == 1)
        if e == 0:
            return ("zero", s == 1) if t == 0 else ("fin", s == 1, Fr(t) * Fr(2) ** f.qmin)
        return ("fin", s == 1, Fr(2 ** f.t + t) * Fr(2) ** (f.qmin + e - 1))

    @staticmethod
    def pack(f, neg, e, t):
        return (1 if neg else 0) << (f.w + f.t) | e << f.t | t

    @staticmethod
    def encode_units(f, neg, u):
        if u < 2 ** f.t:
            return Ref.pack(f, neg, 0, u)
        j = u.bit_length() - 1 - f.t
        return Ref.pack(f, neg, j + 1, u // 2 ** j - 2 ** f.t)

    @staticmethod
    def round(f, mode, neg, v):
        u = v / Fr(2) ** f.qmin          # the exact magnitude in units
        n = math.floor(u)
        j = max(0, n.bit_length() - f.p) if n > 0 else 0
        c = math.floor(u / 2 ** j)
        r = u / 2 ** j - c
        up = {"nearestTiesToEven": r > Fr(1, 2) or (r == Fr(1, 2) and c % 2 == 1),
              "nearestTiesToAway": r >= Fr(1, 2),
              "towardPositive": r != 0 and not neg,
              "towardNegative": r != 0 and neg,
              "towardZero": False}[mode]
        res = (c + (1 if up else 0)) * 2 ** j
        if res <= f.max_units:
            return Ref.encode_units(f, neg, res)
        to_inf = {"nearestTiesToEven": True, "nearestTiesToAway": True, "towardZero": False,
                  "towardPositive": not neg, "towardNegative": neg}[mode]
        return Ref.pack(f, neg, 2 ** f.w - 1, 0) if to_inf else Ref.encode_units(f, neg, f.max_units)

    @staticmethod
    def divide(f, mode, a, b):
        da, db = Ref.decode(f, a), Ref.decode(f, b)
        nan = Ref.pack(f, False, 2 ** f.w - 1, 2 ** (f.t - 1))
        if da[0] == "nan" or db[0] == "nan" or (da[0] == db[0] and da[0] in ("inf", "zero")):
            return nan
        s = da[1] != db[1]
        if da[0] == "inf" or db[0] == "zero":
            return Ref.pack(f, s, 2 ** f.w - 1, 0)
        if db[0] == "inf" or da[0] == "zero":
            return Ref.pack(f, s, 0, 0)
        return Ref.round(f, mode, s, da[2] / db[2])


def struct_value(f, x):
    return struct.unpack("<" + f.code, x.to_bytes(f.k // 8, "little"))[0]


def struct_bits(f, v):
    try:
        return int.from_bytes(struct.pack("<" + f.code, v), "little")
    except OverflowError:
        return None


LIBC = ctypes.CDLL(None)


def hw_divide(f, mode, a, b):
    """The host's quotient bits, or None where the host has no such rounding."""
    if f is B32:
        if mode not in FE_BITS:
            return None
        x = np.array([a], dtype=np.uint32).view(np.float32)
        y = np.array([b], dtype=np.uint32).view(np.float32)
        LIBC.fesetround(FE_BITS[mode])
        try:
            q = x / y
        finally:
            LIBC.fesetround(0)
        return int(q.view(np.uint32)[0])
    if mode != "nearestTiesToEven":
        return None
    x = np.array([a], dtype=np.uint16).view(np.float16)
    y = np.array([b], dtype=np.uint16).view(np.float16)
    q16 = int((x / y).view(np.uint16)[0])
    # independently: a binary64 quotient (CPython) packed by struct '<e'
    va, vb = struct_value(f, a), struct_value(f, b)
    if math.isnan(va) or math.isnan(vb) or vb == 0 or (math.isinf(va) and math.isinf(vb)):
        return q16
    q = va / vb
    sb = struct_bits(f, q)
    if sb is None:  # struct refuses a value that rounds past the largest finite: the result is an infinity
        sb = Ref.pack(f, q < 0, 2 ** f.w - 1, 0)
    assert sb == q16, (f.name, hex(a), hex(b), hex(sb), hex(q16))
    return q16


def is_nan_bits(f, x):
    return Ref.decode(f, x)[0] == "nan"


SPECIAL16 = [0x0000, 0x8000, 0x0001, 0x03FF, 0x0400, 0x3800, 0x3C00, 0xBC00, 0x4200, 0x3555, 0x7BFF, 0xFBFF,
             0x7C00, 0xFC00, 0x7E00, 0x7C01, 0xFE01]
SPECIAL32 = [0x00000000, 0x80000000, 0x00000001, 0x007FFFFF, 0x00800000, 0x3F000000, 0x3F800000, 0xBF800000,
             0x40400000, 0x3EAAAAAB, 0x7F7FFFFF, 0xFF7FFFFF, 0x7F800000, 0xFF800000, 0x7FC00000, 0x7F800001,
             0xFFC00001]
# rounding-sensitive pairs: ties in the subnormal range, the overflow threshold, gradual underflow
TARGET16 = [(0x0001, 0x4000), (0x0003, 0x4000), (0x0005, 0x4000), (0x0001, 0x3FFF), (0x8001, 0x4400),
            (0x03FF, 0x3BFE), (0x0400, 0x4000), (0x7BFF, 0x3BFF), (0x7BFF, 0x3800), (0xFBFF, 0x3800),
            (0x7BFE, 0x3BFF), (0x0001, 0x7BFF), (0x3C00, 0x4200), (0xBC00, 0x4200), (0x4000, 0x4200)]
TARGET32 = [(0x00000001, 0x40000000), (0x00000003, 0x40000000), (0x00000005, 0x40000000),
            (0x80000001, 0x40800000), (0x00800000, 0x40000000), (0x7F7FFFFF, 0x3F000000),
            (0x7F7FFFFF, 0x3F7FFFFF), (0xFF7FFFFF, 0x3F000000), (0x00000001, 0x7F7FFFFF),
            (0x3F800000, 0x40400000), (0xBF800000, 0x40400000), (0x40000000, 0x40400000)]
DIRECTED16 = [0x0001, 0x0003, 0x3C00, 0xBC00, 0x4200, 0x7BFF, 0x3800, 0xB555]
DIRECTED32 = [0x00000001, 0x00000003, 0x3F800000, 0xBF800000, 0x40400000, 0x7F7FFFFF, 0x3F000000, 0xBEAAAAAB]
# exact decide rows (kernel), a few of each kind: (format, attribute, a, b)
DECIDE = {("binary16", "nearestTiesToEven", 0x3C00, 0x4200), ("binary16", "nearestTiesToEven", 0x0003, 0x4000),
          ("binary16", "nearestTiesToEven", 0x0000, 0x0000), ("binary16", "nearestTiesToEven", 0x7BFF, 0x3BFF),
          ("binary16", "nearestTiesToEven", 0x0001, 0x3FFF), ("binary16", "nearestTiesToEven", 0x7C01, 0x3C00),
          ("binary32", "nearestTiesToEven", 0x3F800000, 0x40400000),
          ("binary32", "nearestTiesToEven", 0x00000001, 0x40000000),
          ("binary32", "nearestTiesToEven", 0x7F7FFFFF, 0x3F000000),
          ("binary16", "nearestTiesToAway", 0x0005, 0x4000), ("binary16", "towardZero", 0x7BFF, 0x3800),
          ("binary32", "towardZero", 0x3F800000, 0x40400000), ("binary32", "towardPositive", 0x3F800000, 0x40400000),
          ("binary32", "towardNegative", 0xBF800000, 0x40400000), ("binary32", "towardZero", 0x7F7FFFFF, 0x3F000000),
          ("binary32", "towardNegative", 0x7F7FFFFF, 0x3F000000), ("binary32", "nearestTiesToAway", 0x00000001, 0x40000000)}
DECIDE_DECODE = {("binary16", 0x0001), ("binary16", 0x7C01), ("binary16", 0xFBFF), ("binary32", 0x00800000),
                 ("binary32", 0x7FA00000)}


def random_finite(f, rng, n):
    out = []
    while len(out) < n:
        x = rng.randrange(2 ** f.k)
        if Ref.decode(f, x)[0] in ("fin", "zero"):
            out.append(x)
    return out


def mode_name(m):
    return "." + m


def generate():
    rng = random.Random(20261113)
    L = []
    L.append("import LeanModels.SoftFloat.Binary.Characterization")
    L.append("")
    L.append("/-!")
    L.append("# Differential rows: the library at binary16 and binary32")
    L.append("")
    L.append("GENERATED by `harness/softfloat/binary_rows.py` (do not edit; regenerate with `--write`, verify with")
    L.append("`--check`). Sources (the script's docstring defines them): `struct` and `hw` are oracle results of")
    L.append(f"this host -- Python {platform.python_version()}, numpy {np.__version__}, {platform.machine()} "
             f"{platform.system()}; `ref` is the script's exact")
    L.append("`fractions.Fraction` model, checked against `hw` wherever `hw` exists, and the only source of the")
    L.append("roundTiesToAway rows and the binary16 directed rows: for those, NO ORACLE RESULT IS CLAIMED. A NaN")
    L.append("result is the canonical quiet NaN (the library's policy); the host's result was a NaN on every such row.")
    L.append("Each row is a `#guard` (compiled evaluation); the `example … := by decide` rows are checked by the")
    L.append("kernel.")
    L.append("-/")
    L.append("")
    L.append("namespace LeanModels.SoftFloat.Binary.Tests")
    L.append("")
    L.append("open LeanModels.SoftFloat.Binary")
    L.append("")
    L.append("/-- `(decode f x).value?` is the fraction `n / d` (compared by cross-multiplication). -/")
    L.append("def valueIs (f : Format) (x : BitVec f.k) (n : Int) (d : Nat) : Bool :=")
    L.append("  match (decode f x).value? with")
    L.append("  | some (a, b) => a * d == n * b")
    L.append("  | none => false")
    L.append("")
    counts = {}

    def bump(k, n=1):
        counts[k] = counts.get(k, 0) + n

    for f, pats in ((B16, SPECIAL16 + [0x7D00, 0x7FFF, 0x0200, 0xB555]),
                    (B32, SPECIAL32 + [0x7FA00000, 0xFFFFFFFF, 0x00400000, 0xBEAAAAAB])):
        L.append(f"/-! ## {f.name}: decode, exact value and class (source: struct; NaN class: §6.2.1, no oracle) -/")
        L.append("")
        for x in pats:
            v = struct_value(f, x)
            d = Ref.decode(f, x)
            if math.isnan(v):
                assert d[0] == "nan"
                cls = ".signalingNaN" if d[1] else ".quietNaN"
                L.append(f"#guard classify {f.name} {f.lit(x)} == {cls} && (decode {f.name} {f.lit(x)}).value? == none")
            elif math.isinf(v):
                cls = ".negativeInfinity" if v < 0 else ".positiveInfinity"
                L.append(f"#guard classify {f.name} {f.lit(x)} == {cls} && (decode {f.name} {f.lit(x)}).value? == none")
            else:
                q = Fr(v)
                assert d[0] in ("fin", "zero") and (d[0] == "zero" or d[2] * (-1 if d[1] else 1) == q)
                neg = math.copysign(1.0, v) < 0
                if v == 0:
                    cls = ".negativeZero" if neg else ".positiveZero"
                elif abs(q) < Fr(2) ** f.emin:
                    cls = ".negativeSubnormal" if neg else ".positiveSubnormal"
                else:
                    cls = ".negativeNormal" if neg else ".positiveNormal"
                L.append(f"#guard classify {f.name} {f.lit(x)} == {cls} && "
                         f"valueIs {f.name} {f.lit(x)} ({q.numerator}) {q.denominator}")
            bump("decode")
            if (f.name, x) in DECIDE_DECODE:
                L.append("example : (" + L[-1][len("#guard "):] + ") = true := by decide")
                bump("decide")
        L.append("")
        L.append(f"/-! ## {f.name}: the encoders (source: struct) -/")
        L.append("")
        inf, ninf = struct_bits(f, math.inf), struct_bits(f, -math.inf)
        z, nz = struct_bits(f, 0.0), struct_bits(f, -0.0)
        L.append(f"#guard infinity {f.name} false = {f.lit(inf)} && infinity {f.name} true = {f.lit(ninf)}")
        L.append(f"#guard zero {f.name} false = {f.lit(z)} && zero {f.name} true = {f.lit(nz)}")
        qn = struct_bits(f, math.nan)
        assert Ref.decode(f, qn) == ("nan", False)
        L.append(f"#guard canonicalNaN {f.name} = {f.lit(Ref.pack(f, False, 2 ** f.w - 1, 2 ** (f.t - 1)))}"
                 f"  -- struct packs a quiet NaN as {f.lit(qn)}")
        bump("encode", 3)
        for u in [1, 2 ** f.t - 1, 2 ** f.t, 2 ** f.p - 1, 2 ** f.p, 3 * 2 ** f.p, f.max_units]:
            for neg in (False, True):
                v = float(Fr(u) * Fr(2) ** f.qmin) * (-1 if neg else 1)
                L.append(f"#guard finite {f.name} {'true' if neg else 'false'} {u} = {f.lit(struct_bits(f, v))}")
                bump("encode")
        L.append("")

    def div_rows(f, mode, pairs, title):
        L.append(f"/-! ## {f.name} division, {mode}: {title} -/")
        L.append("")
        for a, b in pairs:
            ref = Ref.divide(f, mode, a, b)
            hw = hw_divide(f, mode, a, b)
            if hw is not None:
                if is_nan_bits(f, hw):
                    assert is_nan_bits(f, ref), (f.name, mode, hex(a), hex(b))
                else:
                    assert hw == ref, (f.name, mode, hex(a), hex(b), hex(hw), hex(ref))
                bump(f"divide {f.name} {mode} (hw)")
            else:
                bump(f"divide {f.name} {mode} (ref only)")
            row = f"divide {f.name} {mode_name(mode)} {f.lit(a)} {f.lit(b)} = {f.lit(ref)}"
            L.append("#guard " + row)
            if (f.name, mode, a, b) in DECIDE:
                L.append("example : " + row + " := by decide")
                bump("decide")
        L.append("")

    for f, sp, tg, dr in ((B16, SPECIAL16, TARGET16, DIRECTED16), (B32, SPECIAL32, TARGET32, DIRECTED32)):
        src = "hw (numpy float16 and CPython binary64 + struct, which agree)" if f is B16 else "hw (binary32 FPU)"
        div_rows(f, "nearestTiesToEven", [(a, b) for a in sp for b in sp],
                 f"every pair of {len(sp)} special and ordinary operands (source: {src})")
        div_rows(f, "nearestTiesToEven", tg + list(zip(random_finite(f, rng, 30), random_finite(f, rng, 30))),
                 f"ties, the overflow threshold, gradual underflow, 30 random pairs (source: {src})")
        for mode in ["towardPositive", "towardNegative", "towardZero", "nearestTiesToAway"]:
            if f is B32 and mode in FE_BITS:
                src2 = "hw (binary32 FPU under fesetround)"
            else:
                src2 = "ref only: no oracle result is claimed"
            div_rows(f, mode, [(a, b) for a in dr for b in dr] + tg, f"(source: {src2})")
    L.append("end LeanModels.SoftFloat.Binary.Tests")
    return "\n".join(L) + "\n", counts


def main(argv):
    text, counts = generate()
    if len(argv) == 2 and argv[0] == "--write":
        open(argv[1], "w", encoding="utf-8").write(text)
    elif len(argv) == 2 and argv[0] == "--check":
        old = open(argv[1], encoding="utf-8").read()
        if old != text:
            print(f"binary_rows: {argv[1]} differs from the regenerated rows")
            return 1
    else:
        print(__doc__)
        return 2
    total = sum(counts.values())
    for k in sorted(counts):
        print(f"{counts[k]:5d}  {k}")
    print(f"{total:5d}  rows (python {platform.python_version()}, numpy {np.__version__}, {platform.machine()})")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
