/-
Examples/rsa_inverse — three-file example layout (see Examples/tri/spec.lean
for the pattern rationale): rsa_inverse.py (vendored BYTE-VERBATIM from the
python-rsa package — provenance in its module docstring), rsa_inverse.json
(generated envelope), THIS FILE (statements, `:= by proofs`), proof.lean
(the real proofs, namespace `Examples.rsa_inverse.proof`).

REAL-WORLD TARGET: `rsa.common.extended_gcd` / `rsa.common.inverse` from
python-rsa 4.9.1 (rsa/common.py, sha256
c3452e5791cdbe4142e2c04c8cc0cef094d4242a17bec2f372826b02eab32e90).

Tier facts (envelope, extractor run 2026-07-21):
* `extended_gcd(a, b)` — fully in-tier, zero Unsupported nodes;
  `args_unsupported`/`locals_unsupported` both null. Node kinds: Assign
  (incl. tuple-unpack `(a, b) = (b, a % b)`), AugAssign:Add,
  BinOp FloorDiv/Mod/Mult/Sub, Compare Lt/NotEq, Constant, Expr
  (docstring), If, Name, Return, Tuple, While.
* `inverse(x, n)` — in-tier except EXACTLY ONE Unsupported node: the
  `raise NotRelativePrimeError(x, n, divider)` statement (rsa_inverse.py
  line 71). The coming proof covers precisely that node with an
  unreachability argument (coprime inputs ⇒ divider = 1 ⇒ the `if` guard
  is false). The `#guard … matches .unsupported` line below documents the
  edge: NON-coprime input does reach the raise, loudly.

Authenticity: every expected value below was computed with Python 3.9.25
against the vendored file AND against the installed rsa==4.9.1 package
(pip, 2026-07-21) — both agree: inverse(3, 7) = 5, inverse(7, 40) = 23,
inverse(17, 3120) = 2753, extended_gcd(12, 18) = (6, 17, 1),
extended_gcd(270, 192) = (6, 5, 263).

Theorem statements land in the next phase; this stub is load + non-vacuity.
-/
import Examples.rsa_inverse.proof

open LeanModels LeanModels.Python

load_program rsa_inverse from "Examples/rsa_inverse/rsa_inverse.json"

/-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
Surface.lean — fixed generous fuel; minimal-fuel pinning retired). -/
#py_check rsa_inverse.inverse(3, 7) = 5
#py_check rsa_inverse.inverse(7, 40) = 23
#py_check rsa_inverse.inverse(17, 3120) = 2753
#py_check rsa_inverse.inverse(1, 2) = 1
#py_check rsa_inverse.inverse(41, 7) = 6
#py_check rsa_inverse.extended_gcd(12, 18) =
    (Val.tuple #[.int 6, .int 17, .int 1])
#py_check rsa_inverse.extended_gcd(270, 192) =
    (Val.tuple #[.int 6, .int 5, .int 263])
#py_check rsa_inverse.extended_gcd(5, 0) =
    (Val.tuple #[.int 5, .int 1, .int 0])

/-! Tier-edge documentation: a NON-coprime `inverse` call reaches the
vendored `raise NotRelativePrimeError(…)` — the single Unsupported node —
and the interpreter refuses loudly (`.unsupported`, not a Python result),
so the check stays a raw `#guard … matches`. -/
#guard (callFunction rsa_inverse "inverse" #[.int 4, .int 6] 4096 matches .unsupported _)
