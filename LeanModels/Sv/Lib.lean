import LeanModels.Sv.Lib.NatArith
import LeanModels.Sv.Lib.BitVecArith
import LeanModels.Sv.Lib.XFVal
import LeanModels.Sv.Lib.RowMajor
import LeanModels.Sv.Lib.Restoring

/-!
# `LeanModels.Sv.Lib`: a proof library for word-level `sv_comb` proofs

Task-independent lemmas that carry the equations `sv_equations` prints (bit functions, the word-level helpers of
`CombKnownBits.lean` / `CombWord.lean`, row-major offsets of generate families) into `Nat` arithmetic, and the
arithmetic of register-transfer proofs:

* `Lib/NatArith.lean` (`LeanModels.Sv.Lib`): `Nat` facts (scaled comparisons, products of powers, modular
  subtraction and decrements, bands of a remainder, the top bit of a bounded value; the `Int` labels of row-major
  windows). Imports nothing.
* `Lib/BitVecArith.lean` (`LeanModels.Sv.Lib`): `BitVec` facts of datapaths (sign extension truncated back, a
  multiply-accumulate at a wider width, a part select of a shift, a counter at its last value). Imports nothing.
* `Lib/XFVal.lean` (`LeanModels.Sv.XF`): the `Nat` value of the word-level helpers (`XF.val` of windows,
  concatenations, extensions, constants, shifts, `addBits`/`subBits`; `XF.any`/`XF.all`/`XF.eqv` as value tests; a
  carry-save adder row, `val_csa`, and an XOR with the top-bit constant, `val_xor_top`).
* `Lib/RowMajor.lean` (`LeanModels.Sv.Lib`): `CombView.rmN` at natural coordinates (`rmN_row0`, `rmN_succ0`,
  `rmN_last_col`, `rmN_eq`).
* `Lib/Restoring.lean` (`LeanModels.Sv.Lib`): restoring division (`restRem`, `restQuo`, `restore_inv`,
  `restore_spec`) and the value of its quotient-bit row (`val_restQuo`).

What belongs here: results that any proof of a class of designs would use. A model of one design's datapath
belongs to that design's proof, which is compiled (and timed) with it: the Newton-Raphson core of svGolf's
`fdivp_newton` reference, `Lib/Newton.lean` until 2026-11-04, is now that reference's section `NwCore` (decided
11/04: code prebuilt here is time a golfer's own equivalent code would not get).

No Mathlib: Init, Std and `LeanModels.Sv` modules only, so svGolf solutions import it at no build cost beyond the
modules themselves (the checker builds imported `LeanModels.Sv.*` modules in its trusted stage).
-/
