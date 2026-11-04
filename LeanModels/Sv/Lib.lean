import LeanModels.Sv.Lib.NatArith
import LeanModels.Sv.Lib.XFVal
import LeanModels.Sv.Lib.RowMajor
import LeanModels.Sv.Lib.Restoring
import LeanModels.Sv.Lib.Newton

/-!
# `LeanModels.Sv.Lib`: a proof library for word-level `sv_comb` proofs

Task-independent lemmas that carry the equations `sv_equations` prints (bit functions, the word-level helpers of
`CombKnownBits.lean` / `CombWord.lean`, row-major offsets of generate families) into `Nat` arithmetic:

* `Lib/NatArith.lean` (`LeanModels.Sv.Lib`): `Nat` facts (scaled comparisons, products of powers of two, modular
  decrements, bands of a remainder, the top bit of a bounded value). Imports nothing.
* `Lib/XFVal.lean` (`LeanModels.Sv.XF`): the `Nat` value of the word-level helpers (`XF.val` of windows,
  concatenations, extensions, constants, shifts, `addBits`/`subBits`; `XF.any`/`XF.all`/`XF.eqv` as value tests).
* `Lib/RowMajor.lean` (`LeanModels.Sv.Lib`): `CombView.rmN` at natural coordinates.
* `Lib/Restoring.lean` (`LeanModels.Sv.Lib`): restoring division (`restRem`, `restQuo`, `restore_spec`) and the value
  of its quotient-bit row (`val_restQuo`).
* `Lib/Newton.lean` (`LeanModels.Sv.Lib`): Newton-Raphson division as its hardware computes it (`nwIter`, `nwQf`,
  `nwRm`, `nwQQ`, `nwRnz`), the error analysis, and `newton_div`/`newton_rest`: after `K ≥ 1` steps with
  `P + 2 ≤ 2^(K+2)` the corrected quotient and sticky are those of restoring division; `nwNI_spec` for
  `K = $clog2((P + 9) / 8) + 1`.

No Mathlib: Init, Std and `LeanModels.Sv` modules only (`Lib/Newton.lean` imports `LeanModels.Sv.Param` for
`clog2`), so svGolf solutions import it at no build cost beyond the modules themselves (the checker builds imported
`LeanModels.Sv.*` modules in its trusted stage).
-/
