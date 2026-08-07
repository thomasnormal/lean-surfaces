/-
Examples/python/sf_pst — three-file example layout. The H1-proper sunfish
acceptance example (sunfish ladder step 3, docs/backlog.md): the REAL
`piece` and `pst` tables and the REAL defining expressions
`MATE_LOWER = piece["K"] - 10 * piece["Q"]` /
`MATE_UPPER = piece["K"] + 10 * piece["Q"]`, copied verbatim from
sunfish.py and evaluated through the dict tier — module-level dict
literals allocated by the G1 world-init pass, subscript reads through the
heap, `in` membership, and the pst tuple-of-int rows indexed behind a
dict read. `sf_consts`'s recorded gap ("MATE_UPPER carries the value but
not its defining expression") closes here.

NOT in this module: sunfish's pst padding loop (`.items()`, a lambda,
`sum` over a generator — loudly out of tier), so `pst` is the raw
pre-padding literal; the padded table lands with that construct tier.

The theorems are CONCRETE (kernel-witnessed runs of the real tables —
values cross-checked against CPython in harness/cases.json); symbolic
dict-read theorems await walker support for heap reads.
-/
import Examples.python.sf_pst.proof

open LeanModels LeanModels.Python

load_program sf_pst from "Examples/python/sf_pst/sf_pst.json"

/-! Non-vacuity: concrete runs (values cross-checked against CPython). -/
#py_check sf_pst.mate_bounds() = (Val.tuple #[.int 50710, .int 69290])
#py_check sf_pst.piece_val("K") = 60000
#py_check sf_pst.piece_val("Q") = 929
#py_check sf_pst.pst_entry("K", 0) = 4
#py_check sf_pst.pst_entry("P", 9) = 83
#py_check sf_pst.pst_entry("Q", 3) = -104
#py_check sf_pst.in_piece("K") = true
#py_check sf_pst.in_piece("x") = false
#py_check sf_pst.piece_val("p") raises .keyError
#py_check sf_pst.score_gain("N", "Q", 30, 51) = 904
#py_check sf_pst.score_gain("P", "", 9, 17) = -54

/-- Sunfish's mate window, from its REAL defining expressions:
`piece["K"] ∓ 10 * piece["Q"]` through the module-global dict. -/
theorem mate_bounds_spec :
    sf_pst.mate_bounds() ==> (Val.tuple #[.int 50710, .int 69290]) := by proofs

/-- `piece["K"]` — the king's material value, read from the real table. -/
theorem piece_val_K : sf_pst.piece_val("K") ==> (60000 : PyInt) := by proofs

/-- `pst["K"][0]` — a real piece-square read: dict lookup, then tuple
index. -/
theorem pst_entry_K0 : sf_pst.pst_entry("K", 0) ==> (4 : PyInt) := by proofs

/-- The capture-scoring shape of sunfish's `value()`: two pst reads and a
piece read, at real table values. -/
theorem score_gain_NQ :
    sf_pst.score_gain("N", "Q", 30, 51) ==> (904 : PyInt) := by proofs

/-- A missing key is the faithful `KeyError` — on the real table. -/
theorem piece_val_missing : sf_pst.piece_val("p") ==>! .keyError := by proofs
