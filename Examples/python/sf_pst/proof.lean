/-
Proof module for `Examples/python/sf_pst/spec.lean` (three-file example
layout). The statements are concrete runs of sunfish's real tables, so
every proof is a kernel-witnessed evaluation at the fixed generous fuel —
`CallsTo.intro 4096 (by rfl)` (resp. the `Raises` witness): the whole
module init (six pst dict entries of 64-int tuples, the piece table, the
MATE window arithmetic) reduces inside the kernel. Symbolic dict-read
theorems await walker support for heap reads (recorded in AGENTS.md).
-/
import LeanModels

namespace Examples.python.sf_pst.proof

open LeanModels LeanModels.Python

load_program sf_pst from "Examples/python/sf_pst/sf_pst.json"

theorem mate_bounds_spec :
    sf_pst.mate_bounds() ==> (Val.tuple #[.int 50710, .int 69290]) :=
  CallsTo.intro 4096 (by rfl)

theorem piece_val_K : sf_pst.piece_val("K") ==> (60000 : PyInt) :=
  CallsTo.intro 4096 (by rfl)

theorem pst_entry_K0 : sf_pst.pst_entry("K", 0) ==> (4 : PyInt) :=
  CallsTo.intro 4096 (by rfl)

theorem score_gain_NQ :
    sf_pst.score_gain("N", "Q", 30, 51) ==> (904 : PyInt) :=
  CallsTo.intro 4096 (by rfl)

theorem piece_val_missing : sf_pst.piece_val("p") ==>! .keyError :=
  ⟨4096, by rfl⟩

end Examples.python.sf_pst.proof
