import LeanModels.Python.Surface

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

load_program round_lab from "Examples/python/round_lab/round_lab.json"

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem round_float_half :
    round_lab.round_float(Float64.ofBits 0x3fe0000000000000) ==> Val.int 0 := by
  exact ⟨32, rfl⟩

theorem round_float_ties :
    round_lab.round_float_ties() ==>
      Val.tuple #[Val.int 0, Val.int 2, Val.int 2, Val.int 0, Val.int (-2), Val.int (-2)] := by
  exact ⟨32, rfl⟩

theorem round_float_large :
    round_lab.round_float_large() ==>
      Val.int 1000000000000000052504760255204420248704468581108159154915854115511802457988908195786371375080447864043704443832883878176942523235360430575644792184786706982848387200926575803737830233794788090059368953234970799945081119038967640880074652742780142494579258788820056842838115669472196386865459400540160 := by
  exact ⟨128, rfl⟩

theorem round_float_nan :
    round_lab.round_float_nan() ==>!
      (.valueError "cannot convert float NaN to integer") := by
  exact ⟨32, rfl⟩

theorem round_float_infinity :
    round_lab.round_float_infinity() ==>!
      (.overflowError "cannot convert float infinity to integer") := by
  exact ⟨32, rfl⟩

end Examples.python.round_lab.proof
