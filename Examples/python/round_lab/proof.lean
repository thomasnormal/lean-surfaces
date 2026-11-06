import LeanModels.Python.Surface

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

load_program round_lab from "Examples/python/round_lab/round_lab.json"

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

private theorem round_ne_fstring : ("round" == fstringFormatBuiltinName) = false := by decide
private theorem round_ne_lenMult : ("round" == lenMultBuiltinName) = false := by decide
private theorem round_ne_starArg : ("round" == starArgBuiltinName) = false := by decide
private theorem round_ne_starTuple : ("round" == starTupleBuiltinName) = false := by decide
private theorem round_ne_starList : ("round" == starListBuiltinName) = false := by decide
theorem round_float_half :
    round_lab.round_float(Float64.ofBits 0x3fe0000000000000) ==> Val.int 0 := by
  exact ⟨256, rfl⟩
theorem round_float_ties :
    round_lab.round_float_ties() ==>
      Val.tuple #[Val.int 0, Val.int 2, Val.int 2, Val.int 0, Val.int (-2), Val.int (-2)] := by
  exact ⟨256, rfl⟩
theorem round_float_large :
    round_lab.round_float_large() ==>
      Val.int 1000000000000000052504760255204420248704468581108159154915854115511802457988908195786371375080447864043704443832883878176942523235360430575644792184786706982848387200926575803737830233794788090059368953234970799945081119038967640880074652742780142494579258788820056842838115669472196386865459400540160 := by
  exact ⟨256, rfl⟩
theorem round_float_nan :
    round_lab.round_float_nan() ==>!
      (.valueError "cannot convert float NaN to integer") := by
  exact ⟨256, rfl⟩
theorem round_float_infinity :
    round_lab.round_float_infinity() ==>!
      (.overflowError "cannot convert float infinity to integer") := by
  exact ⟨256, rfl⟩
theorem round_float_zero :
    round_lab.round_float_zero(Float64.ofBits 0x3ff8000000000000) ==>
      Val.float (Float64.ofBits 0x4000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_int_zero :
    round_lab.round_int_zero(7) ==> Val.int 7 := by
  exact ⟨256, rfl⟩
theorem round_bool_zero :
    round_lab.round_bool_zero(true) ==> Val.int 1 := by
  exact ⟨256, rfl⟩
theorem round_int_positive :
    round_lab.round_int_positive(7) ==> Val.int 7 := by
  exact ⟨256, rfl⟩
theorem round_bool_positive :
    round_lab.round_bool_positive(true) ==> Val.int 1 := by
  exact ⟨256, rfl⟩
theorem round_float_one :
    round_lab.round_float_one(Float64.ofBits 0x4005666666666666) ==>
      Val.float (Float64.ofBits 0x400599999999999a) := by
  exact ⟨256, rfl⟩
theorem round_float_two :
    round_lab.round_float_two(Float64.ofBits 0x3ff3c083126e978d) ==>
      Val.float (Float64.ofBits 0x3ff3ae147ae147ae) := by
  exact ⟨256, rfl⟩
theorem round_float_three :
    round_lab.round_float_three(Float64.ofBits 0x3ff3c083126e978d) ==>
      Val.float (Float64.ofBits 0x3ff3be76c8b43958) := by
  exact ⟨256, rfl⟩
theorem round_float_four :
    round_lab.round_float_four(Float64.ofBits 0x3ff3c0c1fc8f3238) ==>
      Val.float (Float64.ofBits 0x3ff3c0ebedfa43fe) := by
  exact ⟨256, rfl⟩
theorem round_float_five :
    round_lab.round_float_five(Float64.ofBits 0x3ff3c0c9539b8887) ==>
      Val.float (Float64.ofBits 0x3ff3c0cc78e9f6a9) := by
  exact ⟨256, rfl⟩
theorem round_float_six :
    round_lab.round_float_six(Float64.ofBits 0x3ff3c0ca2a5b1d5d) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca600b0293) := by
  exact ⟨256, rfl⟩
theorem round_float_seven :
    round_lab.round_float_seven(Float64.ofBits 0x3ff3c0ca4283de1b) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca45330ff8) := by
  exact ⟨256, rfl⟩
theorem round_float_eight :
    round_lab.round_float_eight(Float64.ofBits 0x3ff3c0ca43db770a) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca45330ff8) := by
  exact ⟨256, rfl⟩
theorem round_float_nine :
    round_lab.round_float_nine(Float64.ofBits 0x3ff3c0ca43db770a) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43db770a) := by
  exact ⟨256, rfl⟩
theorem round_float_ten :
    round_lab.round_float_ten(Float64.ofBits 0x3ff3c0ca43bc8a8e) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bffa2a) := by
  exact ⟨256, rfl⟩
theorem round_float_eleven :
    round_lab.round_float_eleven(Float64.ofBits 0x3ff3c0ca43bce284) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bd3a7a) := by
  exact ⟨256, rfl⟩
theorem round_float_twelve :
    round_lab.round_float_twelve(Float64.ofBits 0x3ff3c0ca43bceb50) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bcf41b) := by
  exact ⟨256, rfl⟩
theorem round_float_thirteen :
    round_lab.round_float_thirteen(Float64.ofBits 0x3ff3c0ca43bcec31) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bced12) := by
  exact ⟨256, rfl⟩
theorem round_float_fourteen :
    round_lab.round_float_fourteen(Float64.ofBits 0x3ff3c0ca43bcec47) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bcec31) := by
  exact ⟨256, rfl⟩
theorem round_float_fifteen :
    round_lab.round_float_fifteen(Float64.ofBits 0x3ff3c0ca43bcec4a) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bcec4c) := by
  exact ⟨256, rfl⟩
theorem round_float_sixteen :
    round_lab.round_float_sixteen(Float64.ofBits 0xbfcc61aba94c9000) ==>
      Val.float (Float64.ofBits 0xbfcc61aba94c8fff) := by
  exact ⟨256, rfl⟩
theorem round_float_seventeen :
    round_lab.round_float_seventeen(Float64.ofBits 0x3f4b6113d6000000) ==>
      Val.float (Float64.ofBits 0x3f4b6113d600001c) := by
  exact ⟨256, rfl⟩
theorem round_float_eighteen :
    round_lab.round_float_eighteen(Float64.ofBits 0x3f296619b1800000) ==>
      Val.float (Float64.ofBits 0x3f296619b17ffff2) := by
  exact ⟨256, rfl⟩
theorem round_float_nineteen :
    round_lab.round_float_nineteen(Float64.ofBits 0x1bcbc5db28669ce4) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_twenty :
    round_lab.round_float_twenty(Float64.ofBits 0xbe6abc642d583e42) ==>
      Val.float (Float64.ofBits 0xbe6abc642d583fca) := by
  exact ⟨256, rfl⟩
theorem round_float_twenty_one :
    round_lab.round_float_twenty_one(Float64.ofBits 0x000000037152faa4) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_twenty_two :
    round_lab.round_float_twenty_two(Float64.ofBits 0xbcba01a69be3d55f) ==>
      Val.float (Float64.ofBits 0xbcba01a6bb68a42c) := by
  exact ⟨256, rfl⟩
theorem round_float_twenty_three :
    round_lab.round_float_twenty_three(Float64.ofBits 0x1ea2921e74374449) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_twenty_four :
    round_lab.round_float_twenty_four(Float64.ofBits 0x8e6ad9eaa6aa45d4) ==>
      Val.float (Float64.ofBits 0x8000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_twenty_five :
    round_lab.round_float_twenty_five(Float64.ofBits 0x000044fa709cccc2) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_twenty_six :
    round_lab.round_float_twenty_six(Float64.ofBits 0x8328aa3794629f05) ==>
      Val.float (Float64.ofBits 0x8000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_twenty_seven :
    round_lab.round_float_twenty_seven(Float64.ofBits 0x3a2385852121f802) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_twenty_eight :
    round_lab.round_float_twenty_eight(Float64.ofBits 0x2c17b3dc78313e22) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_twenty_nine :
    round_lab.round_float_twenty_nine(Float64.ofBits 0x347beee1956a049f) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_thirty :
    round_lab.round_float_thirty(Float64.ofBits 0x034386046695a3a1) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_thirty_one :
    round_lab.round_float_thirty_one(Float64.ofBits 0x00fad538f71e3153) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_thirty_two :
    round_lab.round_float_thirty_two(Float64.ofBits 0x00000002e193c03a) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_thirty_three :
    round_lab.round_float_thirty_three(Float64.ofBits 0x0000000000000001) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_thirty_four :
    round_lab.round_float_thirty_four(Float64.ofBits 0x0000000000000001) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_thirty_five :
    round_lab.round_float_thirty_five(Float64.ofBits 0x0000000000000001) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_thirty_six :
    round_lab.round_float_thirty_six(Float64.ofBits 0x0000000000000001) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_thirty_seven :
    round_lab.round_float_thirty_seven(Float64.ofBits 0x0000000000000001) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_thirty_eight :
    round_lab.round_float_thirty_eight(Float64.ofBits 0x0000000000000001) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_thirty_nine :
    round_lab.round_float_thirty_nine(Float64.ofBits 0x0000000000000001) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_forty :
    round_lab.round_float_forty(Float64.ofBits 0x0000000000000001) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_forty_one :
    round_lab.round_float_forty_one(Float64.ofBits 0x0000000000000001) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_forty_two :
    round_lab.round_float_forty_two(Float64.ofBits 0x0000000000000001) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
theorem round_float_forty_three :
    round_lab.round_float_forty_three(Float64.ofBits 0x0000000000000001) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  exact ⟨256, rfl⟩
