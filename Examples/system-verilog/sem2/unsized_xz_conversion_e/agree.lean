import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE

namespace Examples.«system-verilog».sem2.unsized_xz_conversion_e.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 unsizedXZConversionE
  from "Examples/system-verilog/sem2/unsized_xz_conversion_e/unsized_xz_conversion_e.sv.json"

#guard unsizedXZConversionE.pdesign.others ==
  [("ConversionExpression:xz-literal-parametric", "'bx"),
   ("IntegerLiteral:unsized-xz-parametric", "'bx"),
   ("ConversionExpression:xz-literal-parametric", "'bz"),
   ("IntegerLiteral:unsized-xz-parametric", "'bz"),
   ("ConversionExpression:xz-literal-parametric", "'hx0"),
   ("IntegerLiteral:unsized-xz-parametric", "'hx0"),
   ("ConversionExpression:xz-literal-parametric", "'hz1"),
   ("IntegerLiteral:unsized-xz-parametric", "'hz1")]

private def sourceBody : PStmt :=
  match unsizedXZConversionE.pdesign.processes with
  | [.assign _ _, .alwaysFF _ body] => body
  | _ => .unsupported "fixture" "unexpected process shape"

#guard match sourceBody with
  | .block [
      .nbaAssign "qx" (.unsupported "ConversionExpression:unsized-xz" bx),
      .nbaAssign "qz" (.unsupported "ConversionExpression:unsized-xz" bz),
      .nbaAssign "qhx" (.unsupported "ConversionExpression:unsized-xz" hx),
      .nbaAssign "qhz" (.unsupported "ConversionExpression:unsized-xz" hz)] =>
      bx == "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" &&
      bz == "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz" &&
      hx == "xxxxxxxxxxxxxxxxxxxxxxxxxxxx0000" &&
      hz == "zzzzzzzzzzzzzzzzzzzzzzzzzzzz0001"
  | _ => false

private def stimulus (clk : String) : SvState :=
  [("clk", LVec.lit clk)]

private def edge (n : Int) : Option MemEState :=
  match MemEDesign.ofPDesign unsizedXZConversionE.pdesign [n] with
  | .ok d =>
      match d.step d.init (stimulus "0") with
      | .ok s0 => (d.step s0 (stimulus "1")).toOption
      | .error _ => none
  | .unsupported _ | .timeout => none

private def output (n : Int) (name : String) : Option LVec :=
  (edge n).bind fun s => SvState.lookup s.scalar name

#guard output 40 "qx" == some (LVec.xVec 40)
#guard output 40 "qz" == some (LVec.replicate 40 .lz)
#guard output 40 "qhx" == some (LVec.lit
  "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx0000")
#guard output 40 "qhz" == some (LVec.lit
  "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz0001")
#guard output 8 "qx" == some (LVec.xVec 8)
#guard output 8 "qz" == some (LVec.replicate 8 .lz)
#guard output 8 "qhx" == some (LVec.lit "xxxx0000")
#guard output 8 "qhz" == some (LVec.lit "zzzz0001")
#guard output 40 "mem_q" == some (LVec.xVec 40)
#guard output 8 "mem_q" == some (LVec.xVec 8)

end Examples.«system-verilog».sem2.unsized_xz_conversion_e.agree
