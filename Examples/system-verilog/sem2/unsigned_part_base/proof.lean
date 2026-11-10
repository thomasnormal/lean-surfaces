import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.RunEArray

namespace Examples.«system-verilog».sem2.unsigned_part_base

open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 unsignedPartBase
  from "Examples/system-verilog/sem2/unsigned_part_base/unsigned_part_base.sv.json"

#guard !unsignedPartBase.sem.hasUnsupported

load_design_sv2 negativeRange
  from "Examples/system-verilog/sem2/unsigned_part_base/unsigned_part_negative_range.sv.json"

-- The negative right-bound geometry is a distinct, still-loud boundary.
#guard match negativeRange.sem.processes.toList with
  | [.assign (.ident "y") (.unsupported "ArraySel:dynamic" _)] => true
  | _ => false

load_design_sv2 signedBase
  from "Examples/system-verilog/sem2/unsigned_part_base/signed_part_base.sv.json"

#guard match signedBase.sem.processes.toList with
  | [.assign (.ident "y") (.unsupported "RangeSelectExpression:dynamic-signed-base" _)] => true
  | _ => false

private def e : Elab := Elab.ofDesign2 unsignedPartBase.sem
private def input (s bu : LVec) : SvState :=
  [("v", .ofNat 8 214), ("s", s), ("bu", bu)]

-- Both the bare 32-bit base and the unsigned 32-bit result of s - 2 are
-- sampled by E. Large unsigned, unknown and high-impedance bases are out of
-- range or unknown; ordinary in-range bases still select the source bits.
#guard (runE0Array e σ_src 100 [
    input (.ofNat 4 0) (.ofNat 32 4294967294),
    input (.ofNat 4 1) (.ofNat 32 4294967295),
    input (.ofNat 4 2) (.ofNat 32 0),
    input (.ofNat 4 3) (.ofNat 32 1),
    input (.ofNat 4 6) (.ofNat 32 4),
    input (.lit "x000") (.lit "000000000000000000000000000000x0"),
    input (.lit "z000") (.lit "000000000000000000000000000000z0") ]).toOption.map
    (fun rows => rows.map (fun row =>
      (SvState.showSignal (e.view row.2.store) "by_sub",
       SvState.showSignal (e.view row.2.store) "by_base"))) ==
  some [("xxxx", "xxxx"), ("xxxx", "xxxx"), ("0110", "0110"),
        ("1011", "1011"), ("1101", "1101"), ("xxxx", "xxxx"),
        ("xxxx", "xxxx")]

end Examples.«system-verilog».sem2.unsigned_part_base
