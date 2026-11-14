import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.HierarchyCoreMem

/-!
Canonical-E receipt for IEEE 1800-2023 §23.3.3: a parameter-sized one-rank
unpacked array is connected from a parent input port to a child input port.
The parser's `ArraySel` with an empty index path is retained as a whole-array
connection; `MemState.copyId` transfers the native block while checking the
unpacked bounds and converting each destination element.
-/
namespace Examples.«system-verilog».sem2.unpacked_port_parameterized_canonical_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 unpackedPortParameterized from
  "Examples/system-verilog/sem2/unpacked_port_parameterized_canonical_e/unpacked_port_parameterized_canonical_e.sv.json"

#guard unpackedPortParameterized.plib.length == 1
#guard unpackedPortParameterized.pdesign.generates.any fun g =>
  match g with
  | .inst i => i.conns.any fun c =>
      match c with
      | .input "a" (some (.arrayElem "data" [])) _ => true
      | _ => false
  | _ => false

private def stimulus : List SvState :=
  [[("data[0]", LVec.ofNat 4 1), ("data[1]", LVec.ofNat 4 2),
    ("data[2]", LVec.ofNat 4 4)],
   [("data[0]", LVec.ofNat 4 10), ("data[1]", LVec.ofNat 4 5),
    ("data[2]", LVec.ofNat 4 7)],
   [("data[0]", LVec.lit "xxxx"), ("data[1]", LVec.ofNat 4 3),
    ("data[2]", LVec.ofNat 4 8)],
   [("data[0]", LVec.ofNat 4 9), ("data[1]", LVec.lit "zzzz"),
    ("data[2]", LVec.ofNat 4 0)],
   [("data[0]", LVec.ofNat 4 15), ("data[1]", LVec.ofNat 4 15),
    ("data[2]", LVec.lit "xxxx")]]

def outputs (n : Nat) : Res (List String) := do
  let d ← unpackedPortParameterized.e 4 n
  let initial ← d.initialState
  let rows ← runCoreMemRows d initial stimulus
  .ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "y")

/- The value rows are checked by `oracle.lean` and `check.py`; reducing both
   hierarchy points in a kernel `#guard` makes elaboration needlessly large. -/

#print axioms CoreMemDesign.step

end Examples.«system-verilog».sem2.unpacked_port_parameterized_canonical_e
