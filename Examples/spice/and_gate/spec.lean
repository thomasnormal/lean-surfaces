import Examples.spice.and_gate.proof

open LeanModels.Spice

load_netlist andGateDeck from "Examples/spice/and_gate/and_gate.json"

#guard andGateDeck.hasUnsupported == false
#guard match flatten andGateDeck with
  | .error (.unsupported "M" _) => true
  | _ => false

/-- Any six-transistor NAND-plus-inverter block satisfying the individual MOS
conducting-path laws computes Boolean AND. -/
theorem cmos_and_from_device_laws
    {left right nand series output vdd ground : Bool}
    (hlaws : CmosAndDeviceLaws left right nand series output vdd ground)
    (hvdd : vdd = true) (hground : ground = false) :
    output = Bool.and left right := by proofs

/-- For all four input vectors, every ideal-switch state of the extracted
CMOS network has `out = a && b`, and at least one such state exists. -/
theorem cmos_and_correct :
    BinaryGateContract andGateDeck "a" "b" "out" (· && ·) := by proofs

/-- The same extracted transistor deck proved directly against its exact
ngspice MOS Level-1 equations and KCL, within the 0–5 V operating envelope. -/
theorem cmos_and_mos1_correct :
    Mos1BinaryGateContract andGateDeck "a" "b" "out" (· && ·) := by proofs

#print axioms cmos_and_from_device_laws
#print axioms cmos_and_correct
#print axioms cmos_and_mos1_correct
