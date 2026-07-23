import LeanModels.Spice.Switch

/-!
# Boolean CMOS block interfaces

This module sits above `Switch`. It defines reusable gate and arithmetic-block
contracts over the ideal-switch semantics. These are circuit interfaces, not
primitive transistor laws and not claims about nonlinear MOS I-V equations.
-/

namespace LeanModels.Spice

/-- Supply and input assumptions for a two-input CMOS block. The association
between these Boolean levels and voltage bands is an explicit abstraction
boundary, independently checked against ngspice. -/
def DrivesTwo (state : LogicState) (leftName rightName : String)
    (left right : Bool) : Prop :=
  state.level "0" = false ∧
  state.level "vdd" = true ∧
  state.level leftName = left ∧
  state.level rightName = right

/-- The six ideal-switch path implications contributed by a static-CMOS NAND
followed by an inverter. -/
def CmosAndDeviceLaws
    (left right nand series output vdd ground : Bool) : Prop :=
  (left = false → nand = vdd) ∧
  (right = false → nand = vdd) ∧
  (left = true → nand = series) ∧
  (right = true → series = ground) ∧
  (nand = false → output = vdd) ∧
  (nand = true → output = ground)

/-- An exact Boolean interface for a transistor-level two-input gate under
the ideal-switch abstraction.

The first conjunct is soundness: every switch-model state has the advertised
output. The second is realizability: the switch constraints are consistent
for every input vector. -/
def BinaryGateContract (netlist : Netlist)
    (leftName rightName outputName : String)
    (operation : Bool → Bool → Bool) : Prop :=
  ∀ left right,
    (∀ state, SwitchSatisfies netlist state →
      DrivesTwo state leftName rightName left right →
      state.level outputName = operation left right) ∧
    ∃ state, SwitchSatisfies netlist state ∧
      DrivesTwo state leftName rightName left right

/-- Full ideal-switch interface for a one-bit half-adder. -/
def HalfAdderContract (netlist : Netlist)
    (leftName rightName sumName carryName : String) : Prop :=
  ∀ left right,
    (∀ state, SwitchSatisfies netlist state →
      DrivesTwo state leftName rightName left right →
      state.level sumName = Bool.xor left right ∧
        state.level carryName = Bool.and left right) ∧
    ∃ state, SwitchSatisfies netlist state ∧
      DrivesTwo state leftName rightName left right

/-- One observable run of a particular transistor-level half-adder. -/
def HalfAdderObservation (netlist : Netlist)
    (leftName rightName sumName carryName : String)
    (left right sum carry : Bool) : Prop :=
  ∃ state,
    SwitchSatisfies netlist state ∧
    DrivesTwo state leftName rightName left right ∧
    state.level sumName = sum ∧
    state.level carryName = carry

/-- Implementation-independent Boolean behavior of a half-adder. -/
def HalfAdderBehavior
    (left right sum carry : Bool) : Prop :=
  sum = Bool.xor left right ∧ carry = Bool.and left right

end LeanModels.Spice
