import LeanModels.Python.Surface
import Examples.spice.typed_divider.proof

open LeanModels.Circuit

load_circuit typedDivider from
  "Examples/spice/typed_divider/typed_divider.cir"

#circuit_check typedDivider dc shows "out" = (10 / 3 : Rat)

/-- Every assignment satisfying ground, Ohm's law, the source law, and KCL
has the exact divider output. -/
theorem typed_divider_out :
    typedDivider ⊨dc {
      v, _i => v (node! typedDivider "out") = 10 / 3
    } := by proofs

/-- The universal theorem is paired with an explicit non-vacuity result. -/
theorem typed_divider_realizable :
    RealizableDC typedDivider := by proofs

/-- The complete DC assignment, including branch currents, is unique. -/
theorem typed_divider_wellposed :
    DeterminateDC typedDivider := by proofs

theorem typed_divider_assurance :
    AssuranceCase typedDivider (NominalDCBehavior typedDivider)
      (fun _world => True)
      (SourceBinding.identity typedDivider
        (fun _circuit => NominalDCBehavior typedDivider)
        (fun _circuit _world => True))
      (fun _world assignment _internal =>
        assignment.observeVoltage typedDivider
          (node! typedDivider "out") = 10 / 3)
      (fun _world _assignment _internal => True) := by proofs

/-- The outer non-vacuity link: at least one world is allowed. `RealizableDC`
above closes the empty-behavior hole; this closes the empty-world one. -/
theorem typed_divider_grounded : GroundedUnder (fun _world : Unit => True) :=
  ⟨(), trivial⟩

/-- The existential form, which an empty allowed-world set would refute. -/
theorem typed_divider_exhibits :
    ExhibitsUnder (NominalDCBehavior typedDivider) (fun _world => True)
      (fun _world assignment _internal =>
        assignment.observeVoltage typedDivider
          (node! typedDivider "out") = 10 / 3)
      (fun _world _assignment _internal => True) :=
  typed_divider_assurance.exhibits typed_divider_grounded

#assurance_report typedDivider using typed_divider_assurance
  [typed_divider_wellposed]

#print axioms typed_divider_grounded
#print axioms typed_divider_exhibits

#print axioms typed_divider_out
#print axioms typed_divider_realizable
#print axioms typed_divider_wellposed
#print axioms typed_divider_assurance
#print axioms typedDivider_solution_satisfies
