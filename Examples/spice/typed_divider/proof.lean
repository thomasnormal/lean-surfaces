import LeanModels.Circuit

namespace Examples.spice.typed_divider.proof

open LeanModels.Circuit

load_circuit typedDivider from
  "Examples/spice/typed_divider/typed_divider.cir"

theorem typed_divider_out :
    typedDivider ⊨dc {
      v, _i => v (node! typedDivider "out") = 10 / 3
    } := by
  circuit_dc

theorem typed_divider_realizable :
    RealizableDC typedDivider := by
  circuit_dc

theorem typed_divider_wellposed :
    DeterminateDC typedDivider := by
  circuit_dc

theorem typed_divider_assurance :
    AssuranceCase typedDivider (NominalDCBehavior typedDivider)
      (fun _world => True)
      (SourceBinding.identity typedDivider
        (fun _circuit => NominalDCBehavior typedDivider)
        (fun _circuit _world => True))
      (fun _world assignment _internal =>
        assignment.observeVoltage typedDivider
          (node! typedDivider "out") = 10 / 3)
      (fun _world _assignment _internal => True) := by
  constructor
  · intro _world assignment _internal _hallowed hbehavior
    exact typed_divider_out assignment hbehavior
  · intro _world _hallowed
    obtain ⟨assignment, hassignment⟩ := typed_divider_realizable
    exact ⟨assignment, (), hassignment⟩
  · intro _world _assignment _internal _hallowed _hbehavior
    trivial

end Examples.spice.typed_divider.proof
