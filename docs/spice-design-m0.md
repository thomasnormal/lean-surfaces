# SPICE M0 design status

This document used to specify the JSON-backed `LeanModels.Spice.Netlist`
prototype. That prototype was removed during the shared-circuit cutover.
The normative architecture is now:

* [circuit-assurance-architecture.md](circuit-assurance-architecture.md) for
  semantic and assurance boundaries;
* [circuit-spec-surface.md](circuit-spec-surface.md) for user-facing
  statements and proofs; and
* `LeanModels/Circuit/Spice.lean` for the direct Lean SPICE frontend.

## Current source path

`load_circuit name from "path.cir"` reads the literal source, retains its
text and hash, parses hierarchy, resolves typed node/device/model IDs, and
constructs one `ElaboratedCircuit`. Exact DC, robust real DC, transient DAE,
AC, and resolved MOS1 interpretations are fallible capabilities of that
shared identity.

There is no JSON envelope or parallel netlist AST on the proof path.
Unsupported cards fail explicitly. Ngspice and Spectre are differential
validation tools and never theorem premises.

## Physical laws and theorem shape

Conservative electrical wiring imposes shared potential and zero flow sum.
Component laws are definitions of admissible behavior, not axioms. Universal
safety is reported together with realizability and validity-domain closure;
determinacy, stability, numerical refinement, and physical model coverage
remain separate inspectable claims.

The exact divider is the walking skeleton:

```lean
load_circuit divider from "Examples/spice/divider/divider.cir"

theorem divider_out :
    divider ⊨dc {
      v, _i => v (node! divider "out") = 10 / 3
    } := by
  circuit_dc

theorem divider_realizable : RealizableDC divider := by
  circuit_dc
```

Hierarchy/contracts, robust corners, bounded noise and finite yield,
continuous RC/RLC/MOS transients, exact AC and stability, DRAM charge
sharing, and mixed-signal sampled refinement are described in the normative
documents above.
