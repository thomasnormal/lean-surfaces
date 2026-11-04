# Retired SPICE envelope

The SPICE JSON envelope is retired and is not accepted by the proof surface.
SPICE sources are parsed directly in Lean by
`LeanModels/Circuit/Spice.lean`, producing typed source structures and one
`ElaboratedCircuit`.

Generated `*.json` files may remain as historical extractor fixtures and the
external extractor may still be exercised as a compatibility regression, but
no theorem, specification, solver, or simulator harness consumes them.
Verilog-A is different:
`load_veriloga` deliberately consumes a normalized envelope projected from
the pinned OpenVAF typed AST because OpenVAF owns that language frontend.

The direct SPICE parser supports the explicit documented subset and rejects
unknown cards. Numeric suffixes and decimal/scientific literals are parsed
as exact rationals. Hierarchy is represented by typed `.SUBCKT` definitions
and `X` instances before checked elaboration.
