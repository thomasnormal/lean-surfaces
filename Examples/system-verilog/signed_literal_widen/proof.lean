import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».signed_literal_widen

open LeanModels.Sv

load_design_sv2 signedLiteralWiden
  from "Examples/system-verilog/signed_literal_widen/signed_literal_widen.sv.json"

#guard !(signedLiteralWiden.sem 4).hasUnsupported
#guard !(signedLiteralWiden.sem 8).hasUnsupported
#guard !(signedLiteralWiden.sem 16).hasUnsupported

-- The signed literal is -128 when widened with the signed input, while the
-- mixed expression zero-extends it because its other operand is unsigned.
#guard (match run2 (signedLiteralWiden.sem 4) σ_src 256 [
    [("x", .ofNat 4 8), ("u", .ofNat 4 8)],
    [("x", .ofNat 4 7), ("u", .ofNat 4 7)]] with
  | .ok [s0, s1] =>
      [((SvState.lookup s0 "y").map LVec.toBinString,
        (SvState.lookup s0 "mixed").map LVec.toBinString,
        (SvState.lookup s0 "ge").map LVec.toBinString),
       ((SvState.lookup s1 "y").map LVec.toBinString,
        (SvState.lookup s1 "mixed").map LVec.toBinString,
        (SvState.lookup s1 "ge").map LVec.toBinString)] ==
      [(some "1000", some "1000", some "1"),
       (some "0111", some "0111", some "1")]
  | _ => false)

#guard (match run2 (signedLiteralWiden.sem 8) σ_src 256 [
    [("x", .ofNat 8 128), ("u", .ofNat 8 128)],
    [("x", .ofNat 8 127), ("u", .ofNat 8 127)]] with
  | .ok [s0, s1] =>
      [((SvState.lookup s0 "y").map LVec.toBinString,
        (SvState.lookup s0 "mixed").map LVec.toBinString,
        (SvState.lookup s0 "ge").map LVec.toBinString),
       ((SvState.lookup s1 "y").map LVec.toBinString,
        (SvState.lookup s1 "mixed").map LVec.toBinString,
        (SvState.lookup s1 "ge").map LVec.toBinString)] ==
      [(some "00000000", some "00000000", some "1"),
       (some "11111111", some "11111111", some "1")]
  | _ => false)

#guard (match run2 (signedLiteralWiden.sem 16) σ_src 256 [
    [("x", .ofNat 16 32768), ("u", .ofNat 16 32768)],
    [("x", .ofNat 16 127), ("u", .ofNat 16 127)]] with
  | .ok [s0, s1] =>
      [((SvState.lookup s0 "y").map LVec.toBinString,
        (SvState.lookup s0 "mixed").map LVec.toBinString,
        (SvState.lookup s0 "ge").map LVec.toBinString),
       ((SvState.lookup s1 "y").map LVec.toBinString,
        (SvState.lookup s1 "mixed").map LVec.toBinString,
        (SvState.lookup s1 "ge").map LVec.toBinString)] ==
      [(some "0111111110000000", some "1000000010000000", some "0"),
       (some "1111111111111111", some "0000000011111111", some "1")]
  | _ => false)

end Examples.«system-verilog».signed_literal_widen
