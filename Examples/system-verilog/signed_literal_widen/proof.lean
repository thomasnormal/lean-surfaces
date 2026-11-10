import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».signed_literal_widen

open LeanModels.Sv

load_design_sv2 signedLiteralWiden
  from "Examples/system-verilog/signed_literal_widen/signed_literal_widen.sv.json"

/- MEASURED W=4: this point now refuses `Resize:signed` with
   "signed operand widened 4 → 8 at these parameters".  Keep the refusal
   pinned while the context-dependent signed widening boundary is separate. -/
#guard (signedLiteralWiden.sem 4).hasUnsupported
#guard !(signedLiteralWiden.sem 8).hasUnsupported
#guard !(signedLiteralWiden.sem 16).hasUnsupported

/- The parser's signed literal marker is retained through instantiation.  A
   signed context receives `resizeSigned`, while the mixed unsigned context
   receives `resize` around the same signed literal.  These are source-shaped
   checks of the node mapping; the differential rows exercise their values. -/
def signedAdd : Expr2 → Bool
  | .binary .add (.ident _)
      (.resizeSigned _ (.resizeSigned 8 (.lit _))) => true
  | .resize _ e => signedAdd e
  | _ => false

def signedGe : Expr2 → Bool
  | .scmp .ge (.ident _)
      (.resizeSigned _ (.resizeSigned 8 (.lit _))) => true
  | .resize _ e => signedGe e
  | _ => false

def mixedZeroExtend : Expr2 → Bool
  | .binary .add _ (.resize _ (.resizeSigned 8 (.lit _))) => true
  | .resize _ e => mixedZeroExtend e
  | _ => false

def rhsExprs (N : Nat) : List Expr2 :=
  match (signedLiteralWiden.sem N).processes.toList with
  | [.assign _ y, .assign _ mixed, .assign _ ge] => [y, mixed, ge]
  | _ => []

#guard [8, 16].all fun N =>
  match rhsExprs N with
  | [y, mixed, ge] =>
      signedAdd y && signedGe ge && mixedZeroExtend mixed
  | _ => false

end Examples.«system-verilog».signed_literal_widen
