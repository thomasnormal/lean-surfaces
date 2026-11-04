/-!
# Normalized OpenVAF Verilog-A AST envelope

OpenVAF Reloaded owns preprocessing and parsing. The repository extractor
projects OpenVAF's typed syntax tree into this deliberately small,
source-stable representation. Lean then resolves all names and checks the
semantic subset before constructing a contribution model.
-/

namespace LeanModels.VerilogA

structure Span where
  line : Nat
  column : Nat := 1
deriving Repr, BEq, DecidableEq, Inhabited

structure SourceBranch where
  positive : String
  negative : String
deriving Repr, BEq, DecidableEq, Inhabited

inductive SourceExpr where
  | literal (value : Rat)
  | name (name : String)
  | potential (branch : SourceBranch)
  | flow (branch : SourceBranch)
  | ddt (value : SourceExpr)
  | neg (value : SourceExpr)
  | add (left right : SourceExpr)
  | sub (left right : SourceExpr)
  | mul (left right : SourceExpr)
  | div (left right : SourceExpr)
deriving Repr, BEq, DecidableEq, Inhabited

inductive SourceTarget where
  | potential (branch : SourceBranch)
  | flow (branch : SourceBranch)
deriving Repr, BEq, DecidableEq, Inhabited

structure SourceContribution where
  span : Span
  target : SourceTarget
  expression : SourceExpr
deriving Repr, BEq, DecidableEq, Inhabited

structure SourceParameter where
  span : Span
  name : String
  defaultValue : Rat
deriving Repr, BEq, DecidableEq, Inhabited

structure SourceModule where
  span : Span
  name : String
  ports : Array String
  inouts : Array String
  electricals : Array String
  parameters : Array SourceParameter
  contributions : Array SourceContribution
deriving Repr, BEq, Inhabited

structure FrontendProvenance where
  name : String
  repository : String
  revision : String
  representation : String
deriving Repr, BEq, Inhabited

structure SourceArtifact where
  path : String
  text : String
deriving Repr, BEq, Inhabited

structure Envelope where
  schema : String
  frontend : FrontendProvenance
  source : SourceArtifact
  module : SourceModule
deriving Repr, BEq, Inhabited

end LeanModels.VerilogA
