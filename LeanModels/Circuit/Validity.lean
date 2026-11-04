import LeanModels.Circuit.Behavior

/-!
# Model-validity claims and evidence

Evidence metadata never proves its own coverage claim. `AcceptedValidity`
contains both the record and the proof or explicit hypothesis that the claim
holds.
-/

namespace LeanModels.Circuit

inductive CoverageModality where
  | kernelTheorem
  | checkedCertificate
  | deterministicBound
  | probabilistic
  | finiteValidation
  | calibration
  | explicitAssumption
deriving Repr, BEq, DecidableEq, Inhabited

structure EvidenceRecord where
  artifact : String
  artifactHash : String
  version : String
  issuer : String
  modality : CoverageModality
  domainDescription : String
  confidenceDescription : String := ""
  evidenceDate : String := ""
  supersedes : Option String := none
deriving Repr, BEq, Inhabited

/-- A model envelope covers the intended physical behaviors on a named
operating domain. The physical relation remains an explicit parameter. -/
structure ValidityClaim
    (World Boundary Internal : Type) where
  physical : Behavior World Boundary Internal
  envelope : Behavior World Boundary Internal
  domain : World → Boundary → Internal → Prop
  statement : Prop :=
    ∀ world boundary internal,
      domain world boundary internal →
      physical world boundary internal →
      envelope world boundary internal

/-- Provenance paired with an actual Lean proof or explicit theorem
hypothesis. Metadata alone cannot construct this structure. -/
structure AcceptedValidity
    (claim : ValidityClaim World Boundary Internal) where
  evidence : EvidenceRecord
  accepted : claim.statement

end LeanModels.Circuit
