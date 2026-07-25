import LeanModels.Circuit.Elaboration
import LeanModels.Circuit.Validity

/-!
# Typed circuit assurance cases

An assurance case binds one elaborated source circuit to one relational
behavior, allowed-world set, specification, and validity domain. Its core
obligations cannot be assembled from unrelated theorem statements.
-/

namespace LeanModels.Circuit

/-- The non-negotiable core of an assurance result. All three obligations
share the same circuit, behavior, and allowed-world predicate by
construction. Determinacy, stability, coherence, numerical refinement, and
physical-validity evidence remain additional typed certificates because they
are not meaningful for every model. -/
structure AssuranceCase
    {Artifact : Type} (circuit : Artifact)
    (behavior : Behavior World Boundary Internal)
    (allowed : World → Prop)
    (specification domain : World → Boundary → Internal → Prop) : Prop where
  safe : SafeUnder behavior allowed specification
  realizable : RealizableUnder behavior allowed
  withinDomain : StaysWithinValidityDomain behavior allowed domain

end LeanModels.Circuit
