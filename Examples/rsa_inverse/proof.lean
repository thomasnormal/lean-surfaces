/-
Proof module for `Examples/rsa_inverse/spec.lean` (three-file example
layout; see Examples/tri/proof.lean for the pattern rationale). The
theorems of the coming phase are proved here under the same names as the
spec statements, which will reference them via `:= by proofs`. This file
loads its own copy of the program literal (same envelope, different
constant); `proofs` bridges the two constants by unfolding.

Target: python-rsa 4.9.1 `extended_gcd` / `inverse` (see the provenance
docstring in rsa_inverse.py). `inverse`'s single Unsupported node (the
`raise NotRelativePrimeError` statement) will be covered by an
unreachability argument: on coprime inputs the gcd is 1, the guard is
false, and no run touches the node.
-/
import LeanModels

namespace Examples.rsa_inverse.proof

open LeanModels LeanModels.Python

load_program rsa_inverse from "Examples/rsa_inverse/rsa_inverse.json"

-- Theorems land here in the next phase.

end Examples.rsa_inverse.proof
