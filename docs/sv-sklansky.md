# Sklansky comb-tactic boundary

The natural Sklansky prefix adder has two shapes outside the current v1
recognizer:

* a conditional generate inside a generate loop; and
* a genvar index such as `(i >> 1) << 1`.

The recognizer already names these as `GuardEval obligation` and
`non-affine genvar-index obligation`. The intended extension retains both
branches and carries the guard and index facts into the generated family's
rank, range, coverage, driver-disjointness, and equation obligations. Shift,
division, remainder, bitwise operations by constants or genvars, and admitted
constant system functions (including `$clog2`) are represented as parameter or
Nat terms; facts that arithmetic automation cannot establish remain named
proof obligations.

A parked prototype added guarded `TItem`/`LSite` sites, but its proof expansion
dropped a guarded family when `evalGenGuard` returned an error. That changes the
closed-form family and is unsound. The extension must therefore add guard
totality to the automatic obligations (the proof-facing `AutoObl` route), and
prove the guard is successful at every reached loop valuation before using the
branch-specific expansion. Until that theorem is present, the source-shaped
Sklansky design stays a loud refusal and the prototype is not part of the
semantic path.
