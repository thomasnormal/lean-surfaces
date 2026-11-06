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

## Proof-facing guard contract

The eventual summary API should expose a guard as a retained branch record,
not as a Boolean filter over sites. For an outer valuation `σ`, inner
valuation `σ'`, and reached environment `E'`, the required premise is

```text
GuardTotal σ' E' c := ∃ v, evalGenGuard E' c = .ok v
```

The branch site then carries the corresponding implication: `v ≠ 0` selects
the then-sites and `v = 0` selects the else-sites. The family expansion
theorem must quantify `GuardTotal` at every reached pair of loop indices before
rewriting `GenItem.expand2` to a selected branch. An evaluation error stays an
`Unsupported` result; it is never represented by an empty site list.

The same reached valuation is used for identity and obligations. A branch
site's static key includes its branch label, while its `SiteId` keeps the
complete outer and inner index path. Rank, range, coverage,
driver-disjointness, and printed-equation obligations are all conditional on
the same guard implication. This prevents a proof from establishing an
equation for an unreached arm or identifying two arms merely because their
arithmetic windows coincide.

The implementation should add guard totality to the proof-facing automatic
obligation bundle and thread it through `fam_expand2` and `Summary.sound`. It
must not make `LSite.enabled` a filter whose error case returns `[]`; that
shortcut was the unsound part of the parked prototype.
