# Backlog — the `pyrebuild` lane (the Python monadic rebuild)

Per §9.5: appended only by this lane; ids need no reservation because the
lane name makes them unique. Newest last.

---

## 2026-08-22-pyrebuild-1 — THE ACCEPTANCE GATE PASSES

**Thomas's ruling** was to rebuild the interpreter rather than debug the old
one. The rebuild is a SECOND Python semantics on the family substrate, written
in do-notation, whose acceptance test was parity with the trunk on the trunk's
own differential battery. Measured under `tools/triad.sh`, full build green:

| gate | result |
|---|---|
| `lake build` (FULL) | **green**, exit 0 |
| `docs_check` | green |
| `diff_test` (trunk baseline) | 1394 cases, 0 failed, 118 whitelisted, 1276 matched |
| `monadic_gate` | **1394 / 1394 parity (100.0 %)**, frontier 0, **divergences 0** |
| `script_corpus` trunk | 65 scripts, 0 failed, 50 matched, 15 loud |
| `script_corpus` **monadic** | 65 scripts, 0 failed, 50 matched, 15 loud |
| script rows, trunk vs monadic | **IDENTICAL row-for-row** (verdict AND file) |

The last row is the one that matters: equal TOTALS would not have proved the
same rows matched, so the comparison is per row. Oracle CPython 3.9.19; the
runner was rebuilt in this same tenure (a stale binary would have reported
pre-fix numbers — §5.4a with a build timestamp as the state).

**What the rebuild is.** `SemM W ρ = ExceptT ρ (StateT W Halt)` in
`LeanModels/Core/Outcome.lean`, shared with the family; Python's instantiation,
the `Run` isomorphism and both zoom adapters in `Python/Monadic/Substrate.lean`;
the interpreter split at the fuel boundary into a fuel-free structural half and
a fuel-structural knot; 19 `@[spec]` triples; 18 `#guard`s; two mvcgen gates.
Zero `sorry`, zero `native_decide`.

**MERGE STATUS: NOT merged.** The branch remains the rebuild's home per the
standing ruling; the merge is the coordinator's call.

### Findings this landing produced (details in docs/python-monadic-rebuild.md)

* **The recursion-knot boundary.** `Kont` was introduced as a fuel boundary and
  ended up doing four distinct jobs — fuel, a structural obstacle the measure
  could not express (the dict lockstep, kwargs values), a fuel-bounded MUTUAL
  knot (`stepIter`/`execGen`), and the script layer's shells. Anything a
  structural measure cannot express can be cut out of a recursive block through
  a defunctionalized record for the price of one field.
* **The knot must be built LAZILY.** A strict `let` makes construction O(fuel)
  PER ENTRY. It passed three green gate runs (fuel 10 000) and stalled outright
  at script mode's 10⁶. The strict version compiles, type-checks and passes
  every `#guard` — it is wrong only in COST, which no correctness gate detects.
* **A predicted defect that did not exist.** "The run retains the world/trace
  unboundedly" was written down first and refuted by measurement: 36–37 MB on
  both interpreters across three orders of magnitude of fuel.
* **Two blind instruments, both found by adding a third.** `diff_test`
  over-reports the rebuild by exactly 56 rows (it compares whitelisted rows by
  STATUS alone); `refusal_census` exits 0 on both while 66 lines of its own
  output differ. Hence `harness/monadic_gate.py`.
* **A gate is blind to what its corpus lacks.** The closed-function gate read
  1394/1394 with ZERO frontier while three arms were still `notYet` —
  unreachable from `cases.json` by construction. This is why acceptance is BOTH
  corpora, permanently, even now that both are green.
* **Three `mvcgen` defects recorded**, and the partition between them:
  `grind` wired into `mvcgen_trivial_extensible` deletes closing scripts (the
  bottom of the pipeline) but cannot help the four-deep gate, which dies inside
  mvcgen's own SPLITTING (the top). The altitude lemma that would fix it cannot
  be stated, because the splitter drops the discriminant.

### Owed

* `twinAgrees` (§8.5) — the adequacy theorem. Not attempted, not needed for the
  gate, and on the critical path for any definition swap.
* `--build-target` landed in `tools/triad.sh` with this commit (§7.1a canon).
