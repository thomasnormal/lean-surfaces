# The research lane's backlog

Per-lane backlog, per `docs/family-architecture.md` §9.5. **Appended only by the
research lane.** Ids are `YYYY-MM-DD-research-<n>` and need no reservation,
because the lane name makes them unique.

This lane has no history in `docs/backlog.md` — it opens here. It is a
**docs-only** lane by charter: it reads the literature and the pinned
toolchain's own sources, prices what it finds against pains other lanes have
already measured, and hands the measurements it cannot take to the lanes that
own them. **It runs no Lean.** Where a proposal needs a run, this lane writes
the run down as *owed* and names the lane and the ticket.

---

## 2026-08-22-research-1 — the proof-framework survey, and the two best findings were in our own toolchain

Thomas's directive: *"look at the type of research papers mvcgen is based on.
Maybe there are useful ideas that we can add to our framework that simplifies
proofs."* Deliverable: `docs/proof-framework-research.md`, a survey **mapped
onto recorded pains** with priced proposals, a full table (§8) and a ranked
top-3 (§9).

### The finding that reorders the whole survey

**At `leanprover/lean4:v4.33.0-rc1` there are TWO verification-condition
generators, and only one of them has been censused.**

| | `mvcgen` | `vcgen` |
|---|---|---|
| logic | `Std/Do/` — 21 files | **`Std/Internal/Do/` — 17 more** |
| syntax | `Std/Tactic/Do/Syntax.lean:436` | **`Std/Tactic/Do/Syntax.lean:464`** |
| elaborator | `Lean/Elab/Tactic/Do/VCGen*` | **`Lean/Elab/Tactic/Do/Internal/VCGen/`** |
| frame rule | none | **`Std/Internal/Do/WP/Frame.lean`** (6 202 B, © 2026 Lean FRO) |
| frame inference | — | **`@[frameproc]`** |

`docs/mvcgen-pilot.md` §1.1 censused `Std/Do/` and was **correct and
incomplete** — `Std/Internal/Do/` was not in the question it was asked. The
`vcgen` grammar carries `until <term>` (stop VC generation at a pattern),
`frames <alt>+`, and `with grind`, whose source comment says the `grind`
alternative is first-class *"so it can share `vcgen`'s internalised E-graph"* —
i.e. `docs/lean-structures-census.md` §2's grind seam, **built in** rather than
wired by a `macro_rules` line.

The frame combinator's whole bill, read at the pin: `PreservesSup (op r)`,
action associativity, a unit, and a base `WPMonad` — which the pilot already
showed synthesises for our stack with zero instances written. **No
cancellativity, no step-indexing, no later modality, no resource algebra.** And
`WP.Frames.of_wp_conjunctive` gives framing from a bare preservation lemma with
`⊓` in place of `∗` — which is the exact shape of §L80's residue, the locality
fact *"nobody had written down"*.

### The second finding, same neighbourhood

**`mvcgen` has a `jp` option** (`Std/Tactic/Do/Syntax.lean:43`, default
`false`). Core's docstring: the default *"aggressively split[s] `if` and `match`
statements and inline[s] join points unconditionally. For some programs this
causes **exponential blowup of VCs**"*; `+jp` is *"a more conservative (but
**slightly lossy**) encoding that traverses every join point only once and
yields a formula the size of which is **linear in the number of control flow
splits**."*

**Our two sharpest pains are one measurement of each setting**, and neither
recorded measurement names its `jp` value:

* the deep-gate ceiling (568 ms twin → no close at 8 M heartbeats, ~14 min) is
  what *exponential* looks like at four levels;
* *"the splitter drops the discriminant … the two unreachable branches arrive as
  bare `⊢ False`"* is what *slightly lossy* looks like.

**That is §5.4a's provenance law applied to a tactic option: a number carries
the state it was measured in, and the state includes the tactic's
configuration.**

### What was NOT done, and it is the honest half

**No Lean ran.** Amendment 11 covers all Lean execution and Thomas's training
owns the machine. Every Lean-side claim in the survey is graded `[source]` with
file and line, or labelled an unrun hypothesis. In particular the following are
**owed measurements**, not results:

1. does `mvcgen (config := { jp := true })` close the four-deep gate?
2. does `WPMonad.of_frameClosure` instantiate at `ExceptT ρ (StateT W Halt)` —
   exception **outside**, where the in-tree example is exception **inside**?
3. does `Halt` have (or admit) a `WPMonad` instance at all? Nothing in
   `Std.Do`/`Std.Internal.Do` applies to `SemM` until it does.
4. what fraction of the 13 fuel-family files' plumbing is the `∀ F ≥ t` half
   that Leroy & Grall's Lemma 14 deletes?

### Owed — one ticket, and it is the cheapest in the survey

**A single Amendment-11 ticket covers items 1–3**, because all three are one
`docs/`-level experiment file, out of the pinned build by construction in the
shape `docs/mvcgen-pilot.lean` and `docs/lean-structures-census.lean` already
established. No `lake build`; `lake env lean` on one file.

* **`docs/internal-do-census.lean` + `docs/internal-do-census.md`** — the
  `Std/Internal/Do/` census, in `docs/lean-structures-census.md`'s shape. Must
  report the `Std.Internal` instability as a **first-class finding**, the way
  the pilot priced `mvcgen`'s experimental warning in its §5.4, not as a
  footnote.
* **Two runs on the existing four-deep gate**, default vs `+jp`, with both
  numbers and both settings recorded together.
* **A ~20-line repro** isolating the discriminant loss, for an upstream report.
  Upstream is live in this area (Lean 4.28.0 carries `#11698`; RFCs `#9363` and
  `#9364` sit adjacent).

### Deferred, with the reason

* **Leroy & Grall Lemma 14 for the 13 files** — probe **one** file first
  (`Examples/python/star_lab/spec.lean`, 102 lines, one `fuelMono`) and measure
  the fraction before restating thirteen. **Co-ordinate with the rebuild lane**:
  the fuel structure changes there anyway, since fuel is spent per `Kont` level
  rather than per node.
* **Characteristic formulae (`wpgen` + `mkstruct`)** — the only technique in the
  survey that is *linear AND lossless*, priced at 1 100–2 300 lines (about half
  without separation logic). **Gated three ways**: on the `Std/Internal/Do/`
  census, on `+jp`, and on a ~150-line spike that checks whether
  `wpgen [] ⟨the five-deep gate⟩` reduces to a readable term of linear size.
  The spike is designed to fail cheaply and **failure is a result**.
* **A separation-logic layer over `SemM`** — behind the census. If it is
  declined, the fallback is the modifies-clause metatheorem (§2.4): four
  definitions, ~5 lemmas, one induction, no unstable API, and it composes with
  `grind`, which already carries `getElem_insert` as `@[grind =]`.

### Handed to other lanes, not owed here

* **SV lane** — §7.4: state the ∀-schedule theorem **with its `RaceFree`
  hypothesis**. The unqualified version is **false**: IEEE 1800 deliberately
  leaves same-region races unspecified. Also §7.3: check **mid-cycle
  observability** before freezing `cycleOf_runRegion`'s boundary-only shape —
  with all fifteen regions including the six PLI regions in scope per §6.3, this
  is not hypothetical, and retrofitting a trace-level obligation is expensive.
* **Rebuild lane** — §6.5: CakeML's *Functional Big-Step Semantics* (ESOP 2016)
  is a peer-reviewed endorsement of the clocked-interpreter architecture and an
  argument **against** acquiring a second semantics. `docs/family-architecture.md`
  §3.4's adequacy rule and its fuel ruling should cite it rather than rest on
  our own reasoning.
* **All verdict emitters** — §5: **DIVERGE-with-witness is a Lisbon triple**,
  not an Incorrectness Logic triple (different quantifier structure); a
  membership site is `□` over a disjunctive state predicate and **must never be
  spelled with `⊕`**, which would turn a permission into an obligation; and
  Outcome Logic's Theorem 5.6 names a verdict we do not have — *the expected
  outcome is unreachable*, which our taxonomy currently folds into
  DIVERGE-with-witness. That is the failure mode §L26's vacuity incident had.

### Two citation corrections, made before anything is cited

* **Rensink is not in the characteristic-formula lineage** — Aceto &
  Ingólfsdóttir's survey, written by one of the originators, cites him **zero**
  times. The lineage is Graf & Sifakis 1986 → Steffen & Ingólfsdóttir 1994.
* **"Data Refinement Refined" is He, Hoare & Sanders, ESOP 1986** — not 1987,
  and not that author order.

And one confirmation the brief specifically required: **Lipton, "Reduction: A
Method of Proving Properties of Parallel Programs", *CACM* 18(12), December
1975, pp. 717–721, DOI 10.1145/361227.361234** — verified against dblp and the
CACM volume 18 table of contents. `docs/family-architecture.md` §3.6's
parenthetical citation is **correct**, merely under-specified.

### Adoption status for §9 of the standing strategy

* **§9.1 BUG BEFORE REFACTOR** — this lane ships no instrument, so it has
  nothing on the `--compare` or `git_rev` lists. Nothing to fix, and the absence
  is stated rather than assumed.
* **§9.2 consolidation by touch** — nothing of this lane's to convert.
* **§9.4 verdict vocabulary** — this lane *adds* to it (see the handoff above);
  the addition belongs in `censuskit.row()`'s vocabulary when that lands, not in
  a survey.
* **§9.5 per-lane backlog** — this file. `docs/backlog.md` untouched.

No Lean run, no build, no ticket taken for this landing. Nothing was vendored:
every paper is cited, nothing is reproduced beyond short quoted phrases, and no
fetched file entered the tree — so no per-file license question arises.
