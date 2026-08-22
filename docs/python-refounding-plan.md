# Re-founding the Python tier on the monadic interpreter — the retirement census

**Thomas's ruling** (2026-08-22): *"Yes, please merge. Keep only the new
versions, no reason to be backwards compatible on anything."*

The rebuild passed the acceptance gate (1394/1394 closed-function parity, zero
divergences, script corpus identical row-for-row). Under "no compat" the
question is no longer *whether* the trunk interpreter retires but *in what order
its consumers move*. **This document is a PLAN and a MEASUREMENT. It changes no
Lean.**

---

## §1 THE CENSUS — what actually depends on the old interpreter

### 1.1 The tier layer (`LeanModels/Python/`)

| file | lines | theorems | role |
|---|---:|---:|---|
| `Semantics.lean` | 6684 | 20 | THE INTERPRETER — the statement target of everything below |
| `PayloadBlind.lean` | 3922 | 113 | meta-theorems over the interpreter |
| `VCTactic.lean` | 3371 | 30 | **the walker** (`py_vcgen`, `py_loop`) |
| `Obs.lean` | 3119 | 75 | observation/erasure meta-theory |
| `ClockErase.lean` | 2732 | 70 | the clock-erasure meta-theorem |
| `VCGen.lean` | 2034 | 95 | VC generation |
| `Json.lean` | 1660 | 0 | INGESTION — shared, not interpreter-specific |
| `Runtime.lean` | 1317 | 26 | `RVal`/`World`/`Run` — shared |
| `VC2.lean` | 939 | 27 | triple layer |
| `Surface.lean` | 930 | 24 | the typed spec surface |
| `Script.lean` | 893 | 0 | script admissions — **530 lines already reused** |
| `DictCalc.lean` | 825 | 43 | dict calculation lemmas |
| `VC.lean` | 546 | 26 | `PyTriple` |
| `LoopTactic.lean` | 487 | 1 | loop tactic |
| others | ~2000 | ~40 | Ast/Logic/ModuleInit/Delab/Tests |

**~32 400 lines, ~591 theorems.**

### 1.2 The campaign estate (`Examples/python/`)

**35 385 lines, 1 357 theorems**, of which `sunfish/` is **25 063 lines and 929
theorems** — the flagship. Its largest files: `bound_depth` (4356/221),
`genmoves_ray` (3740/174), `basecase_depth0` (2422/54), `fold_depth1`
(2178/55), `move_gate` (2090/163), `value_bound` (1765/57).

### 1.3 Coupling, measured by symbol

| symbol | files |
|---|---:|
| `#py_check` | 63 |
| `py_simp` | 42 |
| `CallsTo` | 39 |
| `CallsIn` | 23 |
| `py_vcgen` | 22 |
| `py_loop` | 18 |
| `PyTriple` | 8 |
| fuel-family forms (`∃ t, ∀ F ≥ t`, `fuelMono`, `_at_least`) | **13** |

**The load-bearing number is the last one: only 13 files state fuel-family
claims.** Those are the ones whose SHAPE changes, because the rebuild's fuel
boundary is different — everything else is a statement about values and worlds
that the monadic interpreter answers identically (that is what 1394/1394 means).

---

## §2 CLASSIFICATION

**(a) RE-PROVE on the monadic interpreter** — value/world claims on the
fuel-free fragment. `mvcgen` + `@[spec]` + `grind` make these cheap per gate:
the closing script is often *deleted outright* (measured on two gates). This is
the large majority by file count.

**Caveat, measured and not to be forgotten:** the four-deep `value_scores` shape
does **not** close even with `grind`, because the blowup is in `mvcgen`'s own
splitting, not in discharge, and the altitude lemma that would fix it cannot be
stated (the splitter drops the discriminant). **So (a) is cheap per gate but has
a known ceiling on statement depth.** Deep gates fall back to hand proof, and
that cost must be in every estimate.

**(b) RESTATE** — the 13 fuel-family files. `∃ t, ∀ F ≥ t` is outside the WP
layer by construction (`Triple` is unary on one program; these are claims about
a *family*). They are hand-proved against the NEW interpreter's fuel structure,
and that structure genuinely differs: fuel is spent only at `Kont`'s boundary,
so a claim that counted per-node decrements is not merely re-typed, it is
re-derived. **These are the expensive ones and they cannot be transported.**

**(c) DELETE — AND THE FIRST DRAFT OF THIS SECTION WAS WRONG.** It said
`VCTactic` (3371), `LoopTactic` (487) and `VCGen`'s generation half could be
"deleted immediately, ~5 300 lines, no successor". **Measured, every one of them
is CONSUMED right now:**

| file | export | consumer files | of which `Examples/` |
|---|---|---:|---:|
| `VCTactic.lean` | `py_vcgen` | **17** | 10 |
| `LoopTactic.lean` | `py_loop` | **14** | 13 |
| `LoopTactic.lean` | `py_begin` | **11** | 11 |
| `VCGen.lean` | 63 distinctive symbols | **40 used elsewhere**, 23 by nobody | — |

`VCGen`'s live symbols are the worst case for the original claim, because they
are **statement vocabulary**, not generation internals: `PyStmtTriple` (10
files), `IterSteps` (10), `GenEmits` (10), `IterDrains` (8). Deleting that file
would not remove machinery, it would remove the words 10 campaign files use to
*say* what they prove.

**The error, named so it is not repeated: "has no successor" is a claim about
the FUTURE and says nothing about PRESENT consumers.** The monadic route's vcgen
really is core's `mvcgen`, so nothing new will ever import the walker — and that
is exactly the sentence that made a zero-consumer conclusion feel safe without
counting. The master-never-red rule is what a deletion on that reasoning would
have broken.

**Revised: NOTHING in class (c) deletes now.** The ~5 300 lines are a real
saving and remain collectable, but **per file, on re-founding, as each file's
consumers move** — the deletion is the LAST step of a file's migration, never a
precondition for it. The only genuinely zero-consumer surface measured is **23
dead symbols inside `VCGen.lean`**, which is not worth editing a file that ten
campaign files depend on.

**SHARED — not retiring at all**: `Ast`, `Json`, `Runtime`, `Surface`,
`Script`'s admissions, `DictCalc`. The rebuild already imports these; they were
never interpreter-specific. This is the maximal-trunk instinct paying at
retirement time.

---

## §3 `twinAgrees` — NOT a bridge, possibly a TRANSPORT TOOL

Under "no compat" `twinAgrees` is explicitly **not** a compatibility layer to
maintain. But it may still be the cheapest way to move large GREEN files:
prove adequacy once, transport every theorem in a file mechanically, then delete
the old file *and the adequacy theorem with it*.

**The price comparison, per file:**

* **Direct re-proof** costs one `mvcgen` invocation per theorem, cheap on the
  fuel-free fragment and unbounded on deep ones (§2's ceiling).
* **Transport** costs `twinAgrees` **once** — a whole-interpreter induction,
  the genuinely hard artifact — and then near-zero per theorem.

**The crossover is roughly "does one file carry more than ~100 theorems of
mostly-mechanical value-claims".** By the census, four files do:
`bound_depth` (221), `genmoves_ray` (174), `move_gate` (163), `PayloadBlind`
(113). Together they are **671 theorems, ~14 000 lines** — about half the
campaign's theorem count in four files.

**Recommendation: decide `twinAgrees` on those four alone.** If they re-prove
cheaply in a spike, skip it entirely; if they resist, `twinAgrees` pays for
itself there and nowhere else. **Do not start it speculatively** — it is on
nobody's critical path now that the gate has passed without it.

---

## §4 SEQUENCING — the in-flight lanes decide this, not the census

Two lanes have live inches stated against the old interpreter:

* **calmness / F3c** — `qs_stream.lean` (258 lines, 8 theorems), inch 1 just
  landed.
* **R-track / R3c** — `value_bound` / `fold_depth1` / `order_genexp` /
  `genmoves_drain`, all touched today.

**The price of finishing on the old interpreter vs switching now:**

`qs_stream` is **small and early** (8 theorems, one inch in). Switching F3c now
costs re-stating 8 theorems; finishing on the old one and switching later costs
re-stating however many F3c ends with — and F3c's siblings suggest that is
50–200. **F3c should switch now**; it is the cheapest switch available and it
gets the first real campaign inch written on the new interpreter.

R3c is **mid-inch across four files** with `value_bound` (57) and `fold_depth1`
(55) already deep. **R3c should finish its current inch on the old interpreter**
and switch at the inch boundary — switching mid-inch pays the re-statement cost
*and* loses the inch's context, which is the worst of both.

---

## §5 TOP-3 RECOMMENDATION

1. **Switch F3c to the monadic interpreter now.** Smallest in-flight surface (8
   theorems), and it makes the next campaign inch the first one *founded* on the
   new interpreter rather than transported to it. This is the sequencing
   decision with the shortest half-life — it gets more expensive every day.
2. ~~Delete class (c) immediately.~~ **WITHDRAWN ON MEASUREMENT.** All three
   files are consumed today (`py_vcgen` 17 files, `py_loop` 14, `py_begin` 11,
   `VCGen` 40 live symbols including the statement vocabulary of 10 campaign
   files). The saving is real and stays on the books, collected **per file at
   the end of that file's migration**. What replaces this slot is the cheap,
   genuinely-zero-risk half: **mark the layer LEGACY and forbid new consumers**,
   which captures the "a dead walker invites a new consumer" worry without
   touching a line the campaign compiles against.
3. **Spike ONE deep gate before committing to a plan for the big four.** The
   §2 ceiling is the plan's only real unknown: if `bound_depth`-scale statements
   re-prove under `mvcgen`+`grind`, the whole estate is class (a) and
   `twinAgrees` is never needed; if they do not, `twinAgrees` becomes the
   central artifact for 671 theorems. **Everything else in this document is
   already measured; this is the one number that is not.** Spike it before
   sequencing the remaining ~1 000 theorems.

---

## §6 WHAT THIS DOCUMENT DOES NOT DECIDE

* When the trunk interpreter's FILES are deleted. They stay while ~15 k lines of
  campaign theorems are stated against them, marked LEGACY with no new
  consumers.
* Whether `twinAgrees` is built — §3 makes that conditional on one spike.
* The re-founding order beyond the top three; the buckets will re-rank once the
  spike lands, and ranking before measuring is the error this repository names
  most often.
