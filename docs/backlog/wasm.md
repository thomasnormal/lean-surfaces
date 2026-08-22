# The WebAssembly lane's backlog

Per-lane backlog, per `docs/family-architecture.md` §9.5. **Appended only by
the Wasm lane.** Ids are `YYYY-MM-DD-wasm-<n>` and need no reservation,
because the lane name makes them unique.

**Everything before 2026-08-22 is in `docs/backlog.md`** and stays there;
this lane's history is **§L71** (the founding charter, commit `f471528`),
and that reference keeps resolving. Migration is append-only and rewrites no
history.

---

## 2026-08-22-wasm-1 — THE SORRY CENSUS: the number that carried the ruling was **5, not 13**, and the whole ledger is ONE corner of the metatheory

Thomas ruled the **soundness** endgame of `docs/wasm-charter.md` §7.4 —
complement the WG's tooling, don't race the conformance incumbent — with the
condition: *census exactly what the obligations contain before promising any
completion date.* Version follows the ruling: **2.0**, the backend's own
proof target. The census is
[docs/wasm-soundness-census.md](../wasm-soundness-census.md); the rows are in
`docs/wasm-sorry-census.json`, taken by `harness/wasm_sorry_census.py`.
**No Lean was executed** (§0/§6 of the census say so precisely), no
completion date appears anywhere, and **nothing was contacted upstream** —
engagement is Thomas's call with the census in hand.

**THE PIN.** `zilinc/spectec` @ **`b399351f98d8a0350d6e818fe53442117cfe5637`**,
branch `lean-backend`, 2026-08-20, author Yong Zheng Yew, subject
`savepoint`. Cloned to **`~/repos/wasm-soundness`** — a durable home, not the
scratchpad, which is not a preference but a lesson: **this lane's entire
working tree was purged mid-session** and survived only because the charter
had been pushed. Licence **Apache-2.0** (the top-level `LICENSE` is a
per-directory MAP and `spectec/` maps to Apache-2.0). `Contributing.md`
defers to `WebAssembly/design`; **no CLA text exists in-repo** and whether one
applies was not investigated, because that would mean outward contact.

**THE HEADLINE: 5 LIVE OBLIGATIONS, NOT 13.** §L71 §8.1 reported 13 from a
textual grep. **Eight of the thirteen are inside `--` comments** — six are a
block of planning notes (`-- case label => sorry`, `-- case frame => sorry`,
…) and two sit in a commented-out proof attempt. A commented-out `sorry` is
**not an obligation**; it is a note about work someone was thinking about.
`harness/wasm_sorry_census.py` strips Lean comments (`--`, nestable `/- … -/`,
doc comments) and string literals *before* looking for the token — the same
discipline `harness/wasm_suite_census.py` applies to `.wast`, for the same
reason — and reports **both** counts, because the delta is the finding.
Double run byte-identical (verified); three refusal paths RUN, not admired
(missing path, zero `.lean`, unterminated block comment).

**AND THE CHARTER'S OTHER FIGURE WAS TRUE BUT MISLEADING.** §L71 also
reported the generated models at "0 `sorry`". Measured: the
`src/temp_zy_dev/wasm{1,2,3}.0.lean` files it cited **do** have 0 — and their
line counts (3051 / 7179 / 11 289) reproduce **exactly** — but those files
emit **no well-formedness theorems at all**. `test-lean/wasm2.0.lean` has
**158**. Worse, the 3.0 output's "0 `sorry` with 975 `_is_wf`" is not proof
either: there `fzero_is_wf` is an **`inductive … : Prop` that takes
well-formedness as a PREMISE** — it proves nothing and cannot fail — while in
`wasm2.0.lean` the same name is a `theorem := sorry`. **"0 sorry"
distinguishes the emission MODE, not the progress.** The lesson is the
instrument lesson: line counts came from `wc` and the obligation count came
from `grep`, and only one of those is a valid instrument for the question
asked.

**THE LEDGER — and it is ONE corner, not five feature gaps.** The dispatch
asked which language feature each represents (reference types? tables? bulk
memory?). **Measured: none of those.** All five are `instrtype_sub`
(hand-written at `typing_lemmas.lean:1015`) — Wasm's **stack-polymorphic
instruction subtyping**, the `t*` frame rule that lets `t1*->t2*` be used
where `t* t1'* -> t* t2'*` is wanted. That is the same `t*` device §L71 §2.2
flagged as the spec's *fifth* nondeterminism, the one living in the **typing**
relation rather than in execution.

| # | theorem | decl | `sorry` | asserts |
| --- | --- | ---: | ---: | --- |
| **O1** | `instrtype_sub_refl` | 1500 | 1505 | reflexivity |
| **O2** | `instr_subtyping_weaken2` | 1507 | 1514 | outputs weaken upward |
| **O3** | `instrtype_sub_trans` | 1516 | 1523 | transitivity |
| **O4** | `instr_subtyping_strengthen2` | 1525 | 1532 | inputs strengthen downward |
| **O5** | `ais_single_typing_inversion` | 1682 | 1865 | single-instruction typing inversion for admin instrs |

O1-O4 are exactly **reflexivity, transitivity and the two variance
directions of one order**. O5 is the consumer.

**THE DEPENDENCY GRAPH, read out of the code rather than guessed.** O5's
`instr` case (L1704) ends `apply instrtype_sub_refl` — it **already calls
O1**. Its `seq`/`inr` branch (L1768) reads `apply instrtype_sub_trans` — it
**already calls O3**, and is otherwise complete. The surviving `sorry` at
L1865 is the **`sub` case**, and the commented-out attempt above it gets to
`obtain ⟨rest_in, rest_out, supplied_in, …⟩ := ft_sub_rel` and stops — it is
destructuring a frame to reassemble it under a weakened/strengthened type,
which is **O2 and O4**. So **O5 is mechanically blocked, not conceptually
open**: its author knew the shape, and the lemmas it applies are the ones
left `sorry`.

**ONE MISSING LEMMA UNLOCKS THREE — AND MATHLIB ALREADY HAS IT.** O2, O3 and
O4 all need the converse of the already-proved `resulttype_sub_app` (L147): a
**split**, `(a ++ b) subs< c → ∃ c₁ c₂, c = c₁ ++ c₂ ∧ a subs< c₁ ∧ b subs< c₂`.
Read at `Mathlib/Data/List/Forall2.lean:190-200`, **`forall₂_take_append` and
`forall₂_drop_append` are exactly that**, witnesses included (`take`/`drop` at
`length l₁`). Since `Resulttype_sub` is generated as *equal lengths +
`Forall₂ Valtype_sub`*, the missing lemma is a **wrapper over two existing
library lemmas**, not new metatheory. That is the census's most
decision-relevant result after the count. (Read-derived: Mathlib's
orientation splits the RIGHT argument; at least one of O2/O4 needs the mirror,
obtainable by symmetry but not verified.) Already proved and available:
`valtype_sub_refl` (L20), `resulttype_sub_refl` (L23), `valtype_sub_trans`
(L112), `resulttype_sub_trans` (L127), `resulttype_sub_app` (L147).

**DOES OUR MACHINERY APPLY? MOSTLY NO, AND THE REASON IS STRUCTURAL.**
**YES**: the `grind` seam — the file already ends `resulttype_sub_app` in
`grind` and uses `aesop` elsewhere, so our accumulated experience is directly
usable; and our proof-hygiene laws (non-vacuity gates, `#print axioms`, zero
`sorry`/`native_decide`, census-first) apply verbatim. **NO**: the frame rule
in `Std/Internal/Do` — that frame is *monadic state*, while `instrtype_sub`'s
"frame" is a **list prefix in a typing judgement**; the word collides, the
concept does not. Also no: `mvcgen`/`+jp` (no program to generate VCs for),
fuel and the `∃`-fuel threshold form, `Run σ α`/world-as-data (there is no
execution at all — this is static typing metatheory). **This is itself a
calibration result**: §L71 §6.4 predicted the cost would move *from specifying
to proving*, and it did — but the proving turns out to be **ordinary**, which
is good for tractability and bad for anyone hoping the family's tooling gives
an edge. The edge here is discipline and instruments, not tactics.

**THE LADDER (inches, NOT dates).** (1) **O1** — the candidate first proof;
(2) **`resulttype_sub_split`** — the highest-leverage single step, unlocking
three; (3) **O3**; (4) **O2 and O4**, duals, one shape proved twice; (5)
**O5's `sub` case**, whose skeleton already exists.

**THE CANDIDATE FIRST PROOF: `instrtype_sub_refl` (O1)** — every lemma it
needs is already proved in the same file; it is the only one behind no
missing lemma; **it already has a consumer** (O5's `instr` case), so closing
it turns a `sorry`-dependent branch into a real one immediately; the proof is
short and its shape is forced (instantiate the frame empty, then three
appeals to `resulttype_sub_refl`); and — after this census — it is a genuine
obligation rather than a comment, which is not a property to take for
granted.

**A SECOND DRIFT THAT CHANGES THE FIELD PICTURE.** The fork carries branches
`aaron/preservation/admin_instructions`, `aaron/subtyping/inversion_lemmas`,
`aaron/subtyping/instr_ok2_inversion_lemmas`,
`aaron/store_extension/reduction`, `antanas/subtyping` and
`inversion_instr_ok`. **Read from branch NAMES only — no branch was
inspected.** They suggest more than one person working on exactly this
corner, possibly on these obligations. **Inch 1's first act must be reading
those branches**, or this lane risks re-proving landed work. It costs a
`git log`.

**CONFIDENCE, priced.** **HIGH (read at the pin)**: the count of 5; the
declarations, statements and comment status; `instrtype_sub`'s definition;
which supporting lemmas are proved; that O5 already calls O1 and O3; that its
surviving `sorry` is the `sub` case; the licence; the line counts; the two
emission modes. **MEDIUM (read-derived judgement)**: every difficulty class,
the ladder, that the split is a thin wrapper, the O1 sketch. **NOT
VERIFIED**: whether the tree **builds at all** at this commit — the branch's
commits are titled `savepoint` and one reads *"remaining issue: deal with
decidable equality"*; whether the `aaron/*` branches already close any of
these; §L71's "26 theorems"; anything about a CLA. **What a build would buy
is bounded**: that the file elaborates and that a proposed proof closes. It
would not change the count, the graph, or the feature analysis — those are
properties of the text.

**OWED, NAMED RATHER THAN DONE.** `docs/wasm-charter.md` §8.1 still reads
"13 `sorry`". It is corrected in the census and cross-referenced there rather
than silently rewritten, **because the charter is the document Thomas took
his ruling from and the correction should be visible as a correction.**

### Triad

**Not run this landing, and the reason is measured rather than asserted.**
This landing adds **four files, three of them new** (`harness/wasm_sorry_census.py`,
`docs/wasm-soundness-census.md`, `docs/wasm-sorry-census.json`,
`docs/backlog/wasm.md`) and **edits no existing file**. The new harness
script is **imported and invoked by nothing** (verified by grep) and is
deliberately not in `tools/ci.sh`, following the rule that keeps
`harness/c_suite_census.py` out of it. **No Lean, no `LeanModels` module, no
`diff_test` row and no `script_corpus` script can be reached by this change**,
so `docs_check` is the only gate it can move — and it passes. Under
amendment 14 (full-tree `lake build` is a quiet-machine-only operation) and
base rule 4 (one triad per landing, never per edit), a full triad here would
be a ~35-minute no-op on a contended machine. **Recorded OWED and runnable on
demand**; §L71's triad (3693 jobs, 73/73, 1394/0/118/1276, 65/0/50/15) is this
lane's last full green.

---

## 2026-08-22-wasm-2 — INCH 1, STEP 1: the four branches are **ISABELLE**, none is merged, and they prove the **ENTIRE LADDER** — so the engagement is a PORT, not a discovery

`2026-08-22-wasm-1` closed by naming a check that had to come first: read the
fork's `aaron/*` and `antanas/*` branches before attempting any obligation, or
risk re-proving landed work. **Done, and it changes the shape of the
engagement for the third time.** No upstream contact of any kind; reading
public branches only.

**FINDING 1 — they are ISABELLE branches, not Lean.** Measured: **0 `.lean`
files, 7-10 `.thy` files** on each. So they **cannot be consumed** by a Lean
lane the way the dispatch's option (1) imagined — there is nothing to take
with attribution, because there is no Lean there.

**FINDING 2 — none of the six is merged into the pin.** `git merge-base
--is-ancestor origin/<b> b399351f` fails for all six. They are all
**June-July 2026**; the `lean-backend` pin is **2026-08-20**. So this is not
work the Lean lane inherited and moved past — it is a parallel effort in
another assistant, on a branch the Lean line never took.

| branch | last commit | author | content |
| --- | --- | --- | --- |
| `aaron/preservation/admin_instructions` | 2026-06-05 | Aaron Lee | 10 `.thy` |
| `antanas/subtyping` | 2026-06-02 | Antanas Kalkauskas | 7 `.thy` |
| `aaron/subtyping/inversion_lemmas` | 2026-06-19 | Aaron Lee | 7 `.thy` |
| `aaron/subtyping/instr_ok2_inversion_lemmas` | 2026-06-26 | Aaron Lee | — |
| `inversion_instr_ok` | 2026-06-28 | Aaron Lee | — |
| `aaron/store_extension/reduction` | 2026-07-21 | Aaron Lee | — |

**FINDING 3 — and it is the one that matters: `isabelle_type_safety_proof/Subtyping_Properties.thy`
PROVES THE WHOLE LADDER.** 189 lines. Its lemma list, read against this
lane's five obligations:

| this lane's obligation | Isabelle counterpart | size |
| --- | --- | ---: |
| **O1** `instrtype_sub_refl` | **`instr_subtyping_refl`** | **3 lines** |
| **O3** `instrtype_sub_trans` | **`instr_subtyping_trans`** | **64 lines**, structured `proof -` |
| **the missing split** | **`Resulttype_sub_split_left`** | **3 lines** |
| **the split's MIRROR** | **`Resulttype_sub_split_right`** | **3 lines** |
| (already proved in Lean) | `Valtype_sub_refl`, `Resulttype_sub_refl`, `Valtype_sub_trans`, `Resulttype_sub_trans`, `Resulttype_sub_append` | 2-5 each |
| (extra, no Lean counterpart yet) | `instr_subtyping_sub_rule`, `instr_subtyping_frame_rule`, `func_sub_app_single`, `Resulttype_sub_empty` | — |

**Every difficulty class in `2026-08-22-wasm-1` §2 is CONFIRMED by an
independent implementation.** O1 really is the cheapest (3 lines there). O3
really is the biggest of O1-O4 (64 lines, the only one needing a structured
proof). The split really is the shared key.

**FINDING 4 — a flagged uncertainty is RESOLVED, and against the guess.** The
census wrote that Mathlib's orientation splits the right argument and *"at
least one of O2/O4 needs the mirrored orientation, obtainable by symmetry but
NOT verified here."* Aaron needed **both** and proved them as **two separate
lemmas** — `Resulttype_sub_split_left` (closing `by (metis list_all2_append2)`)
and `Resulttype_sub_split_right` (closing `by (metis list_all2_append1)`).
**So the mirror is a real second obligation, not a free symmetry.** The
ladder's inch 2 is two lemmas, not one.

**FINDING 5 — the Mathlib route is INDEPENDENTLY CONFIRMED.** Isabelle's
proofs close on **`list_all2_append2` / `list_all2_append1`** — the exact
analogues of Mathlib's `forall₂_take_append` / `forall₂_drop_append` that
`2026-08-22-wasm-1` identified by reading. Two implementations, two libraries,
the same factoring. That is as much corroboration as a read can give.

**FINDING 6 — the supply-chain question the dispatch raised is ANSWERED, and
the answer is "no cost".** `spectec/test-lean/lakefile.lean` reads
`require mathlib from git ".../mathlib4" @ "v4.32.0"`, the manifest pins
mathlib `81a5d257c8e4` alongside aesop/batteries/Qq/plausible, and
`typing_lemmas.lean:1` is `import Mathlib.Tactic`. **The fork's Lean project
already depends on Mathlib**, so citing `forall₂_take_append` adds **nothing**.
The fallback of proving the two witnesses locally is not needed.

**WHAT THIS DOES TO THE ENGAGEMENT — it shrinks again.** `2026-08-22-wasm-1`
found the ledger was one corner rather than five feature gaps. This entry
finds that **that corner is already proved, in another assistant, by the same
project**. The Lean ladder is therefore a **PORT with a known-good proof
structure and confirmed difficulty ordering** — not a discovery, and not
open metatheory. The remaining Lean-side work is translation plus whatever
Lean/Isabelle automation gap shows up (Isabelle's `metis`/`fastforce` closers
have no one-to-one Lean equivalent; `grind`/`aesop` are the candidates, and
the file already uses both).

**Attribution, recorded now rather than at contribution time**: any Lean proof
this lane writes for O1, O3 or the split lemmas follows the structure of
Aaron Lee's `Subtyping_Properties.thy` on
`origin/aaron/subtyping/inversion_lemmas` (`e75dad778`, 2026-06-19), in the
same repository, Apache-2.0.

**BUILD FEASIBILITY (dispatch step 2) — PRICED, NOT YET RUN, and it is not
cheap.** `spectec/test-lean/lean-toolchain` pins **`leanprover/lean4:v4.32.0`**
and **that toolchain is NOT installed** on this box (present: 4.12.0,
4.27.0-rc1, 4.33.0-rc1, 4.33.0-rc2). So verifying the tree builds requires a
**new elan toolchain download plus a fresh Mathlib v4.32.0 cache** — a
different Lean version from lean-surfaces' own, so **amendment 13's
"clone a warm peer's `.lake`" does not apply**: no peer holds a v4.32.0
cache. Disk checked per A11 rule 6: **205 GB free, 78% used** — space is fine.
Load at the time of writing was **27.8**. Recorded as the next gated step
rather than started, because a multi-GB download for a different toolchain
onto a load-28 machine is a coordinator-visible commitment, not a detail.
**The census's read-only findings stand independently of it** — the count,
the ledger, the dependency graph and every finding above are properties of
text, not of a build.

### Triad

**Not run; not applicable.** This landing edits **one file**
(`docs/backlog/wasm.md`) and adds none. No Lean was executed anywhere in this
lane this session. `docs_check` passes.

---

## 2026-08-22-wasm-3 — INCH 1, STEP 2: **the pin does NOT build** — six errors, all in the hand-written proof file, and the model itself is FINE

Coordinator-approved resource spend (recorded per A11 rule 6, and the
approval is the record): **`elan toolchain install leanprover/lean4:v4.32.0`**
— the fork pins that version and this box had 4.12.0 / 4.27.0-rc1 /
4.33.0-rc1 / 4.33.0-rc2 only — then **`lake exe cache get`**, which downloaded
and decompressed **8639 Mathlib olean files, exit 0**. Disk checked before
starting: 205 GB free. A13's warm-peer `.lake` clone genuinely does not apply
across toolchains — no peer holds a v4.32.0 cache — which is why this was a
download rather than a copy. Neither step is CPU contention, so neither took
the lock; **only the build did.**

**THE BUILD RAN UNDER `tools/triad.sh` — this lane's first adoption of the
canonical wrapper**, per A13's directive to drop lane-private scripts.
`--lane wasm --dir <fork>/spectec/test-lean`. Its `--self-test` was run first
(**12 ok, 0 failed**) and the script was checked for lane-specific
assumptions: it makes no git calls and only `cd`s to `--dir`, so it drives a
foreign tree correctly. **Queue behaviour observed and worth recording: the
ticket waited ~49 minutes behind four lanes** (`pyrebuild`, `c`, `sv`, `es`)
at a machine load of only 5-8 — the lock was serializing, not the CPU
saturating. The FIFO worked exactly as designed and the wait was fair.

**THE ANSWER: the tree does NOT build at `b399351f`. Six errors, ALL of them
in `typing_lemmas.lean`:**

```
typing_lemmas.lean:371:8   too many variable names provided
typing_lemmas.lean:380:17  Tactic `rcases` failed
typing_lemmas.lean:537:17  Unknown identifier `cvtop`
typing_lemmas.lean:1035:2  Case tag `SELECT` not found
typing_lemmas.lean:1113:2  Case tag `frame` not found
typing_lemmas.lean:1865:4  No goals to be solved
```

**AND THE MODEL IS FINE — that is the load-bearing half.** Measured from the
build log: `«wasm2.0»` **BUILT** (with warnings, 12s), `custom_notation`
**BUILT**, `ExtendedDeriveDecEq` **BUILT**, `sandbox_5` **BUILT** — and only
`typing_lemmas` failed. **The generated 10 385-line model elaborates; the
hand-written 1865-line proof file does not.** So the SpecTec→Lean backend's
output is in better shape than its proof lane, which is the opposite of what
"savepoint" commit titles might suggest.

**WHAT THE ERRORS MEAN: MODEL DRIFT, not broken proofs.** `Unknown identifier
cvtop`, `Case tag SELECT not found`, `Case tag frame not found` are the
signature of a **proof file written against an older generated model**. The
generator's constructor and case names moved underneath it. That is consistent
with the branch's own commit titles — `savepoint`, `savepoint before laptop
dies, probably good wasm 2.0 model`, `remaining issue: deal with decidable
equality` — and with `2026-08-22-wasm-1`'s LOW-confidence flag, which named
exactly this risk and is now **resolved as: it does not build.**

**A CORRECTION TO THIS LANE'S OWN CENSUS, and it is the sharpest one yet.**
`2026-08-22-wasm-1` published **"5 live obligations"**. That count is a count
of `sorry` tokens **in a file that does not elaborate**, and one of the six
errors is `1865:4: No goals to be solved` — **at the very `sorry` the census
called O5.** "No goals to be solved" at a `sorry` means the preceding tactics
already closed everything there, so **O5's surviving `sorry` is unreachable
as written.** (Whether that is genuine or a cascade from the five earlier
errors is NOT determined here — the earlier failures can change what
elaborates downstream.)

So the honest statement, replacing the census's headline: **the obligation
ledger is not merely small — at this pin it is not yet WELL-DEFINED**, because
the file it lives in does not compile. The count went 13 → 5 → *"5, in a file
that does not build, one of which is unreachable"*. Each step came from a
better instrument than the last: `grep` → a comment-aware scanner → **a
compiler**. That is the census ladder working as intended, and it is why
step 2 was worth the toolchain.

**WHAT SURVIVES THE CORRECTION, unchanged.** Everything in
`2026-08-22-wasm-1` and `-wasm-2` that is a property of *text* rather than of
elaboration: the five theorem statements and their locations; `instrtype_sub`'s
definition; that all five are the stack-polymorphic frame rule and not five
feature gaps; the dependency graph read out of the proof bodies; that Mathlib
is already a dependency; and every finding about Aaron Lee's Isabelle
development, which is a different file in a different assistant.

**CONSEQUENCE FOR THE LADDER — it gets a new inch 0.** Porting into
`typing_lemmas.lean` is not possible while it does not elaborate. But the
model builds, so **a port can live in its own file** depending only on
`«wasm2.0»` and `«custom_notation»` — both of which build. That is what
`SubtypingPort.lean` (written, verification ticket queued at time of writing)
does, and the broken proof file makes that isolation a *feature* rather than a
workaround.

**Still owed and now sharper: whether the fork intends `typing_lemmas.lean` to
build at this commit at all**, or whether it is a scratch file the author
knows is mid-refactor. That is an upstream question, and upstream contact
remains **Thomas's decision** — now with a concrete finding to offer, which is
a better position than the census had.

### Triad

**Not run for lean-surfaces; not applicable.** This landing edits **one file**
(`docs/backlog/wasm.md`) and adds none to this repository. The Lean execution
recorded above was in the **fork's** tree, under a ticket, with
`LEAN_NUM_THREADS=2` and `nice -n 19` via `tools/triad.sh`, and the lock was
released cleanly (`LOCK RELEASED (mine)`). `docs_check` passes.
