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
