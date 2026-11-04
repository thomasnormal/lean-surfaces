# The Wasm soundness engagement: THE OBLIGATION CENSUS

**Status: M2's deliverable. The census IS the milestone — there are no
completion promises in this document, by instruction and by taste.**

Thomas ruled the **soundness** endgame of `docs/wasm-charter.md` §7.4:
complement the working group's tooling rather than race the conformance
incumbent. His condition, applied here: *census exactly what the
obligations contain before promising any completion date.* The version
follows the ruling — **Wasm 2.0**, which is the backend's own proof target.

**Nothing was contacted, upstream or otherwise.** Engagement with the
upstream project is Thomas's decision with this census in hand.

---

## 0 THE PIN, AND WHAT WAS READ VERSUS RUN

| | |
| --- | --- |
| repository | `zilinc/spectec`, branch `lean-backend` |
| durable clone | `~/repos/wasm-soundness/spectec` (NOT scratchpad — a purge took this lane's tree once already) |
| **pinned commit** | **`b399351f98d8a0350d6e818fe53442117cfe5637`** |
| commit date | 2026-08-20 23:00:42 +0800 |
| author | Yong Zheng Yew |
| subject | `savepoint` |
| licence | **Apache-2.0** — the top-level `LICENSE` is a per-directory MAP, and `spectec/` (where every file below lives) maps to Apache-2.0 |
| contribution norms | `Contributing.md` defers to the `WebAssembly/design` repository's guidelines. **No CLA text exists in this repository**; whether one applies was NOT investigated, because that would mean outward contact |

**§5.4a — read versus run.** Everything in this document was obtained by
**READING** files. **No Lean was executed**: no `lake build`, no
`lake env lean`, no proof was checked or attempted. That is deliberate —
the machine is under a build lock and a census of *what obligations say*
does not need a compiler. **Every difficulty class below is therefore a
READING judgement and is marked as such in §6.** The one thing a build
would change is confirming that a proposed proof actually closes; nothing
here claims that.

Verified by reading, in the tree: `grep` for the obligation token, the
enclosing declarations, the definitions those declarations mention, the
already-proved lemmas they can draw on, and the relevant Mathlib API (read
out of `~/repos/lean-surfaces/.lake/packages/mathlib`, which is a read of a
peer's cache, not a build).

---

## 1 THE HEADLINE: THE COUNT IS 5, NOT 13

`docs/wasm-charter.md` §8.1 reported **13 `sorry`s** in the backend's proof
lane, from a textual grep. **The live count is 5.**

`harness/wasm_sorry_census.py` lands with this document. It strips Lean 4
comments (`--` to end of line, nestable `/- … -/`, doc comments) and string
literals *before* looking for the token — the same discipline
`harness/wasm_suite_census.py` applies to `.wast`, and for the same reason:
a scanner that reads commentary as syntax produces a plausible wrong table.

```
test-lean/typing_lemmas.lean :  5 live / 13 raw  (8 commented out)
```

**Eight of the thirteen are inside `--` comments** — six of them a block of
case-name notes (`-- case label => sorry`, `-- case frame => sorry`, …)
that someone wrote while planning an induction, and two inside a
commented-out proof attempt. **A commented-out `sorry` is not a proof
obligation**; it is a note about work someone was thinking about. Counting
it inflates the ledger, and the ledger is what Thomas's ruling rests on.

The instrument reports **both** numbers because the delta is the finding.

### 1.1 The charter's other figure was true and misleading, and here is why

§8.1 also reported the generated models at **0 `sorry`**. Measured, at the
pin:

| file | lines | live `sorry` | `_is_wf` decls |
| --- | ---: | ---: | ---: |
| `src/temp_zy_dev/wasm1.0.lean` | 3051 | **0** | **0** |
| `src/temp_zy_dev/wasm2.0.lean` | 7179 | **0** | **0** |
| `src/temp_zy_dev/wasm3.0.lean` | 11 289 | **0** | **0** |
| `test-lean/wasm2.0.lean` | 10 385 | **158** | 158 |
| `temp-wasm-3/test_spectec_output.lean` | 14 647 | **0** | **975** |
| `test-lean-backend/test_spectec_output.lean` | 18 438 | **365** | 365 |

The charter cited the `src/temp_zy_dev/` files, and its line counts match
them exactly — so the "0 `sorry`" was **literally true of the files it
named**. Those files simply **emit no well-formedness theorems at all**, so
they have no obligations to leave open.

**And the 3.0 output's "0 `sorry` with 975 `_is_wf`" is not proof either.**
Read directly: there, `fzero_is_wf` is

```lean
inductive fzero_is_wf : N → fN → Prop where
  | fzero_is_wf_0 (v_N : N) (ret_val : fN) :
    ret_val = (fzero v_N) → wf_fN v_N ret_val → fzero_is_wf v_N ret_val
```

— an **inductive relation that takes well-formedness as a premise**. It
proves nothing and cannot fail. In `test-lean/wasm2.0.lean` the same name is
a `theorem … := sorry`, which is a genuine obligation. **The backend has two
emission modes, and "0 sorry" distinguishes the mode, not the progress.**

**Consequence for the charter**: §8.1's numbers stand as written but must
never be read as "the generated model is proved". Corrected in §7.

---

## 2 THE OBLIGATION LEDGER — the 5, in full

All five live in `spectec/test-lean/typing_lemmas.lean` (1865 lines).

| # | theorem | decl line | `sorry` line | what it asserts |
| --- | --- | ---: | ---: | --- |
| **O1** | `instrtype_sub_refl` | 1500 | 1505 | `ft instrsub< ft` |
| **O2** | `instr_subtyping_weaken2` | 1507 | 1514 | output type may be weakened upward |
| **O3** | `instrtype_sub_trans` | 1516 | 1523 | `instrsub<` is transitive |
| **O4** | `instr_subtyping_strengthen2` | 1525 | 1532 | input type may be strengthened downward |
| **O5** | `ais_single_typing_inversion` | 1682 | 1865 | inversion: a one-element admin-instruction sequence's typing comes from a single instruction typing, up to `instrsub<` |

### 2.1 THE LANGUAGE FEATURE — and it is ONE, not five

The dispatch asked which feature each obligation represents — reference
types? tables? bulk memory? **Measured: none of those. All five are the
same corner of the metatheory.**

Every one is about `instrtype_sub`, hand-written at `typing_lemmas.lean:1015`:

```lean
def instrtype_sub (original_ft contextualized_ft : functype) : Prop :=
  match original_ft, contextualized_ft with
  | mk_functype (mk_list original_input_type) (mk_list original_output_type),
    mk_functype (mk_list actual_supplied_input_type) (mk_list actual_needed_output_type) =>
    ∃ (rest_in rest_out supplied_in needed_out : List valtype),
      actual_supplied_input_type = rest_in ++ supplied_in
      ∧ actual_needed_output_type = rest_out ++ needed_out
      ∧ (rest_in subs< rest_out)
      ∧ (supplied_in subs< original_input_type)
      ∧ (original_output_type subs< needed_out)
```

This is Wasm's **stack-polymorphic instruction subtyping**: an instruction
typed `t1* -> t2*` may be used where `t* t1'* -> t* t2'*` is wanted, with a
**frame** (`rest_in`/`rest_out`) threaded past it. It is the same `t*`
device `docs/wasm-charter.md` §2.2 flagged as the spec's *fifth*
nondeterminism — the one that lives in the **typing** relation rather than
in execution, and the reason the spec ships a separate validation
*algorithm* in its appendix.

**So the whole open ledger is: the frame rule's structural laws, plus one
inversion lemma that consumes them.** O1-O4 are exactly reflexivity,
transitivity, and the two variance directions of one order. That
concentration is the census's most useful structural result — this is not
five scattered feature gaps, it is one corner.

### 2.2 What each one NEEDS

`Resulttype_sub` (generated, `wasm2.0.lean:7349`) is a clean pointwise
relation — equal lengths plus `Forall₂ Valtype_sub`. The lemmas already
**proved** in the file and available to draw on:

| lemma | line | status |
| --- | ---: | --- |
| `valtype_sub_refl` | 20 | proved |
| `resulttype_sub_refl` | 23 | proved |
| `valtype_sub_trans` | 112 | proved |
| `resulttype_sub_trans` | 127 | proved |
| `resulttype_sub_app` (the `++` direction) | 147 | proved |

**O1 needs nothing that is not already proved.** Instantiate the frame
empty: `rest_in := []`, `rest_out := []`, `supplied_in := original_input`,
`needed_out := original_output`. The three side conditions become
`[] subs< []`, `t1s subs< t1s`, `t2s subs< t2s` — all three are
`resulttype_sub_refl`, and the two equalities are `[] ++ x = x`.

**O2, O3 and O4 share ONE missing lemma**, and it is the converse of the
already-proved `resulttype_sub_app`: a **split**.

> `resulttype_sub_split : (a ++ b) subs< c → ∃ c₁ c₂, c = c₁ ++ c₂ ∧ a subs< c₁ ∧ b subs< c₂`

Each of O2/O3/O4 must take a frame decomposition on one side of a
`subs<` and transport it to the other side; that is precisely a split.
O3 additionally composes two frames, which needs `resulttype_sub_trans`
(proved) once the split is available.

**And the split is not new metatheory — Mathlib already has it**, read at
`Mathlib/Data/List/Forall2.lean:190-200`:

```lean
theorem forall₂_take_append (l : List α) (l₁ l₂ : List β) (h : Forall₂ R l (l₁ ++ l₂)) :
    Forall₂ R (List.take (length l₁) l) l₁
theorem forall₂_drop_append (l : List α) (l₁ l₂ : List β) (h : Forall₂ R l (l₁ ++ l₂)) :
    Forall₂ R (List.drop (length l₁) l) l₂
```

These give both halves **and the witnesses** (`take`/`drop` at
`length l₁`). So `resulttype_sub_split` is a wrapper: unfold
`resulttypeSub`, apply the two Mathlib lemmas, and discharge the length
obligation. **This is the single most decision-relevant finding after the
count**: it downgrades O2/O3/O4 from "needs new metatheory" to "needs a
wrapper around two existing library lemmas".

*Read-derived. The orientation Mathlib provides splits the RIGHT argument
against an append; at least one of O2/O4 needs the mirrored orientation,
obtainable by symmetry but NOT verified here.*

**O5 needs O1-O4 and nothing else.** Its proof is 183 lines and is
**already written except for one case**. Read directly from the tree:

* its `instr` case (L1704) ends `apply instrtype_sub_refl` — **it already
  calls O1**;
* its `seq` case, `inr` branch (L1768) reads `apply instrtype_sub_trans` —
  **it already calls O3**, and that branch is otherwise complete;
* the surviving `sorry` at **L1865 is the `sub` case** — the subsumption
  rule of `Instrs_ok2`. The commented-out attempt immediately above it
  (L1850-1863) gets as far as `obtain ⟨rest_in, rest_out, supplied_in, …⟩
  := ft_sub_rel` and stops — it is destructuring a frame in order to
  re-assemble it under a weakened/strengthened type, which is O2 and O4.

So O5 is **mechanically blocked, not conceptually open**. Its author
already knew the shape; the lemmas it applies are the ones left `sorry`.

### 2.3 The dependency graph

```
                 (Mathlib forall₂_take_append / forall₂_drop_append)
                                    │
                        resulttype_sub_split   ← the one missing lemma
                            ┌───────┼───────┐
                            │       │       │
      O1 ────────────────►  O2      O3      O4
   (independent;            │       │       │
    needs only              └───────┼───────┘
    proved lemmas)                  │
                                    ▼
                                   O5  (capstone; consumes O1,O2,O3,O4)
```

**O1 is a root and unlocks a real consumer immediately** (O5's `instr`
case). **O2/O3/O4 are siblings behind one shared lemma.** **O5 unlocks
nothing** — it is the ledger's only leaf, and it is what the four exist to
serve.

---

## 3 DOES OUR MACHINERY APPLY? — per obligation, honestly

The dispatch asked whether the family's proof stack transfers. **Mostly
no, and the reason is structural rather than incidental.**

| our machinery | applies here? | why |
| --- | --- | --- |
| **`grind` seam** | **YES** | the file already leans on it — `resulttype_sub_app` (L147) ends in `grind`, and `resulttype_sub_trans` and others use `aesop`. Our accumulated `grind` experience is directly usable, and the split lemma is exactly the shape `grind` handles well once the `Forall₂` API is unfolded |
| **the frame rule in `Std/Internal/Do`** | **NO** | that frame rule is about *monadic state* in do-notation. `instrtype_sub`'s "frame" is a **list prefix in a typing judgement** — the word collides, the concept does not. Nothing here is monadic, stateful, or imperative |
| **`mvcgen` / `+jp`** | **NO** | there is no program to generate verification conditions for. These are inductive relations over syntax, not code with control flow |
| **fuel / `∃`-fuel threshold form** | **NO** | no interpreter, no recursion depth, no termination measure |
| **`Run σ α`, world-as-data, effects-as-traces** | **NO** | no execution at all; this is static typing metatheory |
| **non-vacuity gates, `#print axioms`, zero `sorry`/`native_decide`** | **YES** | our proof-hygiene laws apply verbatim and should be imposed on anything this lane contributes |
| **census-first (§L25)** | **YES** | this document is that law applied to someone else's proof lane |

**Per obligation**: O1-O4 are classic structural metatheory — induction
over lists and an inductive relation. The honest answer for all four is
that **the family's distinctive machinery does not help; standard Lean plus
Mathlib's `List.Forall₂` API does**, with `grind` as the closer. O5 is the
same, one layer up: an induction over a typing derivation.

**This is itself a calibration result.** `docs/wasm-charter.md` §6.4
predicted the cost would *move from specifying to proving*. It did, and the
proving turns out to be ordinary — which is good news for tractability and
bad news for anyone hoping the family's tooling gives an edge here. The
edge, if there is one, is discipline and instruments, not tactics.

---

## 4 THE LADDER

Ordered by dependency, then by cost. **Inches, not dates.**

| inch | content | why here |
| ---: | --- | --- |
| **1** | **`instrtype_sub_refl` (O1)** | independent root; every lemma it needs is proved; already called by O5 |
| **2** | **`resulttype_sub_split`** — the missing lemma, as a wrapper over `forall₂_take_append`/`forall₂_drop_append` | unlocks three obligations at once; the highest leverage single step |
| 3 | **`instrtype_sub_trans` (O3)** | split + the proved `resulttype_sub_trans`; O5's `seq` case already applies it |
| 4 | **`instr_subtyping_weaken2` (O2)** and **`instr_subtyping_strengthen2` (O4)** | duals; one shape proved twice |
| 5 | **`ais_single_typing_inversion` (O5)**, `sub` case | the capstone; unblocked once 3-4 land, and its proof skeleton already exists |

### 4.1 THE CANDIDATE FIRST PROOF: `instrtype_sub_refl` (O1)

The hello-world of the engagement, and the reasons are all measured:

1. **Every lemma it needs is already proved in the same file**
   (`resulttype_sub_refl`, L23).
2. **It is independent** — the only one of the five behind no missing
   lemma.
3. **It already has a consumer**: O5's `instr` case ends
   `apply instrtype_sub_refl`, so closing O1 turns a `sorry`-dependent
   branch into a real one immediately.
4. **The proof is short and its shape is forced** — instantiate the frame
   empty, then three appeals to one proved lemma.
5. **It is a genuine obligation, not a comment** — which, after §1, is not
   a property to take for granted.

Sketch, offered as a *reading* and explicitly not as a checked proof:

```lean
theorem instrtype_sub_refl (ft : functype) : ft instrsub< ft := by
  obtain ⟨⟨t1s⟩, ⟨t2s⟩⟩ := ft            -- functype of two mk_list's
  exact ⟨[], [], t1s, t2s, rfl, rfl,
         resulttype_sub_refl [], resulttype_sub_refl t1s, resulttype_sub_refl t2s⟩
```

**Whether that elaborates is exactly what this census did not test** (§0).
The destructuring of `functype`/`list` and the `[] ++ x = x` defeq are the
two places it would plausibly need adjusting.

---

## 5 DRIFT FROM THE CHARTER

| charter §8.1 said | measured at `b399351f` | verdict |
| --- | --- | --- |
| "13 `sorry`" in `typing_lemmas.lean` | **5 live**, 13 raw, 8 commented | **corrected — the number that carried the ruling was 2.6× high** |
| `typing_lemmas.lean` 1865 lines | 1865 | confirmed exactly |
| "26 theorems" | not re-counted this pass | not verified |
| generated models "0 `sorry`" | true of `src/temp_zy_dev/*`; **158 in `test-lean/wasm2.0.lean`** | **true as written, misleading as read** (§1.1) |
| `wasm{1,2,3}.0.lean` = 3051/7179/11 289 lines | 3051/7179/11 289 | confirmed exactly |
| the lane targets **2.0** | `typing_lemmas.lean` imports `«wasm2.0»` | confirmed |

**The charter's line counts were exact and its obligation count was not.**
The difference is that line counts came from `wc` and the obligation count
came from `grep` — and one of those two is a valid instrument for the
question asked.

**A second drift worth recording, because it changes the field picture.**
The fork carries branches named `aaron/preservation/admin_instructions`,
`aaron/subtyping/inversion_lemmas`,
`aaron/subtyping/instr_ok2_inversion_lemmas`,
`aaron/store_extension/reduction`, `antanas/subtyping` and
`inversion_instr_ok`. **Read from branch names only — no branch was
inspected.** They suggest more than one person working on exactly this
corner, possibly including the obligations above. **Before any of the
ladder is attempted, those branches must be read**, or this lane risks
re-proving landed work. That check costs a `git log` and it is the first
thing inch 1 should do.

---

## 6 CONFIDENCE

Per the dispatch's request to price the census's own confidence.

**HIGH — verified by reading the tree at a pinned commit**: the count of 5;
which declarations they sit in; the exact statements; that 8 are commented;
`instrtype_sub`'s definition; which supporting lemmas are already proved;
that O5 already calls O1 and O3; that the surviving `sorry` in O5 is the
`sub` case; the licence; the line counts; the two emission modes.

**MEDIUM — read-derived judgement, not machine-checked**: every difficulty
class in §2 and the ladder in §4; that `resulttype_sub_split` is a thin
wrapper over the two Mathlib lemmas; that O2/O3/O4 need nothing beyond it;
the O1 proof sketch.

**LOW / NOT VERIFIED**: whether the tree **builds at all** at this commit
(the branch's commits are titled `savepoint`, and one is *"remaining issue:
deal with decidable equality"*, which suggests it may not); whether the
`aaron/*` branches already close any of these; whether upstream would want
a contribution; the charter's "26 theorems"; anything about a CLA.

**What a build would buy, and it is bounded**: confirmation that the file
elaborates, and that a proposed proof closes. It would not change the
count, the dependency graph, or the feature analysis — those are properties
of the text.

---

## 7 WHAT LANDED, AND WHAT IS OWED

Landed: `harness/wasm_sorry_census.py` (deterministic — double run
byte-identical, verified; three refusal paths RUN, not admired),
`docs/wasm-sorry-census.json`, this document, and `docs/backlog/wasm.md`.

**Owed, and named rather than done**: `docs/wasm-charter.md` §8.1 still
reads "13 `sorry`". It is corrected *here* and cross-referenced *there*
rather than silently rewritten, because the charter is the document Thomas
took his ruling from and the correction should be visible as a correction.

**No completion promise appears anywhere in this document.** The ladder is
ordered; it is not scheduled.
