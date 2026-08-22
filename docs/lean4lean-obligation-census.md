# The lean4lean OBLIGATION CENSUS — M2

**Status: M2's deliverable.** Thomas ruled the endgame **CONSUME-AND-EXTEND**
(`docs/lean-tier-charter.md` §10.2) — *"no reason to copy lean4lean; if we can
reuse most of it that sounds good."* That ruling changes the question. It is no
longer *how big is the gap*; it is **which specific obligations are open, what
does each need, and which are untouched** — because the untouched ones are the
contribution surface and the in-flight ones are somebody else's work in
progress.

Everything numeric here is produced by `harness/lean4lean_obligation_census.py`
→ `docs/lean4lean-obligation-census.json`, re-derived on every run, with a
`--compare` drift guard. **No claim below is carried over from the M1 charter
without being re-measured against HEAD**, and §1.1 records where that changed an
answer.

Measured at lean4lean **`e0e3f6b`** (2026-08-14), the same commit M1 built green
in 98 s. **No build was taken for this census** — it is a reading instrument.

---

## 1 THE COUNT, and the delta is a finding

| count | value |
| ---: | --- |
| **raw** `sorry`/`admit` tokens (including comments, docstrings, strings) | **138** |
| **real**, after stripping Lean comments and string literals | **113** |
| **comment-only** — the delta | **25** |
| `axiom` declarations | 103 |

**The 25-token delta is why this is an instrument and not a `grep -c`.** A raw
count overstates the real obligation load by **22%**, and the overstatement is
not random: it is concentrated in docstrings and commented-out proof attempts,
i.e. exactly where a project *discusses* its holes. The Wasm lane's lesson
transfers intact.

The stripper handles what a regex cannot: **nested** `/- /- -/ -/` block
comments, `/-- -/` docstrings, `--` line comments, and string literals with
escapes — while preserving line numbers so every obligation still reports a real
`file:line`. It ships with an 11-case self-test (`--selftest`), and the nesting
case is the one a naive implementation gets wrong.

### 1.1 Where the M1 charter was right, and where it was wrong

The dispatch asked for all three M1 figures to be verified against HEAD with the
instrument rather than trusted. Result: **two confirmed, one wrong.**

| M1 charter claim | measured at HEAD | verdict |
| --- | --- | --- |
| 24 shipped-build sorries | **24** | **CONFIRMED** |
| 89 in `Experimental/` | **89** | **CONFIRMED** (24 + 89 = 113) |
| `Theory/Inductive.lean` is a two-stub file | **7 lines, 2 `sorry`s, both `def`s** | **CONFIRMED verbatim** |
| "11 of 24 shipped sorries cluster on projections" | **10** | **WRONG — corrected to 10** |
| partition sizes 3964 / 21531 / 13309 / 664 | identical | **CONFIRMED** |

The proj figure was off by one. The M1 number appears to have counted
`tryEtaStructCore.WF` as proj-named; it is not — though §3.2 shows it *is*
proj-**blocked**, for a reason only reading the executable reveals. The
corrected headline is **10 of 24 named for projections, and 10 blocked by the
projection stub** — the same number arrived at two different ways, which is
coincidence rather than corroboration and is flagged as such.

---

## 2 THE STRUCTURAL FINDING: 24 sorries are 3 missing DEFINITIONS and a cascade

This is the census's main result, and it changes what (b) is buying.

> **Of the 24 open obligations in the proof layer, 3 are `def`s whose body is
> `sorry` — the SPECIFICATION is missing, not the proof. The other 21 are
> theorems, and 13 of those are blocked by one of the 3.**

| partition | value |
| ---: | --- |
| definitional stubs (`def … := sorry`) | **3** |
| proof obligations (`theorem … := sorry`) | **21** |
| — of those, **blocked** by a stub or a sorried lemma | **14** |
| — of those, **independent** | **7** |

The three stubs, and what each costs:

| stub | file | unblocks |
| --- | --- | ---: |
| **`TrProj`** | `Verify/Typing/Expr.lean:67` | **11** |
| `VEnv.addInduct` | `Theory/Inductive.lean:7` | 1 → cascades to `addDecl.WF` |
| `VInductDecl.WF` | `Theory/Inductive.lean:5` | 1 → cascades to `addDecl.WF` |

**`TrProj` alone gates eleven of the twenty-one proof obligations — 52%.** It is
declared as

```lean
def TrProj : ∀ (Γ : List VExpr) (structName : Name) (idx : Nat) (e : VExpr), VExpr → Prop := sorry
```

— a relation that does not exist. The seven `TrProj.*` lemmas in
`Verify/Typing/Lemmas.lean` are therefore not seven hard proofs; they are seven
statements *about nothing*, which typecheck only because their subject is a
`sorry`-backed `Prop`. **Writing `TrProj` is a definition task, not a proof
task**, and it is the single highest-leverage item in the whole census.

The inductive stubs have the same shape one level up: `VInductDecl.WF` and
`VEnv.addInduct` are both `def … := sorry`, so `addInduct_WF` is a theorem about
an undefined function, and `addDecl.WF`'s `inductDecl` case — the capstone — is
blocked behind both. The author's own docstring on `addDecl.WF` says it: *"The
only declaration form still outstanding is inductives, which need a constructive
`AddInduct` model."*

**This reframes (b)'s price.** "24 sorries" sounds like 24 proofs. It is closer
to **3 definitions, 14 downstream proofs that become possible once those exist,
and 7 genuinely independent theorems** — and the definitions are the part where
a spec-mirror discipline (§7.1's 71 cited rules) has most to offer, because the
thesis *states* the inductive rules that `VInductDecl.WF` would have to encode.

---

## 3 THE OBLIGATION TABLE

`S`-rows are definitional stubs; numbered rows are proof obligations.

| # | declaration | file:line | corner | blocked by |
| ---: | --- | --- | --- | --- |
| S1 | **`VInductDecl.WF`** (a `def`) | `Theory/Inductive.lean:5` | inductive-types | — *it is the missing definition* |
| S2 | **`VEnv.addInduct`** (a `def`) | `Theory/Inductive.lean:7` | inductive-types | — *it is the missing definition* |
| S3 | **`TrProj`** (a `def`) | `Verify/Typing/Expr.lean:67` | proj | — *it is the missing definition* |
| 1 | `NormalEq.parRed` | `Theory/Typing/ChurchRosser.lean:1190` | church-rosser | **independent** |
| 2 | `NormalEq.parRed` | `Theory/Typing/ChurchRosser.lean:1209` | church-rosser | **independent** |
| 3 | `addInduct_WF` | `Theory/Typing/InductiveLemmas.lean:10` | inductive-types | `VEnv.addInduct`, `VInductDecl.WF` |
| 4 | `IsDefEqU.sort_inv` | `Theory/Typing/Injectivity.lean:12` | injectivity | **independent** |
| 5 | `IsDefEqU.forallE_inv_stratified` | `Theory/Typing/Injectivity.lean:21` | injectivity | **independent** |
| 6 | `IsDefEqU.sort_forallE_inv` | `Theory/Typing/Injectivity.lean:34` | injectivity | **independent** |
| 7 | `IsDefEqU.weakN_iff` | `Theory/Typing/UniqueTyping.lean:174` | unique-typing | `IsDefEqU.sort_inv`, `IsDefEqU.forallE_inv_stratified` |
| 8 | `addDecl.WF` | `Verify/Environment.lean:236` | environment/addDecl | `addInduct_WF` |
| 9 | `checkPrimitiveDef.WF` | `Verify/Environment/Boundaries.lean:35` | environment/addDecl | **independent** |
| 10 | `inferProj.WF` | `Verify/TypeChecker/InferType.lean:391` | proj | `TrProj` |
| 11 | `tryEtaStructCore.WF` | `Verify/TypeChecker/IsDefEq.lean:227` | defeq | `TrProj` |
| 12 | `isDefEqUnitLike.WF` | `Verify/TypeChecker/IsDefEq.lean:488` | defeq | **independent** |
| 13 | `reduceProjCore.WF` | `Verify/TypeChecker/Reduce.lean:145` | proj | `TrProj` |
| 14 | `reduceRecursor.WF` | `Verify/TypeChecker/WHNF.lean:8` | whnf/reduction | `TrProj` |
| 15 | `TrProj.weak'` | `Verify/Typing/Lemmas.lean:559` | proj | `TrProj` |
| 16 | `TrProj.weak'_inv` | `Verify/Typing/Lemmas.lean:640` | proj | `TrProj` |
| 17 | `TrProj.defeqDFC` | `Verify/Typing/Lemmas.lean:644` | proj | `TrProj` |
| 18 | `TrProj.wf` | `Verify/Typing/Lemmas.lean:810` | proj | `TrProj` |
| 19 | `TrProj.uniq` | `Verify/Typing/Lemmas.lean:855` | proj | `TrProj` |
| 20 | `TrProj.instN` | `Verify/Typing/Lemmas.lean:1157` | proj | `TrProj` |
| 21 | `TrProj.instL` | `Verify/Typing/Lemmas.lean:1426` | proj | `TrProj` |

### 3.1 By feature corner

| corner | obligations |
| --- | ---: |
| **proj** | **10** |
| inductive-types | 3 |
| injectivity | 3 |
| church-rosser | 2 |
| defeq | 2 |
| environment / `addDecl` | 2 |
| whnf / reduction | 1 |
| unique-typing | 1 |

**The corner table found a bug in itself, and it is worth recording** because it
is the same class of error §5.5 exists to prevent. A path-based classifier filed
all seven `TrProj.*` lemmas as **"other"**, because they live in
`Verify/Typing/Lemmas.lean` — a generic filename that says nothing. The census's
single largest cluster was invisible in its own summary table. Name-based rules
now run first. **A corner table that cannot see its own biggest bucket is worse
than no corner table**, and this one was shipped that way for exactly one run.

### 3.2 A dependency the NAMES do not show — found by reading the executable

`tryEtaStructCore.WF` looks independent: its name has no `TrProj` prefix and it
lives in `IsDefEq.lean`. It is not independent. The function it verifies builds
projection terms:

```lean
unless ← isDefEq (.proj fInfo.induct (i - fInfo.numParams) t) args[i] do return false
```

So proving it requires relating an `Expr.proj` to the model — which is `TrProj`,
which is a stub. **A mechanical name-prefix analysis put a blocked theorem at the
top of the candidate list**; only reading the executable caught it. The edge is
now declared in the instrument with that reasoning attached, and the same check
was run against the other candidates: `isDefEqUnitLike` and `reduceRecursor`
**do not** touch `proj` and are genuinely independent.

This is the general caution for (b): **in this repository the dependency graph is
semantic, not nominal.** Any future obligation triage has to read the verified
function, not just the theorem name.

---

## 4 OUR-MACHINERY FIT, honestly

M1 already established the shape (`docs/family-architecture.md` §3.4.1): this
tier's subject is **judgment-shaped, not run-shaped**, so the family's
`SemM`/`Run` substrate does not apply and was never going to. What is left is
ordinary structural metatheory, and the fit is correspondingly plain:

| our machinery | fit here |
| --- | --- |
| `SemM` / `Run σ α` / fuel | **none.** No world, no effects, no schedule (§3.1: zero nondeterminism) |
| `mvcgen` / `@[spec]` | **none.** These are weakest-precondition tools for imperative runs; the obligations are inductive-relation lemmas |
| `omega` | **yes, narrowly** — de Bruijn index arithmetic in the lifting/instantiation lemmas (`weak'`, `instN`) is exactly its domain |
| `grind` | **plausible** for the congruence-closure steps in defeq lemmas; unproven here and should be tried before it is claimed |
| structural induction + `Std` | **the actual work.** These are ordinary Lean 4 metatheory proofs over inductive relations |
| our census/verdict/instrument METHOD | **yes** — and it is the transferable part, as §5.5's manifest already showed |

**The honest summary: we bring discipline and instruments, not tactics.** The
proofs themselves are the same craft Mario is already doing, and claiming our
toolchain gives an edge on them would be the kind of overclaim this repository's
own laws forbid. Where we do have an edge is upstream of the proofs — the cited
rule manifest (§7.4 of the charter), the drift guards, and the census that says
which obligation is worth attacking.

---

## 5 THE CANDIDATE FIRST PROOF

The Wasm-O1 criterion: **the cheapest real obligation that has a waiting
consumer.** Seven obligations are independent; four of them disqualify
themselves.

| candidate | consumers | why it is / is not the first proof |
| --- | ---: | --- |
| `IsDefEqU.sort_inv` | **9** | Most-wanted by far — the keystone of `UniqueTyping`. **DISQUALIFIED — HIGHEST RACE RISK IN THE CENSUS**, and not for the reason the file's docstring suggests. See §6.4. |
| `IsDefEqU.forallE_inv_stratified` | 1 | Same, §6.4. |
| `IsDefEqU.sort_forallE_inv` | 0 | Same, §6.4. |
| `NormalEq.parRed` ×2 | **0** | No consumer anywhere in the tree — scaffolding inside a 1 200-line Church-Rosser development. Fails the criterion outright. |
| `checkPrimitiveDef.WF` | 1 | **DISQUALIFIED — IN FLIGHT.** Its file was created 2026-08-04 by Kim Morrison (PR #28, merged), and open **PR #32** — *updated the day of this census* — is titled *verify primitive-model conservation*. Independently of that, its subject is a 492-line syntactic recognizer: shallow and tedious. Both reasons point the same way. |
| **`isDefEqUnitLike.WF`** | 1 | **RECOMMENDED.** See below. |

### 5.1 Why `isDefEqUnitLike.WF`

> **`theorem isDefEqUnitLike.WF` — `Verify/TypeChecker/IsDefEq.lean:488`.**
> The unit-like (subsingleton) eta rule: if a type is a non-recursive inductive
> with one constructor, no fields and no indices, any two of its inhabitants are
> definitionally equal.

Every signal the census can measure points the same way:

* **The subject is 9 lines.** `isDefEqUnitLike` calls only `whnf`, `inferType`
  and `isDefEqCore` — no recursion of its own, no fuel, no projections.
* **It is genuinely independent**, verified the hard way: its executable does
  **not** touch `.proj`, checked directly and transitively — which is exactly the
  test that eliminated `tryEtaStructCore.WF` and `reduceRecursor.WF` (§3.2).
* **It has a waiting consumer**, `IsDefEq.lean:604`, in the same file.
* **It sits in the densest neighbourhood of proved analogues in the repository**:
  26 theorems in that file, **median proof 15 lines**. `tryStringLitExpansion.WF`
  — a structurally similar "small kernel rule" obligation — sits ten lines above
  it, proved in five.
* **It is a rule this tier already understands.** `unit-like` is one of the 16
  named kernel reduction rules in `docs/lean-kernel-census.json`
  (`is_def_eq_unit_like`, `type_checker.cpp`), so the obligation connects
  directly to the vocabulary census M1 landed.
* **Our machinery genuinely applies**: it is structural induction plus defeq
  congruence — the `grind`/`omega` corner of §4, not the `SemM` corner that does
  not exist here.

**The honest caveat:** one consumer is a thin prize. This is a *first* proof —
chosen to establish that this lane can land a real proof in someone else's
metatheory at all, at a difficulty where failure teaches rather than blocks.
The high-value work is `TrProj`, and §6 says so.

### 5.2 The high-value work is a DEFINITION, and that is the census's advice

If Thomas wants leverage rather than a warm-up, the census is unambiguous:

> **Write `TrProj`.** It is a definition, not a proof; it unblocks **11 of 21**
> proof obligations; it is the construct where §8 of the charter found four
> independent instruments converging; and it is the one place where the thesis
> (§7.1's 71 cited rules) offers **nothing at all** — `proj` is absent from its
> grammar — so the definition has to be *designed*, with the kernel's own
> three-mechanism treatment as the specification.

That is simultaneously the most valuable and the most dangerous item in the
census: valuable because of the 11, dangerous because designing a definition in
someone else's metatheory is precisely the thing to coordinate before starting
rather than after. **§7 records it as needing Thomas's engagement decision
first.**

---

## 6 THE ACTIVE-WORK SPLIT — what is in flight, and what is ours

**Method and its limits.** Public reading only: branches, open and merged PRs,
issues, per-file `git blame` recency, and the paper's stated future work. **No
contact of any kind was made** — engagement is Thomas's decision (§7). And the
probe's own caveat is the important one:

> **Absence of a public reply is NOT evidence of absence of work.** The author
> rebases (an entire logical-relations line landed as fresh SHAs), so
> unpublished local work is invisible to this method. Every "untouched" below
> means *no public evidence*, never *nobody is working on it*.

### 6.1 DO NOT ENTER — visibly in flight

| cluster | evidence |
| --- | --- |
| **inductive types** (`VInductDecl.WF`, `VEnv.addInduct`) | **Open PR #43 "Iota Reduction"** (opened 2026-08-08, updated 2026-08-18) **replaces both stubs with real definitions** and adds ~100 lines |
| **`addDecl` / primitive boundary** | **Open PR #32** (kim-em) — **updated the day of this census**; builds the end-to-end `addDecl` story |
| **injectivity** (`sort_inv`, `forallE_inv_*`) | The author **already solved it in the `SExpr` world** (2026-05-13); porting it is his obvious next move |
| **universe levels** | **11 commits on 2026-08-11 alone**, plus HEAD itself (2026-08-14) — he is working here this month |
| **church-rosser** | Circled by both the author's `.extra` work and PR #43 |

**This is the census's most consequential result for planning**, and it lands
against the charter: **two of the three definitional stubs are already being
written by someone else.** M1's §6.4 called `Theory/Inductive.lean` "the seam"
and the highest-value unwritten artifact in the field. Three weeks later there is
an open PR filling it. A lane that had started there on the strength of the
charter alone would have spent its first milestone duplicating a stranger's
merged work.

### 6.2 UNTOUCHED — the contribution surface, ranked

| rank | cluster | why it is ours |
| ---: | --- | --- |
| **1** | **`TrProj` + its downstream lemmas** | **No branch, no PR, no issue.** The definition has been `sorry` since **2025-05-29 — about 15 months**; three of the dependent lemma sites date to **2023** |
| 2 | `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` | Blame **2025-09-28**, untouched ~11 months, no claimant — but **partly gated on rank 1** |
| 3 | `IsDefEqU.weakN_iff` | Blame **2023-12-16**, the oldest live site — but inherits the injectivity race risk |

**Rank 2's "partly" is exactly the split §3.2 measured**, arrived at
independently from the other direction: `tryEtaStructCore.WF` **is** gated on
`TrProj` (its executable builds `.proj`); `isDefEqUnitLike.WF` **is not**. Two
methods — reading executables here, reading git history there — agree on the
cluster and this census can say precisely which half of it is free.

**So the recommendation of §5.1 survives contact with the activity data**, and is
now better supported than when it was made: `isDefEqUnitLike.WF` is the
independent half of the second-ranked untouched cluster, in a neighbourhood
nobody has touched in eleven months.

### 6.3 Governance — measured, and it belongs in the engagement decision

| observation |
| --- |
| The maintainer has replied to **exactly one of eleven** substantive open PRs (#27). **Nine external proof PRs sit unanswered**, several since 2026-07-05 |
| **Thomas's own issue #16, "Contributing proofs"** — which asks precisely which sorries are unclaimed — has been **open 23 days with zero replies** |
| There is **no published open-problems list**. This census is substituting for one |

The middle row is the one to weigh. **The polite path was already tried, by
Thomas, 23 days before this census, and it produced nothing.** That is not a
complaint — an unfunded personal research project owes nobody triage — but it
does mean a plan that depends on upstream coordination is depending on a channel
with a measured 0-for-1 response rate, and that nine other contributors are in
the same queue.

### 6.4 THE INJECTIVITY TRAP — the docstring is stale and the truth is worse

M1's charter quoted `Injectivity.lean`'s header — *"A bunch of important
structural theorems which we can't prove :("* — and concluded these were the
author's known-hard, therefore-avoid cases. **That reading is wrong, and the
correct one disqualifies them more firmly.**

> **Injectivity is already PROVED, sorry-free, on master** — at
> `Experimental/ShapeLogRelAdequacy.lean:450,455,459`, landed 2026-05-13 on a
> branch whose tip commit reads *"Finished injectivity! 🎉"*.

The three `sorry`s in `Theory/Typing/Injectivity.lean` survive because the proofs
are for the **`SExpr`/stratified** development, and — measured — **`Theory/` and
`Verify/` contain zero `import Lean4Lean.Experimental`**. The two type systems do
not meet. So the open work is not *proving injectivity*; it is **porting it
across the `SExpr`→`VExpr` bridge**, which is the move the author makes whenever
he returns to metatheory, and which he has every advantage in making.

**Two lessons, and both are methodological.**

*A stale docstring nearly set this lane's direction.* The header dates from
before the proof existed. M1 read it as current, and a charter that had acted on
it would have avoided these theorems for a reason that stopped being true three
months earlier — while the *correct* reason to avoid them is stronger.

*The author does not publish linearly.* The `logrel` branch reports as "42
commits ahead of master", which reads like unmerged work. It is not: those
commits were **rebased onto master with new SHAs**, and `logrel`'s tip is
byte-equal in subject and date to a commit already on master. **A branch-ahead
count is not evidence of unmerged work in this repository**, and the census's
"untouched" verdicts inherit that caveat — unpushed local work is invisible to
any public method.

### 6.5 TWO TRAPS FOR ANY FUTURE RUN OF THIS CENSUS

**(1) `sorry` → `axiom` laundering.** The `types2025` branch converts
`VInductDecl.WF`, `addInduct`, `addInduct_WF`, `IsDefEq.uniq`, `sort_inv`,
`forallE_inv`, `sort_forallE_inv` and `weakN_inv` from `sorry` into **`axiom`**,
retaining `-- := sorry` as a comment. **Zero proof content** — it is presentation
hygiene for a paper snapshot.

A `sorry`-counting instrument run against that branch would report a dramatic
improvement that did not happen. **This instrument counts `axiom` declarations
alongside `sorry`/`admit` for exactly this reason** (103 at HEAD), and a future
comparison must read both numbers or be fooled. It is the same failure the
`--compare` audit found elsewhere: an artifact that reads green because it cannot
read anything else.

**(2) Recent file touches that discharge nothing.** Several sorry-bearing files
show August 2026 commit dates, which looks like activity. Measured, those touches
are toolchain bumps, a do-elaborator migration and a namespace move; **the
`sorry` blame dates are the honest signal** and several are from 2023. Any
recency judgement must blame the *site*, not the *file*.

### 6.6 What the two live PRs actually do — and what they leave

Both matter to (b)'s plan, and neither closes the capstone:

* **PR #43 "Iota Reduction"** replaces both `Theory/Inductive.lean` stubs with
  real definitions — `VInductDecl.WF` as a 4-field structure, `addInduct` as a
  real fold — modelling ι as a schematic pattern rule. But its `VInductDecl.WF`
  **does not enforce strict positivity, universe constraints, or recursor
  shape**, it leaves **twelve `IOTA-TODO(soundness)` gaps**, and **`addInduct_WF`
  stays open**.
* **PR #32** (24 247 insertions, updated the day of this census) proves an
  end-to-end `addDecl.WF` — and **explicitly scopes inductives out**:
  `Declaration.SupportedByModel | .inductDecl .. => False`.

> **So the capstone is pincered but not closed: both live efforts deliberately
> leave the inductive case aside.** `addDecl.WF`'s `inductDecl` sorry is
> therefore **AMBIGUOUS** rather than in-flight — its surroundings are being
> rebuilt by two people while the case itself is untouched by both. That is the
> worst kind of target: high value, high churn around it, and a merge conflict
> surface that changes weekly.

---

## 7 WHAT M2 CONCLUDES

### 7.1 The recommendation stands, and is better supported than when it was made

**Candidate first proof: `isDefEqUnitLike.WF`** (§5.1). It is the *independent
half* of the second-ranked untouched cluster — 11 months idle, no claimant, one
waiting consumer, a 9-line subject, and 26 proved analogues in its own file at a
median of 15 lines. Two methods reached it independently: reading executables for
the dependency graph, and reading git history for the activity split.

**The high-value work is `TrProj`** (§5.2), and the activity data promotes it
rather than qualifying it: **rank-1 untouched, no branch, no PR, no issue, the
definition `sorry` for about 15 months, dependent lemmas dating to 2023** — and
it gates **11 of 21** proof obligations.

**One caveat that belongs next to it**: the author *added* a projection sorry on
2026-07-08 (`Verify/TypeChecker/Reduce.lean`). Proj is not abandoned ground; it
is ground he keeps stepping onto and leaving. And `TrProj` is a
**definition-design** task, so a wrong guess is expensive and he may hold
unstated constraints — which is precisely why §7.3 makes it the engagement
question rather than a unilateral start.

### 7.2 The charter's "seam" claim needs amending

M1's §6.4 named `Theory/Inductive.lean` the highest-value unwritten artifact in
the field. **Three weeks later there is an open PR filling it.** The claim was
true when written and is now stale — and the correction is the argument for
running an active-work check *before* choosing a target, not after.

`docs/lean-tier-charter.md` §6.4 should be read with this section beside it. The
seam that is still open is **`TrProj`**, not inductives.

### 7.3 STILL OWED BY THOMAS — sharpened by this census

1. **The engagement decision** (charter §11.4), now with data. The governance
   numbers are not encouraging: **nine external proof PRs unanswered**, one
   maintainer reply across eleven, no published open-problems list, and
   **Thomas's own issue #16 asking exactly this question open 23 days with zero
   replies**. A plan that depends on upstream coordination depends on a channel
   with a measured 0-for-1 response rate.
2. **Whether to start `TrProj` unilaterally.** It is the highest-leverage item
   and the highest design risk, and those are the same fact. The alternative is
   the §5.1 warm-up first, which costs little and answers "can this lane land a
   proof in someone else's metatheory at all".
3. **Whether `Experimental/` is in scope.** 89 of the 113 obligations live there;
   it is CI-gated since 2026-08-03, so it is not abandoned scratch, and eight
   external PRs target it.

### 7.4 WHAT THIS CENSUS DID NOT MEASURE

* **Zulip was not read.** `bugs-found.md` links a soundness thread that may carry
  intent statements. This is the most likely place for undiscovered signal.
* **Unpushed local work is unknowable**, and §6.4 proves the author works that
  way. Every "untouched" means *no public evidence*, never *nobody is working*.
* **No Lean was executed and no build was taken.** Obligation counts are static —
  no `sorry` was verified to compile and no `#print axioms` closure was computed.
  M1 inch 2 already built this commit green in 98 s; that is not re-derived here.
* **PR #43's branch history** was not read — only its merged diff and metadata.
* The paper is **paraphrased and cited by section**; no long passage reproduced.

