# Proof-framework research — the literature behind `mvcgen`, mapped onto our recorded pains

**The question, as Thomas put it:** *"look at the type of research papers mvcgen
is based on. Maybe there are useful ideas that we can add to our framework that
simplifies proofs."*

**What this document is.** A survey with a bill attached. Every idea below is
tied to a pain **this project has already recorded and measured** — a named law,
a numbered incident, a timing. An idea with no pain to attach to is not in the
table, however good the paper. Every claim is sourced; nothing is reproduced
beyond short quoted phrases.

**Evidence levels**, carried through honestly in the house convention of
`docs/litreview/SYNTHESIS.md`:

* **[source]** — read in the pinned toolchain's own Lean source at
  `leanprover/lean4:v4.33.0-rc1`. The strongest grade here, and the only one
  that is about *our* build rather than about a paper.
* **[read]** — primary text read substantially (paper PDF, official reference).
* **[secondary]** — read via faithful restatements, cross-corroborated.
* **[skimmed]** — abstract/search-grade only.

**No Lean was run for this document.** Amendment 11's build lock covers all Lean
and Thomas's training owns the machine. Every Lean-side claim below is either a
**source reading** (grade `[source]`, with file and line) or an **unrun
hypothesis explicitly labelled as one**. Where a proposal needs a measurement to
be believed, the measurement is named as *owed*, not implied — §5.4a's
provenance law, applied to a document that could not measure anything.

---

## THE VERDICT, first

**The literature has good answers for us, and the three best ones are not
purchases.**

1. **Two of the top three findings are facts about our own toolchain, not about
   any paper.** At `v4.33.0-rc1` there are **two** verification-condition
   generators, not one: `mvcgen` over `Std/Do/` (21 files, censused by the
   pilot) and **`vcgen` over `Std/Internal/Do/` (17 more files, censused by
   nobody)** — and the second one ships **a frame rule**
   (`Std/Internal/Do/WP/Frame.lean`), a `@[frameproc]` attribute for frame
   inference, and a tactic grammar carrying `until`, `frames` and `with grind`.
   Separately, `mvcgen` has a `jp` option whose default core describes as
   *"exponential blowup of VCs"* and whose alternative is *"linear in the number
   of control flow splits"* — **and neither of our two sharpest recorded pains
   records which setting it was measured under.** §1.5, §2.1.

2. **Our hardest-won laws are the literature's named theorems, and the
   convergence is the good news.** The altitude law is `mkstruct_conseq` applied
   by hand (§3.5). `PyTriple` is `Std.Do.Triple` (§1.3). The `∃t.∀F≥t` form is
   **Leroy & Grall's `D`**, and their **Lemma 14** collapses it to `∃F` given
   fuel monotonicity — a 2009 theorem that may delete most of the plumbing in
   thirteen files **without changing the model at all** (§4.1). `Kont` is
   McBride's free monad of recursive calls (§1.4). Our verdict taxonomy is
   `□`/`♢` over one Outcome Logic triple, and DIVERGE-with-witness has a name we
   were not using — the **Lisbon triple** (§5.3).

3. **The one big build the survey endorses is gated, not recommended.**
   Characteristic formulae (`wpgen` + `mkstruct`, the SLF/CakeML *verified*
   design, never CFML's axiom-emitting tool) are the only technique that is
   **linear AND lossless**, and they are the structural fix to the deep-gate
   ceiling. But the price is **1 100–2 300 lines**, much of what they buy may
   already be in `Std/Internal/Do/`, and a 150-line spike decides it. §3.

4. **Two proposals the brief expected are refused, and refused on measurement.**
   Interaction trees would **break kernel-reducible runs** — and in Lean the
   fuel-free model is literally a quotient of a fuel-indexed tower
   (`MvQPF.Cofix` over `{approx : ∀ n, CofixA F n // AllAgree}`), so it is not
   even an escape. §4.3. And relational Hoare logic is aimed at *two programs
   under one semantics*, where we have *one program under two semantics*; its
   fallback rule `SeqProd` **is** the two-proofs-plus-a-bridge cost we are
   trying to reduce. §6.2.

5. **One paper argues we should not have the problem at all**, and it describes
   our architecture as the good one: CakeML's *Functional Big-Step Semantics*
   (ESOP 2016) makes the **clocked interpreter the official semantics** for
   every intermediate language, and reports better induction theorems and
   symbolic evaluation by rewriting as the payoff. **Our fuel index is a
   published design choice, not an apology.** §6.5.

6. **And one recorded theorem is currently false as stated.** *"∀ schedules
   produce the same outcome"* is **not** a theorem about the scheduler; it is a
   theorem about **race-free designs**, because SystemVerilog deliberately
   leaves same-region races unspecified. `RaceFree` is half the content and
   belongs in the statement from day one — which is §0.1 principle I pointed at
   our own future work. §7.4.

**The top three, priced, are in §9. The full table is §8. What this survey did
not do is §11, and it should be read.**

---

## §0 THE PAIN LEDGER — what we are shopping for

Everything in this survey is bought against one of these. The ledger is the
spine; the papers are the catalogue.

| # | the pain | where recorded | the number |
|---|---|---|---|
| **P1** | **The deep-gate ceiling.** A four-deep expression gate closes in **568 ms** against the shallow twin and **does not close at all** against the faithful interpreter. | `docs/python-monadic-rebuild.md` §3.1; `docs/family-architecture.md` §3.4 (L1208) | 568 ms → **no close at 8 M heartbeats (~14 min), `timeout at whnf`**; 4 M / ~10 min after two arm lemmas; 4 M again with `grind` wired |
| **P2** | **The unstateable lemma.** `mvcgen` splits an inner `match` **without retaining the discriminant equation**, so unreachable arms arrive as bare `⊢ False` with nothing to refute them. `evalOpen_name_global` *cannot be stated*. | `docs/python-monadic-rebuild.md` §3.1; `docs/python-refounding-plan.md` §2 caveat | the blocker is in **VC generation**, not discharge — `grind` never gets that far |
| **P3** | **The ∃-fuel family claim is outside the WP layer.** `∃ t, ∀ F ≥ t, run F = .ok w v` is neither produced nor consumed by any WP calculus; it is assembled by hand at every fuel-recursive point. | `docs/mvcgen-pilot.md` §2 Route B; `docs/family-architecture.md` §3.4 (L1232–1248) | mvcgen returns the goal **unchanged after 1 m 31 s** at symbolic fuel; **13 files** carry the fuel-family shape |
| **P4** | **Hand-rolled framing, and it is the residue that actually resists.** §L80: *"what actually resists is a **locality fact that nobody had written down**"* — that the inner generator's steps preserve the `pst` slot. The reason it is not derivable is stated exactly: `IterSteps` *"says nothing about what a step does to slots it did not touch."* | `docs/backlog.md` §L80 (L19710–19736); `LeanModels/Python/DictCalc.lean` (825 lines / 43 theorems) | `order_genexp.lean` **14 s → 43 s**, essentially all of it the frame chain's induction; ~18 of 47 `DictCalc` theorems subsumable, **~29 ours permanently** |
| **P4b** | **The frame tower does not collapse.** *"`cap`, `move_depth`, `score`, `live` are four different keys, so `Env.set_set` never fires and every later gate's lookups are `Env.lookup_set_ne` through the ones before it."* | `docs/backlog/sunfish-rtrack.md` L54–57 | quadratic disjointness bookkeeping, *"mechanical, not free"* |
| **P5** | **`Triple` does not frame the state.** A read-only primitive must *say* it leaves the state unchanged, by pinning the pre-state. | `docs/mvcgen-pilot.md` §3.3 (NEW law); `docs/family-architecture.md` L1263–1264 | an unframed `get!_spec` leaves an unprovable `s✝ = s✝¹` |
| **P6** | **`twinAgrees` — the unpaid adequacy bill.** Any second semantics owes a whole-interpreter induction, and the differential corpus does not discharge it. | `docs/mvcgen-pilot.md` §5.1; `docs/family-architecture.md` L1333–1334 | transport crossover ≈ **100 theorems/file**; four files carry **671 theorems / ~14 000 lines** |
| **P7** | **The ∀-schedule claim has no proof form.** Concurrency tiers need "every admissible schedule", and the schedule space cannot be enumerated. | `docs/family-architecture.md` §3.6 piece 4 | mover lemmas are named as tier 2 of three; **one parenthetical Lipton citation in the whole repo** (L1863) |
| **P8** | **Verdict taxonomy is home-grown.** ∀-schedule MATCH / membership sites / DIVERGE-with-witness / counterexample-schedule `#guard` were invented without literature guidance. | `docs/family-architecture.md` §3.6 pieces 2 and 4; §4.3, §5.2 | zero repo-wide hits for `outcome logic` or `incorrectness` |
| **P9** | **The cycle-model → scheduler projection.** SV has an abstract cycle model and a concrete event-region scheduler and owes an agreement proof. | `docs/sv-r1-scheduler.md`, `docs/family-architecture.md` §3.6 | — |
| **P10** | **Loop annotation burden.** Every loop needs a hand-written invariant and measure; `mvcgen invariants?` produces a skeleton that by construction cannot close. | `docs/mvcgen-pilot.md` §1.5; Lean reference | 6 goals per unbounded `while`, one-to-one with `py_vcgen`'s |
| **P11** | **VACUITY, twice, on the campaign's own target.** `BoundRefines` was **FALSE** at every depth (`not_boundRefines`, 20 lines), and then the strengthened step was **VACUOUS** — `recursionStep_vacuous : RecursionStep V` is a one-liner for every `V`. *"the campaign's own success criterion stopped being able to fail."* | `docs/backlog.md` §L26 (L10168–10214), §L27 finding 4 (L10428–10431) | 3 further holes of the same shape at L10209–10214 |
| **P12** | **The kernel wall.** `initWorld sunfish` cannot be reduced by kernel `rfl`; one iteration of one statement costs **138 s / 6.1 GB, OOM-killed**. Compiled, the same initializer is **~0.35 s**. And *"fuel is not the driver"*. | `docs/backlog.md` §L11/§L12 (L8085–8235) | statement 8 **627 s, OOM**; the wall is **inside one statement**, below the available chop granularity |

> Three of these — **P1, P2, P3** — are the same wound seen from three angles:
> **the interpreter is a deep embedding and the proof pays for its control flow
> every time.** That is the thread the top-3 pulls on.

---

## §1 mvcgen's lineage — what we reinvented, and the one thing its model cannot say

### 1.1 The model at the pin, read from the source

Before asking what the papers offer, it is worth being exact about what
`Std.Do` *is*, because two of this survey's conclusions turn on details that the
documentation does not state. All of §1.1 is grade **[source]**.

| piece | definition at the pin | file |
|---|---|---|
| `SPred σs` | `SVal σs (ULift Prop)` — a predicate **curried over a list of state types** | `Std/Do/SPred/SPred.lean:32` |
| its connectives | `and`, `or`, `not`, `imp` — **ordinary, pointwise** | `Std/Do/SPred/SPred.lean:88–120` |
| `PostShape` | `pure \| arg (σ : Type) \| except (ε : Type)` | `Std/Do/PostCond.lean:52–66` |
| `Assertion ps` | `SPred (PostShape.args ps)` — **`.except` layers discarded** | `Std/Do/PostCond.lean:88` |
| `ExceptConds ps` | one failure barrel per `.except` layer, each seeing only the states **inside** it | `Std/Do/PostCond.lean:104–108` |
| `PredTrans ps α` | a postcondition transformer that is **conjunctive**, hence monotone | `Std/Do/PredTrans.lean:59–82` |
| `WP m ps` | interprets `x : m α` as a `PredTrans ps α` | `Std/Do/WP/Basic.lean:25–55` |
| `WPMonad` | asserts that interpretation **distributes over the monad operations** | `Std/Do/WP/Basic.lean` |
| `Triple x P Q` | `P ⊢ₛ wp⟦x⟧ Q` | `Std/Do/Triple/Basic.lean:31` |

**Two findings that matter, neither of them in the docs.**

**(i) `SPred` is not a separation logic.** It is a *state-indexed* predicate with
pointwise `∧`/`∨`/`¬`/`→`. There is no separating conjunction, no magic wand, no
`emp`, no later modality, no step-indexing — a grep for `sep`, `wand`, `emp`,
`later`, `BI`, `resource algebra` across all 21 files of `Std/Do/` returns
nothing but the word "separating" inside an unrelated docstring
(`Std/Do/Triple/Basic.lean:106`). **Whatever `Std.Do` gives us, it does not give
us a frame rule over the heap.**

> **Read §2.1 before concluding anything from that.** The sentence above is true
> of `Std.Do` and **false of the pin**: `Std/Internal/Do/` — a *second*,
> unrecorded VC-generator hierarchy shipped at the same toolchain — contains
> `WP/Frame.lean` and a `@[frameproc]` attribute. This is the survey's headline
> finding and it is a fact about our own build, not about a paper.

**(ii) What `Std.Do` calls "frame" is pure-hypothesis framing, not heap
framing.** `Lean/Elab/Tactic/Do/ProofMode/Frame.lean` synthesises a `HasFrame`
instance over a **conjunction** of hypotheses; the official tutorial states the
intent exactly — *"Hypotheses in the Lean context are part of the immutable
frame of the stateful logic, because in contrast to stateful hypotheses they
survive the rule of consequence"* [read]. `mframe` moves `⌜p⌝` facts out to the
Lean context and back. Useful, and entirely orthogonal to P4.

### 1.2 The lineage, precisely

`Std.Do` is a **Dijkstra monad**, presented the way the 2019 generalisation says
you should present one, with an **Iris Proof Mode** front end bolted on. Both
halves are documented, and only the second is documented *by the Lean project*.

**The specification half.** "Dijkstra Monads for All" (Kenji Maillard, Danel
Ahman, Robert Atkey, Guido Martínez, Cătălin Hriţcu, Exequiel Rivas, Éric
Tanter; *PACMPL* 3(ICFP), Article 104, 2019) proves that **any monad morphism
from a computational monad to a specification monad induces a Dijkstra monad**,
and that a wide family of specification monads is obtained by applying monad
transformers to base specification monads — predicate transformers among them
[read, abstract + venue verified]. `WP`/`WPMonad` is *precisely* that shape:
`WP m ps` is the map into the specification monad `PredTrans ps`, and `WPMonad`
is the assertion that the map is a monad morphism. The predecessor, "Dijkstra
Monads for Free" (Ahman, Hriţcu, Maillard, Martínez, Plotkin, Protzenko,
Rastogi, Swamy; POPL 2017), derives Dijkstra monads by CPS-translating the
computational effect, and names the tool family this line serves: **F\*, Hoare
Type Theory, and Ynot** [secondary]. The Hoare-monad root is Nanevski, Morrisett
& Birkedal, "Polymorphism and Separation in Hoare Type Theory" (ICFP 2006; JFP
2008), implemented as **Ynot** (Nanevski, Morrisett, Shinnar, Govereau,
Birkedal, ICFP 2008) [secondary]. Behind all of it is Dijkstra's own predicate
transformer (`wp`) — the reason `PredTrans` carries a **conjunctivity** field is
that conjunctivity (and hence monotonicity) is the healthiness condition of that
calculus.

The closest single paper to what `Std.Do` actually does, however, is **Wouter
Swierstra and Tim Baanen, "A Predicate Transformer Semantics for Effects
(Functional Pearl)", *PACMPL* 3(ICFP), Article 103, 2019, DOI
10.1145/3341707** [read, primary PDF]. It defines `wp` as a **fold over a free
monad** — *"By defining these semantics as a fold over the free monad, we can
establish compositionality results, allowing us to decompose the verification of
a large program into smaller parts"* — for exceptions (§3), state (§4),
non-determinism (§5) and **general recursion (§6)**. §6 is the one that matters
to us and it gets its own subsection below.

**The user-interface half, and the Lean project says so.** The official tutorial
states: *"The proof mode was adapted in large part from its Lean clone,
[`iris-lean`]"* [read]. That is corroborated in the source: the proof-mode
tactic set is IPM's — `Intro`, `Cases`, `Frame`, `Specialize`, `Revert`,
`Focus`, `Pure`, `Exfalso`, `LeftRight` — and
`Lean/Elab/Tactic/Do/ProofMode/Frame.lean` is **Copyright (c) 2025 Lars
König**, while `Std/Do/SPred/Laws.lean` and `DerivedLaws.lean` are authored
"Lars König, Mario Carneiro, Sebastian Graf" [source]. `iris-lean`
(`leanprover-community/iris-lean`) began as König's KIT master's thesis, a Lean
4 port of Iris's separation-logic interface and chiefly of **MoSeL**, the
IPM front end [secondary]. The papers behind that UI are Krebbers, Timany &
Birkedal, "Interactive proofs in higher-order concurrent separation logic"
(POPL 2017) and Krebbers, Jourdan, Jung, Tassarotti, Kaiser, Timany,
Charguéraud & Dreyer, "MoSeL: a general, extensible modal framework for
interactive proofs in separation logic" (ICFP 2018) [skimmed].

> **The lineage in one line: `Std.Do` took Iris's *ergonomics* and Dijkstra's
> *model*, and left Iris's *separating conjunction* behind.** That is a coherent
> design — it is what makes `WPMonad` synthesise for our stack with zero
> instances written — and it is exactly why P4 is still ours to pay.

### 1.3 What `PyTriple`/`VCGen` reinvented — and it is now priced

The refounding plan's own table already reaches this conclusion; the survey
confirms it from the other side and adds the names.

| ours | the standard object | evidence |
|---|---|---|
| `PyTriple m P ss Q` | `Std.Do.Triple` over a Dijkstra monad | pilot §2 iso, "a hand-rolled stand-in"; **546 lines of `VC.lean` define what one core word means** |
| `PyPost`'s five flow arms | `PostCond` + a flow **sum on the success barrel** — core's own idiom (`Spec.repeatM`'s `α ⊕ β` cursor) | pilot §5.1 |
| `py_vcgen`'s loop interface | core's six `Spec.repeatM` goals | pilot §1.5: *"The correspondence is one-to-one"* |
| **altitude lemmas** | `@[spec]` triples over named primitives | pilot §3.3: **259+ VCs unfolded vs 12 behind specs** |
| the need to pin the pre-state (P5) | `Triple.observe`, which Std ships | pilot §3.3 |
| `EvalsTo`/`EvalsIn` | plain `Triple` — **with no threshold at all**, because `evalOpen` is fuel-free | refounding plan §2(c2) |

**Five replace, six re-define, zero preserve** is the refounding plan's own
count, and §0.1's trust argument for doing it is the strongest sentence in that
document: every hand-rolled word deleted from a **statement** is one fewer
definition a reader must audit. The survey adds nothing to that verdict except
the names of the objects and the confidence that they are the standard ones.

### 1.4 What the model CANNOT say — P3, and what the literature actually offers

`Triple` is **unary on one program**. `fuelMono` and `∃ t, ∀ F ≥ t, …` are
claims about a **family indexed by fuel**. No amount of `@[spec]` coverage
bridges that, and the pilot measured the wall: at symbolic `F`, mvcgen returns
the goal unchanged after 1 m 31 s. So: *is there a termination/fuel-aware WP in
the literature?* Two answers, and they are different in kind.

#### (a) Swierstra & Baanen §6 — a fuel-free WP whose soundness is stated against a fuel-driven runner

This is the closest thing in print to the shape we want, and it is worth stating
in their notation because the correspondence to our tree is almost embarrassing.

* A general-recursive function of type `I → O` is not defined; instead its
  **call graph** is represented in a free monad, `I ⇝ O := (i : I) → Free I O (O i)`,
  with a smart constructor `call : (i : I) → Free I O (O i)`. They credit the
  technique to **Conor McBride, "Turing-Completeness Totally Free" (MPC 2015,
  LNCS 9129)**, which shows general recursion is the free monad over the effect
  *"make a recursive call"*, with semantics supplied afterwards by monad
  morphisms [read §6; McBride skimmed]. **This is our `Kont`.** `Kont` is
  described in `docs/python-monadic-rebuild.md` §2 as *"the defunctionalized
  fuel boundary"* and generalised as *"a **recursion-knot boundary**"* — which
  is McBride's construction, arrived at independently and for the same reason.
* The predicate transformer for such a Kleisli arrow requires a **specification
  as an argument** — `wpRec spec f P i = wpSpec spec P i ∧ invariant i spec (f i)`
  — and the paper says why, in a sentence that is our P10 exactly: *"This is
  analogous to how imperative programs require an explicit loop invariant:
  assigning semantics to recursive functions requires an explicit
  specification."*
* **Soundness is proved against a "petrol-driven semantics"**:
  `petrol : (f : I ⇝ O) → Free I O a → Nat → Partial a`, which unfolds `f` once
  per unit and **aborts at zero**. The theorem is
  `soundness : (∀ i → wpRec spec f P i) → ∀ n i → mayPT (P i) (petrol f (f i) n)`.

> **That is the "13 files restated against a fuel-free model, connected by one
> theorem" shape, in print, with the theorem written down.** Their `petrol` is
> our fuel; their `Free I O` is our `Kont`; their `wpRec` is a WP that never
> mentions fuel.

**And here is the honest half, which is why this is a *pilot* and not an
*adopt*.** Their soundness is **partial correctness only**. `mayPT` is defined
so that `mayPT P (Step Abort _) = ⊤` — *running out of petrol satisfies
everything*. The theorem therefore reads "if the petrol run produces a result,
the result is correct"; it **never yields `∃ t`**. Our form is
`∃ t, ∀ F ≥ t, run F = .ok w v` — a claim that a threshold *exists*, i.e. a
termination claim. `wpRec` gives us the `∀ F ≥ t, … correct` half for free and
declines the `∃ t` half by construction. That is a real reduction of the bill —
it is exactly the half that costs 13 files' worth of per-node threshold algebra
— but it is not the whole bill, and anyone who says otherwise has not read §6's
last paragraph, which lists bounding the iterations, a coinductive fixpoint
(citing **Capretta 2005**), well-foundedness, and Bove–Capretta as the *separate*
techniques needed to recover totality.

#### (b) Time credits — the literature's fuel-aware WP, and its price is a BI

There *is* a program logic in which the fuel is **inside** the assertion, and it
is a good one.

* **Robert Atkey, "Amortised Resource Analysis with Separation Logic" (ESOP
  2010; journal version in LMCS)** introduces the **time credit** assertion: a
  consumable separation-logic resource that "pays" for steps of execution
  [secondary].
* **Arthur Charguéraud & François Pottier, "Verifying the Correctness and
  Amortized Complexity of a Union-Find Implementation in Separation Logic with
  Time Credits" (*JAR* 62, 2019)** is the practical demonstration: CFML extended
  with time credits, one specification covering correctness *and* complexity
  [secondary]. The companion "A Fistful of Dollars: Formalizing Asymptotic
  Complexity Claims" (Guéneau, Charguéraud, Pottier, ESOP 2018) adds the big-O
  layer [skimmed].
* **Glen Mével, Jacques-Henri Jourdan & François Pottier, "Time Credits and Time
  Receipts in Iris" (ESOP 2019)** is the machine-checked Iris version, and
  supplies the dual: **credits `$n` are an upper bound on cost; receipts are a
  lower bound** [secondary].

The mapping is exact and, as far as I can find, nobody has written it down for a
fuel-indexed interpreter: **a threshold `t` is a bill of `$t`, and threshold
composition is credit addition.** Every `execStmts_mono` / `callIn_of_…` /
`execWhile_at_least` lemma we hand-write is an instance of `$ (n+m) ≡ $n ∗ $m`
plus the frame rule.

**The price is the reason this is not the top-3 answer.** Splitting `$n` needs
`∗`; `∗` needs a BI; `Std.Do`'s `SPred` has none (§1.1(i)). So time credits are
**not an alternative to §2 — they are an application of it**, and they should be
read as the strongest single *argument* for a framing layer rather than as an
independent proposal. Recorded here so that if §2 is ever taken, this is the
second thing it buys.

#### (c) A vocabulary note, offered as vocabulary only

Fuel monotonicity is the *dual* of step-indexing's downward closure (Appel &
McAllester, "An indexed model of recursive types for foundational proof-carrying
code", *TOPLAS* 23(5), 2001 [skimmed]): a step-indexed predicate holds at fewer
steps, our fuel predicate holds at more fuel. This is a naming convenience, not
a technique; recorded so a future reader is not tempted to think there is
machinery here that we are missing. **There is not.**

### 1.5 THE SPLITTER, read at the pin — P1 and P2 are two ends of ONE DOCUMENTED KNOB

This is the survey's most actionable finding and it did not come from a paper.
It came from reading `Std.Do`'s splitter at the pin, and it says that our two
sharpest pains are **the two settings of a boolean that Lean documents and that
we have never set**.

**`mvcgen` has a `jp` option, and its default is the exponential one.** All
`[source]`, at `leanprover--lean4---v4.33.0-rc1/src/lean/`:

`Std/Tactic/Do/Syntax.lean:36–43` — the config field, with core's own docstring:

> If `false` (the default), then we aggressively split `if` and `match`
> statements and inline join points unconditionally. **For some programs this
> causes exponential blowup of VCs.** Set this flag to choose a more
> conservative (but **slightly lossy**) encoding that traverses every join point
> only once and yields a formula the size of which is **linear in the number of
> control flow splits**.

```
jp : Bool := false
```

`Lean/Elab/Tactic/Do/VCGen.lean:111` gates the join-point path on
`(← read).config.jp`; the comment at `VCGen.lean:116` reads *"if, dite and
match-expressions (without `+jp` which is handled by `onJoinPoint`)"*.

**Now map that onto the ledger.**

| knob | what core says | our pain |
|---|---|---|
| **`jp := false`** (the default we have always run) | *"we aggressively split … and inline join points unconditionally. For some programs this causes **exponential blowup of VCs**."* | **P1** — the deep-gate ceiling. A four-deep gate is `2⁴`; 8 M heartbeats and ~14 minutes is what exponential looks like |
| **`+jp`** | *"more conservative (but **slightly lossy**) … **linear** in the number of control flow splits"* | **P2** — *lossy* is the discriminant. See below |

**And the lossiness has a location.** On the `+jp` path,
`VCGen.lean:253` builds the per-alternative predicate with
`info.splitWith (mkSort .zero) …` and **no `useSplitter` argument**, so it
defaults to `false`; `Split.lean:189` wires `addEqualities := useSplitter`, so
the discriminant equations are **not requested**. And `mkJoinGoal`
(`VCGen.lean:240–245`) sets `hyps := emptyHyp uWP σs` with the source comment
*"we only take 4 args and **clear the stateful hypothesis of the goal**"*. For
`ite`, `Split.lean:145–147` passes `fields := #[]` when `useSplitter` is
false — **no `h : c` in the true arm**. Meanwhile the *non*-`+jp` path
(`VCGen.lean:191`) passes `useSplitter := true`, which *does* request the
equalities via core's `MatcherApp.transform`
(`Lean/Meta/Match/MatcherApp/Transform.lean:258`, *"equalities connecting the
discriminant to the parameters of the alternative"*). Also relevant:
`Split.lean:107–110` abstracts a matcher with an explicitly **non-dependent
motive** — the source comment is literally `-- Non-dependent motive:
fun _ ... _ => mα` — which is the mechanism by which an alternative forgets
which discriminant produced it.

**The hypothesis, stated as one, and flagged unrun under Amendment 11:**

> `mvcgen`'s two encodings are **lossless-and-exponential** (default) versus
> **linear-and-lossy** (`+jp`), and our two recorded pains are one measurement
> of each. P1 was measured on the default. P2 — *"the splitter drops the
> discriminant … the two unreachable branches arrive as bare `⊢ False`"* — is
> the documented lossiness of `+jp`, or of the inlined join point's
> hypothesis-clearing, and **not a bug**.

**This is §5.4a's provenance law, applied to a tactic option.** A number carries
the state it was measured in, and *the state includes the tactic's
configuration*. Neither recorded measurement names its `jp` setting, so we do
not currently know whether the four-deep gate has ever been tried on the linear
encoding. **That is a one-token experiment against a fourteen-minute wall.**

**Verdict: ADOPT-NOW (as an action, not as a technique).** Two runs and a note:
re-measure the four-deep gate with `mvcgen (config := { jp := true })`, and
write the twenty-line repro that isolates the discriminant loss. If `+jp` closes
the gate, P1 dissolves for the price of one token. If it closes the gate but
strands unreachable arms at `⊢ False`, then P1 and P2 are the same trade-off and
**§3's characteristic formulae are the design that escapes it** — see §3.6.

* **Price.** Two `lake env lean` runs on the existing gate file plus a ~20-line
  repro, out of the pinned build by construction like the pilot's.
* **Blocked by.** Amendment 11 — one ticket, and it is the **cheapest ticket in
  this document by orders of magnitude.**
* **Risk.** `+jp` may not help; the lossiness may bite exactly where the gate
  needs the discriminant. Then the result is a *characterised* wall rather than
  an unexplained one, plus a precise upstream bug report. Upstream is live in
  this area — Lean 4.28.0 carries `#11698` (*"makes `mvcgen` early return after
  simplifying discriminants, avoiding a rewrite on an ill-formed match"*) and
  two open RFCs sit adjacent (`#9363` *"`mvcgen` should 'purify' any emitted
  stateful subgoals"*; `#9364` binders for `Std.Do.Assertion`) [skimmed].
* **What it does NOT weaken.** Nothing. The vcgen is LIBRARY under §0.1's trust
  table; a tactic option cannot make any statement weaker. But note the flip
  side and record it: **a lossy encoding can make a proof go through that a
  lossless one would not** only by *strengthening* the hypotheses handed to the
  arm, never by weakening the theorem — `+jp` is documented as conservative,
  i.e. it may fail to prove, not prove something false.

---

## §2 Separation logic and the frame rule — and a second VC generator sitting in our own pin

**The pains:** P4 (the §L80 locality residue nobody had written down), P4b (the
four-`Env.set` tower), P5 (`Triple` does not frame the state).

### 2.1 THE FINDING — and it is about our toolchain, not about a paper

The brief asked whether a BI-style frame rule or a modifies-clause discipline is
better priced for us. **Both answers are overtaken by a fact about the pin that
no lane has recorded**, and this section leads with it because it is the most
consequential `[source]` result in the document.

**At `leanprover/lean4:v4.33.0-rc1` there are TWO verification-condition
generators, not one.**

| | `mvcgen` | `vcgen` |
|---|---|---|
| logic | `Std/Do/` — **21 files** | **`Std/Internal/Do/` — 17 more files** |
| tactic syntax | `Std/Tactic/Do/Syntax.lean:436` | **`Std/Tactic/Do/Syntax.lean:464`** (plus a `grind`-embedded step at `:476`) |
| elaborator | `Lean/Elab/Tactic/Do/VCGen*` | **`Lean/Elab/Tactic/Do/Internal/VCGen/`** |
| a frame rule | **none** | **`Std/Internal/Do/WP/Frame.lean`, 6 202 bytes, © 2026 Lean FRO, Sebastian Graf** |
| frame automation | — | **`@[frameproc]`** — `Lean/Elab/Tactic/Do/Internal/VCGen/FrameProc.lean` + `FrameProcAttr.lean` |
| stability | public `Std.Do` | **`Std.Internal` — explicitly internal** |

**`docs/mvcgen-pilot.md` §1.1's census — *"`Std.Do` at the pin — yes, 21 files
under `src/lean/Std/Do/`, 2 under `Std/Tactic/Do/`"* — is correct and
incomplete.** It censused the namespace it was asked about. `Std/Internal/Do/`
was not in the question, and it is where the frame rule lives.

**And the `vcgen` tactic's grammar is a list of things this survey was about to
recommend building.** Verbatim from `Std/Tactic/Do/Syntax.lean:464–472`:

```
syntax (name := vcgen) "vcgen" optConfig
  (" [" … "] ")?
  (&" until " term)?
  (&" frames " withPosition((colGe frameAlt)+))?
  (invariantAlts)?
  (&" simplifying_assumptions" …)?
  (&" with " vcgenDischarge)? : tactic
```

* **`until <term>`** — stop VC generation when the program matches a pattern.
  That is §3's *"stop just before a branching point … to establish facts that
  are needed in several branches"* — CFML's `xgo`-stopping rule, as a tactic
  clause.
* **`frames <alt>+`** — a first-class frames clause.
* **`with grind`** — and the source comment says the `grind` alternative is
  first-class *"so it can share `vcgen`'s internalised E-graph"*. That is
  `docs/lean-structures-census.md` §2's grind-seam recommendation — measured
  there at **12 VCs → 0** — **built into the tactic** rather than wired by a
  `macro_rules` line.

### 2.2 The frame combinator, read at the pin, with its exact obligations

`Std/Internal/Do/WP/Frame.lean` [source]:

```lean
structure WP.Frames {R : Type t} (op : R → Pred → Pred) (x : Prog) (F : R) : Prop where
  conj_wp_le_wp_conj : ∀ (Q : Value → Pred) (E : EPred),
    op F (wp x Q E) ⊑ wp x (fun a => op F (Q a)) E
```

That is **Calcagno, O'Hearn & Yang's locality condition**, transcribed. And the
combinator that makes it hold *by construction*:

```lean
@[instance_reducible] noncomputable def WPMonad.of_frameClosure
    {m : Type → Type} [Monad m] {P : Type u} {E : Type z} [Assertion P] [Assertion E]
    {R : Type} (op : R → P → P) [∀ r, PreservesSup (op r)] {comp : R → R → R} {e : R}
    (hact : ∀ r r' a, op (comp r r') a = op r (op r' a))
    (hunit : ∀ a, op e a = a)
    (base : WPMonad m P E) : WPMonad m P E
```

**Four obligations, and that is the whole bill:** `PreservesSup (op r)`, action
associativity, a unit, and a base `WPMonad` — which §1.3 already showed
synthesises for our stack with **zero instances written**. **No cancellativity.
No step-indexing. No later modality. No resource algebra. No ghost state.**

**And there is a cheaper door still**, in the same file:

```lean
theorem WP.Frames.of_wp_conjunctive [WPConjunctive Prog Value Pred EPred]
    {x : Prog} {F : Pred} (h : ∀ E, F ⊑ wp x (fun _ => F) E) : WP.Frames (· ⊓ ·) x F
```

> **If `wp x` is conjunctive, then "F is preserved by `x`" IS a frame rule for
> `F`, with meet in place of `∗`.** And conjunctivity is not something we would
> have to arrange: `Std.Do.PredTrans` carries conjunctivity **as a field of the
> structure** (`Std/Do/PredTrans.lean:59–82`) — it is the healthiness condition
> the Dijkstra-monad model was built on. §1.1's observation that `PredTrans` is
> conjunctive turns out to be the hinge.

That is precisely the shape of the §L80 residue. The locality fact nobody had
written down — *"the inner generator's steps preserve the `pst` slot"* — is
`h : ∀ E, PstAt ⊑ wp x (fun _ => PstAt) E`, and `of_wp_conjunctive` turns it
into framing for free. **`PstAt` was already the right object; what was missing
was the rule that consumes it.**

### 2.3 What the literature says, and where it lands

**The frame rule, and the side condition we do NOT pay.** John C. Reynolds,
"Separation Logic: A Logic for Shared Mutable Data Structures", LICS 2002,
55–74, DOI 10.1109/LICS.2002.1029817; Peter W. O'Hearn, John C. Reynolds,
Hongseok Yang, "Local Reasoning about Programs that Alter Data Structures",
CSL 2001, LNCS 2142, 1–19, DOI 10.1007/3-540-44802-0_1 [both secondary]. The
rule is `{P} C {Q} ⟹ {P ∗ R} C {Q ∗ R}` with side condition
`Modifies(C) ∩ Free(R) = ∅`, and CSL 2001 says immediately after defining
`Modifies` — this is the sentence that matters most for us —

> the `Modifies` set only tracks potential alterations to the **store**, and
> says nothing about the heap cells that might be modified.

**So separation logic does not replace modifies clauses.** It uses `∗` for the
*heap* dimension and keeps a modifies clause for the *program-variable*
dimension. Soundness rests on two semantic properties of the *language* — later
named **Safety Monotonicity** and the **Frame Property** (Hongseok Yang, *Local
Reasoning for Stateful Programs*, PhD dissertation, UIUC, 2001; Yang & O'Hearn,
"A Semantic Basis for Local Reasoning", FoSSaCS 2002, LNCS 2303, 402–416
[secondary]) — and Yang proved the frame rule **complete**.

**And our substrate is the favourable case.** Arthur Charguéraud, "Separation
Logic for Sequential Programs (Functional Pearl)", *PACMPL* 4(ICFP), Article
116, 2020, DOI 10.1145/3408998 [read] §1:

> targeting an ML-style language with **immutable variables and mutable
> heap-allocated memory cells leads to the simplest formulation of the reasoning
> rules, avoiding a number of complications associated with mutable variables**.

His frame rule carries **no side condition at all**. In `SemM` all mutation is
in `W` and Lean's binders are immutable, so **the side condition the brief
identified as "where the cost lives for us" does not exist for us.**

**What Iris's machinery is actually for.** Jung, Krebbers, Jourdan, Bizjak,
Birkedal, Dreyer, "Iris from the ground up", *JFP* 28:e20, 2018, DOI
10.1017/S0956796818000151 [secondary]. §4 is explicit that step-indexing exists
to solve one problem: the model wants `iProp ≜ Res → Prop` with
`Res ≜ F(iProp)`, and for higher-order ghost state that equation has provably
**no** solution by a cardinality argument — *"In order to circumvent this
problem, we use step-indexing."* Scoring the brief's four candidates:

| machinery | needed for a first-order frame rule over a finite map? |
|---|---|
| separation algebra / PCM on the state | **yes** — the irreducible core |
| later modality + step-indexing | **no** — solely for the recursive domain equation |
| ghost state / resource algebras | **no** — for ownership protocols and concurrency |
| the `wp` definition | **yes, but it is ours** — the frame rule is *derived* |

**And the algebraic minimum is smaller than the textbook definition.** Calcagno,
O'Hearn & Yang, "Local Action and Abstract Separation Logic", LICS 2007,
366–378, DOI 10.1109/LICS.2007.30 [secondary] define a separation algebra as a
*cancellative* partial commutative monoid — but **cancellativity is used for the
lattice structure and for completeness, not for frame soundness**. Frame
soundness is characterised exactly, and as an *iff*: a relation satisfies Safety
Monotonicity and the Frame Property **iff** the frame rule is sound for it.
**Lean's `WP.Frames` is a direct transcription of that condition.**

**Empirical corroboration that step-indexing is droppable:**
`leanprover-community/iris-lean`'s own `Iris/Instances/Classical/Instance.lean`
gives a full `BI` instance for a plain non-step-indexed heap model with
`later P σ := P σ` — **the later modality is the identity** — and
`COFE.ofDiscrete`, over a `State` module whose entire obligation set is **seven
lemmas**: `empty_union`, `union_comm`, `union_assoc`, `empty_disjoint`,
`disjoint_comm`, `disjoint_assoc`, `disjoint_union`. **No cancellativity**
[secondary].

### 2.4 The modifies-clause alternative, priced honestly

**Papers.** K. Rustan M. Leino, "Dafny: An Automatic Program Verifier for
Functional Correctness", LPAR-16, LNCS 6355, 348–370, DOI
10.1007/978-3-642-17511-4_20 [skimmed]. Ioannis T. Kassios, "Dynamic Frames",
FM 2006, LNCS 4085, 268–283, DOI 10.1007/11813040_19 [skimmed]. **Anindya
Banerjee, David A. Naumann, Stan Rosenberg, Region Logic, *JACM* 60(3), Article
18, 2013, DOI 10.1145/2485982** [secondary] — the most transferable design.
Matthew J. Parkinson & Alexander J. Summers, "The Relationship Between
Separation Logic and Implicit Dynamic Frames", *LMCS* 8(3:01), 2012, DOI
10.2168/LMCS-8(3:01)2012 [secondary] — **for the fragments tools actually
support, separation logic embeds faithfully into implicit dynamic frames**; the
choice is about tooling, not expressiveness.

Region Logic's own framing of the relationship is the sentence to keep:
`P ∗ Q` says *"something like `P ∧ Q ∧ (ε ⫽ η′)`"*, so explicit footprints
amount to **"skolemizing the existential implicit in `∗`"**; and *"a virtue of
stateful frame conditions: **they do not require a really new logic**."*

**The Lean shopping list for this route** is four definitions (`agree`,
`allows`, `ftpt`, the write-effect judgement), ~5 lemmas, and **one theorem that
replaces the forty**:

```lean
-- (illustrative — the poor-man's frame, not a tree file)
theorem exec_frame {s : Stmt} {σ σ' : World} (h : exec F σ s = .ok σ' v) :
    ∀ k ∉ writes s, σ'.heap[k]? = σ.heap[k]?
```

One tip worth taking from Region Logic (Remark 6.6): state the framing lemma as
an **iff** — `agree σ σ' (ftpt Q) → (Q σ ↔ Q σ')` — because the one-way form
makes negation unsound.

**Two honest data points on this route.** (i) Why3 is the interesting negative:
Filliâtre & Paskevich, ESOP 2013, DOI 10.1007/978-3-642-37036-6_8 — **WhyML has
no frame rule because it has no heap**; framing is a typing consequence. If part
of `W` is genuinely non-aliased by construction, restructuring costs *zero*
framing lemmas. (ii) The one hard number in this area: Jialin Li et al.,
"Linear Types for Large-Scale Systems Verification", *PACMPL* 6(OOPSLA1),
Article 69, 2022, DOI 10.1145/3527313 [skimmed] — converting ~24 K lines of
Dafny using the dynamic-frames idiom to linear types for 91% of the code gave
**28% fewer proof lines and 30% shorter verification time**. Their diagnosis of
the alternative — *"SMT solvers do not provide good support for separation
logic"* — is the mirror-image argument that **does not apply to us**: we have no
SMT backend to placate.

**No peer-reviewed head-to-head measuring annotation lines for the same program
specified both ways was found.** Any stronger quantitative claim is unsupported.

### 2.5 The closest prior art — framing for a monad, and what it cost them

**Pierre Nigron & Pierre-Évariste Dagand, "Reaching for the Star: Tale of a
Monad in Coq", ITP 2021, LIPIcs 193, 29:1–29:19, DOI
10.4230/LIPIcs.ITP.2021.29** [secondary] does exactly our thing. Their monad is
CompCert's `SimplExpr`: an uncatchable error plus `gensym` plus a state
**record** — structurally `ExceptT ρ (StateT W Halt)`. They define `wp` by
recursion on a reified free monad, set `hprop := gset ident → Prop` — **a
predicate over an abstract resource view, not over the state record** —
instantiate MoSeL, and derive `frame`.

**Their measured cost, in their words: *"The definition of the monad and its
separation logic introduce an additional 750 lines of code (ignoring the 30 000
lines of code of Iris/MoSel)."* Proof scripts went DOWN, 1 100 → 650 lines.**
And their stated missing piece — *"a library of ready-made separation logics for
reasoning about common effects"* — **is precisely what `WPMonad.of_frameClosure`
now is, in Lean core, at our pin.**

**The design lesson transfers directly: put `∗` on a PROJECTION of `W`, not on
`W`.** Globals and the table stay outside the separation structure.

Two more, for the record: **seL4/Isabelle** (Bannister, Höfner & Klein,
"Backwards and Forwards with Separation Logic", ITP 2018, LNCS 10895, 68–87,
DOI 10.1007/978-3-319-94821-8_5 [skimmed]) moved a generic separation-algebra
class and its tactics onto a **nondeterministic state monad** for the reported
cost of *"the addition of two trivial interface lemmas"* — the right order of
magnitude when the algebra already exists. And a **warning**: Paulo Emílio de
Vilhena & François Pottier, "A Separation Logic for Effect Handlers", *PACMPL*
5(POPL), Article 33, 2021, DOI 10.1145/3434314 [skimmed] — framing under effect
handlers is sound **only under a one-shot continuation discipline**. Our `Kont`
is defunctionalized data and §3.4's ruling says `SemM` cannot suspend, so we are
inside that discipline — **but a tier that ever resumes a continuation twice
would break the frame rule, and that should be written down before any tier
tries.**

Finally, O'Hearn's CACM retrospective names our exact failure mode. **Peter W.
O'Hearn, "Separation Logic", *CACM* 62(2):86–95, 2019, DOI 10.1145/3211968**
[secondary], §4: `deletetree` *"could not be verified without the Frame Rule,
unless we were to complicate the initial specification by **including some
representation of frame axioms (saying what does not change)** to enable the
proofs at the recursive call sites."* **We have forty of those, and `DictCalc`
is one module.** The counterweight from §3 of the same paper is equally worth
recording: many papers *"avoided `−∗`, often on the grounds that it complicates
automation and is **only needed for programs with significant sharing**."*

### 2.6 Price, risk, verdict

| item | price | risk | verdict |
|---|---|---|---|
| **CENSUS `Std/Internal/Do/` AND THE `vcgen` TACTIC AT THE PIN** — 17 files, a frame rule, `@[frameproc]`, `until`, `frames`, `with grind` | one docs-only census in the shape of `docs/lean-structures-census.md`, plus **one experiment file** and one ticket | **not doing it is the risk.** We have been pricing a build against a capability we may already own | **ADOPT-NOW.** This is the survey's #1 item |
| **`WP.Frames.of_wp_conjunctive`** — turn "`PstAt` is preserved" into framing, with `⊓` and no `∗` at all | one preservation lemma per primitive; `PredTrans` is *already* conjunctive | needs `WPConjunctive` for our stack, which is `Std.Internal`'s, not `Std.Do`'s — unverified for `ExceptT`-outside | **PILOT — and it is the cheapest attack on P4 in the document** |
| **`WPMonad.of_frameClosure` with a real `∗` on a projection of `W`** | ~250–350 lines by the in-core blueprint: heap defs + ~6 heap lemmas, an **opaque** `HProp` with a `CompleteLattice` instance, 4 connectives, 3 algebra laws, 1 `PreservesSup`, 1 `upperAdjoint` | `Std.Internal` is **explicitly unstable**; the in-tree exception example is `StateT Nat (ExceptT String Id)` — **exception INSIDE**, and ours is outside; and `Halt` needs a `WPMonad` instance first | **PILOT, gated on the census** |
| **The modifies-clause metatheorem** — `exec F σ s = .ok σ' v → ∀ k ∉ writes s, σ'.heap[k]? = σ.heap[k]?`, plus `agree`/`ftpt`/framing-as-iff | 4 defs, ~5 lemmas, one induction sized to the interpreter's case analysis | it will fail to compose exactly where two **unknown** sub-heaps must be disjoint — the existential `∗` keeps and footprints skolemize away | **PILOT — the fallback, and it is a good one.** Uses no unstable API and composes with `grind`, which already has `getElem_insert` as `@[grind =]` |
| **Iris / `iris-lean`'s `ProgramLogic`** | 3.4 MB, toolchain one minor behind, a `Language`/`EctxLanguage` interface `SemM` does not fit | — | **NOT-FOR-US, because** we would import all of that to get a `∗` we can define in thirty lines. (`iris-lean`'s `Instances/Classical` remains worth *reading* — it is the proof that the later modality can be the identity) |
| **Building our own BI from scratch** | the "Eileen" plan's own anchor: Iris in Rocq is ~200 files / ~50 000 lines, and its author writes *"This project has a reasonable chance of failure"* | — | **NOT-FOR-US** |

**Does §0.1 survive?** Yes throughout. A frame rule is **LIBRARY** by principle
II's own table — the trust boundary is drawn at the definition, and `wp`,
`Frames` and any `@[frameproc]` are help, not meaning. The one thing to watch is
`WPMonad.of_frameClosure`'s *reinterpretation* of `wp`: it replaces the
weakest-precondition **with its frame closure**, which is a change to what a
`Triple` *means*. That is still LIBRARY — no interpreter changes — but it is the
kind of thing that must be stated at the use site, per §0.1's receipts-at-the-
use-site rule, not adopted silently.

---

## §3 Characteristic formulae — the design that is linear AND lossless

**The pains:** P1 (the deep-gate ceiling), P2 (the unstateable lemma), P12 (the
kernel wall), and — unexpectedly — a large part of P3.

### 3.1 The claim, in one paragraph

A **characteristic formula** `⟦t⟧` is a higher-order-logic predicate built by
structural recursion on the program's **syntax**, of size **linear** in the
program, that *pre-applies* the program logic's rules. The proof is conducted
against the formula; **the interpreter is never traversed again.** Charguéraud's
own three-point summary (SLF notes §10.1) is the cleanest statement: the formula
"no longer refer[s] to the deeply-embedded syntax"; it "in some sense
**pre-applies all the reasoning rules of the program logic**", so that at a
let-binding "there is no need to apply the lemma `wp-let`"; and the remaining
bookkeeping is "instantiate an existential quantifier and split a conjunction".

### 3.2 The papers

* **Arthur Charguéraud, "Program verification through characteristic formulae",
  ICFP 2010, 321–332, DOI 10.1145/1863543.1863590** [read].
* **Arthur Charguéraud, "Characteristic formulae for the verification of
  imperative programs", ICFP 2011, 418–430, DOI 10.1145/2034773.2034828**
  [read] — adds Separation Logic; the size claim is explicit: *"a
  characteristic formula has a size **linear** in that of the program it
  describes"* (§1).
* **Arthur Charguéraud, "Separation logic for sequential programs (functional
  pearl)", *PACMPL* 4(ICFP), Article 116, 2020, DOI 10.1145/3408998** [read].
* **Arthur Charguéraud, "Separation Logic Foundations", *Software Foundations*
  Volume 6** — chapters `WPsem`, `WPgen`, `WPsound` [read]. **This is the
  version to copy** (§3.4).
* **Armaël Guéneau, Magnus O. Myreen, Ramana Kumar, Michael Norrish, "Verified
  Characteristic Formulae for CakeML", ESOP 2017, LNCS, 584–610, DOI
  10.1007/978-3-662-54434-1_22** [read] — the fully-mechanised version, in
  HOL4, **against a clock-indexed functional big-step semantics**.
* Lineage of the *term*: **Susanne Graf & Joseph Sifakis, "A modal
  characterization of observational congruence on finite terms of CCS",
  *Information and Control* 68(1–3):125–145, 1986, DOI
  10.1016/S0019-9958(86)80031-6** (ICALP 1984 conference version), and
  **Bernhard Steffen & Anna Ingólfsdóttir, "Characteristic formulae for
  processes with divergence", *Information and Computation* 110(1):149–163,
  1994, DOI 10.1006/inco.1994.1028** — which Aceto & Ingólfsdóttir's survey
  ("Characteristic Formulae: From Automata to Logic", BRICS RS-07-2, 2007) calls
  *"the standard reference"* [all secondary].

  **Two corrections to the brief's lineage, made before we cite it.** (i)
  **Rensink is not in this lineage** as far as the survey could establish —
  "Bisimilarity of Open Terms" is about conditional transition systems, and
  Aceto & Ingólfsdóttir cite him **zero** times. Drop him. (ii) **Charguéraud
  himself does not cite Graf & Sifakis** — his ICFP 2010 sentence "The notion of
  characteristic formula originates in process calculi" cites Korver (CAV 1991),
  Milner (*Communication and Concurrency*, 1989) and Park (LNCS 104, 1981). Cite
  the lineage and what Charguéraud actually cited as two separate facts.

### 3.3 THE RESULT — and it is the reason this section exists

Read §1.5's finding next to Charguéraud's abstract and the identification is
exact.

| encoding | size | information kept |
|---|---|---|
| `mvcgen` default (`jp := false`) | *"exponential blowup of VCs"* | everything |
| `mvcgen +jp` | *"**linear** in the number of control flow splits"* | *"slightly **lossy**"* |
| **characteristic formula** | *"a size **linear** in that of the program"* | **everything** |

> **`+jp` and characteristic formulae reach the same size bound by the same
> insight — traverse each join point once — and CF does it without paying the
> lossiness.** Lean's own team wrote "traverses every join point only once …
> linear in the number of control flow splits" in a docstring, sixteen years
> after Charguéraud wrote "size linear in that of the program it describes" in
> an abstract, and neither cites the other. That convergence is the strongest
> evidence in this survey that CF is aimed at our problem.

**Why CF gets linearity without loss — the mechanism, stated exactly.** Naive WP
pushes the continuation *into* each branch: `wp (if b then t₁ else t₂; k)`
becomes `if b then wp(t₁;k) else wp(t₂;k)`, duplicating `k`. Nest that `d` deep
and you get `2ᵈ` copies. **Our 259-vs-12 measurement is this, and the "four-deep
ceiling" is `2⁴` beginning to bite.** CF avoids it two ways:

1. **Sharing in the generated term.**
   `wpgen_if t₀ F₁ F₂ = fun Q => ∃b, ⌜t₀ = b⌝ ⋆ (if b then F₁ Q else F₂ Q)` —
   the *same* `Q` flows into both branches, and the continuation lives outside
   as one `λ` in `wpgen_let F₁ (fun v => F₂of v Q)`. The formula is a
   DAG-with-sharing, not an unfolded tree.
2. **`mkstruct` puts the consequence rule at every node**, so you can **stop,
   name an intermediate assertion, and cut** — instead of dropping information.
   That is the lossless analogue of `+jp`'s lossiness.

And Charguéraud names the anti-duplication goal explicitly (ICFP 2010 §1.2, on
why `xgo` must be stoppable): stopping before a branching point *"allows one to
stop just before a branching point in the code in order to establish facts that
are needed in several branches … it is **extremely important to avoid
duplicating the corresponding proof script across several branches**."*

### 3.4 THE TRUST STORY — this is the section that decides it under §0.1

**CFML *the tool* is disqualified by our doctrine, and it must be said out
loud whenever we cite it.** From the primary sources: CFML *"parses an OCaml
source code … produces a set of Coq definitions … plus **one axiom** stating the
characteristic formula"* (2010 §1.3); for a top-level recursive function it
*"generates **two Coq axioms**"* (2011 §2.4); and on what backs them —
*"We have proved **on paper** that characteristic formulae are sound with
respect to the logic of Coq … (In practice, generating actual proof terms would
require a lot of effort, so **we have not implemented it**.)"*. The TCB is a
3 000-line OCaml generator plus a 4 000-line Coq library. The CakeML team's
independent assessment is blunter: CFML's `cf` *"is external to the proof
assistant (Coq), and the translation from OCaml to Coq is **not completely
transparent**"*.

> **That architecture is exactly what §0.1 principle I forbids** — a definition
> layer that an unverified translator can influence. **We do not adopt CFML.**

**SLF and CakeML are the verified version, and they are what we would copy.**
SLF's `wpgen : ctx → trm → formula` is an ordinary Coq function over the AST,
with a machine-checked soundness theorem:

```
wpgen_sound       : ∀ E t Q, wpgen E t Q ⊢ wp (isubst E t) Q
triple_of_wpgen   : ∀ t H Q, H ⊢ wpgen nil t Q → triple t H Q
```

structured through **one** auxiliary judgement,
`formula_sound t F ≜ ∀Q, F Q ⊢ wp t Q`, then a one-to-four-line lemma per
constructor and a main induction Charguéraud reports as *"no more than a dozen
lines long"*.

**And CakeML proved it against a CLOCK-INDEXED semantics** — the ESOP 2017
theorem existentially quantifies the clock:

```
⊢ cf e env H Q ⇒ ∀st. H (state_to_set st) ⇒
    ∃st' hf hg v ck. evaluate (st with clock := ck) env [e] = (st',Rval [v]) ∧ …
```

They state the point in as many words: this *"eliminates the last bits of paper
proof that need to be trusted in CFML."* **This is direct evidence that the CF
design survives a fuel-indexed interpreter** — which is the single fact that
makes it a candidate for us at all.

### 3.5 `mkstruct`, precisely, because it is what we would be buying

```
mkstruct F ≜ fun Q => ∃ Q₁, F Q₁ ⋆ (Q₁ -⋆ Q)
```

*"`mkstruct F` holds of `Q` if `F` holds of some `Q₁`, together with the
resources to turn `Q₁` into `Q`."* It is the ramified frame rule at the level of
formulas. It exists because the frame and consequence rules are **not
syntax-directed** — you cannot tell from the shape of `t` where the user will
want them — so the generator's strategy is *aggressive*: put one at **every
node**. Properties: `mkstruct_erase`, `_conseq`, `_frame`, `_monotone`,
`mkstruct_wp` (it adds nothing to a real `wp`), `mkstruct_idem`.

**Cost**: one wrapper per AST node (a constant factor — linearity survives);
every x-tactic must strip it first (`xstruct`); one extra soundness lemma (~4
lines).

**`mkstruct_conseq` at every node is the anti-duplication lever**, and it is
exactly what our altitude law does by hand: prove it once at the chain, with
every operand symbolic. **The altitude law is `mkstruct_conseq` applied
manually.**

### 3.6 A Lean 4 instance already exists — and its limits are informative

**`verse-lab/splean`** (VERSE Lab, NUS) is a genuine SLF port over a **deep
embedding**, in Lean 4 [secondary, source-level reading]. `SPLean/Theories/
WP1.lean` (~1 819 lines) contains, by name: `wp`, `mkstruct`, `structural`,
`mkstruct_ramified/_erase/_conseq/_frame/_monotone`, the `wpgen_*` leaf
combinators, `wpgen`, `formula_sound`, `wpgen_sound`, `triple_of_wpgen`,
`xwp_lemma_fun/fix/funs`, and the x-tactic family as Lean 4 `macro`/`elab` —
`xstruct`, `xval`, `xlet`, `xseq`, `xif`, `xref`, `xapp` (with an `@[xapp]`
hint database), `xwp`, `xtriple`, `xsimp_step`.

**Its limits are the honest part.** SPLean's `wpgen` is the **one-step
(non-recursive)** variant — subterms go to `wp`, not to a recursive `wpgen` —
the `ctx`-based `wpgen_var` is commented out, `wpgen_for_sound` is commented out
and incomplete, and the README says *"Recursion is not supported (yet)"* and
*"We only support programs in an SSA-normal form"*. **So it is a working
skeleton, not a finished generator** — but it proves the design typechecks in
Lean 4 and it hands us `mkstruct`, `formula_sound`, `wpgen_sound` and ~1 000
lines of x-tactic metaprogramming to read.

**Nothing in Lean 4 is a full recursive `wpgen` with context-based binder
handling and a complete soundness theorem over a statement language.** That is
open ground.

### 3.7 What it would cost us

The estimate is anchored on three measured artifacts: SLF's `WPgen.v`/`WPsound.v`,
SPLean's 1 819-line `WP1.lean`, and CFML's 4 000-line Coq library.

| component | Lean 4 lines |
|---|---|
| `formula := (Val → World → Prop) → World → Prop` | 5 |
| `mkstruct` + 6 properties | 60–120 |
| `wpgen_*` leaves, one per `Stmt` constructor | 60–120 |
| `wpgen : Ctx → Program → formula` | 30–60 |
| `isubst`/`rem`/`lookup` + commuting lemmas — *"the only tedious parts"* per the author | **80–200** |
| `formula_sound` + per-constructor lemmas | 80–150 |
| `wpgen_sound` + `triple_of_wpgen` | 30–60 |
| loops (`while`/`for` with quantified `R`/`S`, incl. the fuel discharge) | **150–350** |
| x-tactics (`xwp`, `xstruct`, `xval`, `xlet`, `xseq`, `xif`, `xapp`, spec DB) | **500–1 000** |
| notation/delaborators so formulas read like source | 100–250 |
| **total** | **~1 100–2 300** |

**The single largest lever on that number: do we need separation logic at all?**
Our `World` is a record, not an arbitrary heap. If the answer is no, `mkstruct`
degenerates to consequence-only —
`mkstruct F Q := fun w => ∃ Q', F Q' w ∧ (∀ v w', Q' v w' → Q v w')` — with no
magic wand, no `xsimpl`, no `xchange`, and **no ~900-line entailment
simplifier**. That roughly halves the estimate and removes the largest source of
tactic complexity. **Check it early; it is the biggest single decision.**

Against that, the number to beat is `VC.lean` 546 + `VC2.lean` 939 +
`VCTactic.lean` 3 371 + `LoopTactic.lean` 487 = **5 343 lines**, which is
per-language by construction. A CF generator is per-language too — but it is
**~1 100–2 300 lines of which the tactic half is largely reusable**, and its
soundness is one theorem rather than 3 371 lines of walker nobody audits.

### 3.8 What it does NOT buy — and this is the honest half

* **CF does not fix Lean's reducer; it RELOCATES the problem.** Getting `wpgen`
  applied to a concrete `Program` to compute into a *readable* formula is
  precisely the difficulty SLF documents (naive `simpl` *"makes output hard to
  relate to the original program"*), solved there by auxiliary definitions plus
  custom notation. In Lean we would fight the same fight with `simp only
  [wpgen, …]`, transparency settings and equation lemmas — **in the exact
  neighbourhood where our `mvcgen` defect already lives.** The difference that
  matters: **we would fight it once per `xwp`, not once per proof step, and we
  would control the reduction because `wpgen` is our own definition.**
* **Completeness is not on our path.** Charguéraud proves it; we only need
  soundness. Do not budget for it.
* **The loop case is research, not transcription.** SPLean's `wpgen_for_sound`
  is commented out and unfinished; CFML's loop soundness is in the paper proofs.
  Connecting a quantified-`R` loop formula to a fuel-indexed `execStmts` is
  original work — **CakeML did it with a clock, so it is known-possible**, but
  budget it as research.

### 3.9 Price, risk, verdict

| item | price | risk | verdict |
|---|---|---|---|
| **The CF spike** — `formula`, `mkstruct`, leaf combinators and `wpgen` for a **three-constructor** fragment of `Stmt`, then check that `wpgen [] ⟨the five-deep gate⟩` reduces to a readable term of ~linear size | ~150 lines, one day, one ticket | it is designed to fail cheaply; **failure is the result** | **PILOT — and it is the gate on everything else in this section.** Do §1.5's two runs first; do this second |
| **The full `wpgen` + x-tactics** | 1 100–2 300 lines (half that without separation logic) | reduction control (highest); loops+fuel (research); binder handling; ~1 000 lines of metaprogramming that tracks Lean releases and that **we** maintain, where `mvcgen` is maintained by the Lean team | **PILOT, gated on the spike** — and gated on `+jp` failing. If `+jp` closes the four-deep gate, the case shrinks to the *other* two benefits (interpreter never traversed; loops without fuel unrolling), which `+jp` does not address |
| **CFML the tool** (external generator + axioms) | — | — | **NOT-FOR-US, because** §0.1 principle I forbids a definition layer an unverified translator can influence. Say so whenever we cite CFML |
| **The lineage citations** (Graf & Sifakis 1986; Steffen & Ingólfsdóttir 1994) | free | none | **ADOPT-NOW as citations**, with Rensink dropped and Charguéraud's own citation list kept separate |
| **The altitude law's new name** | free | none | **ADOPT-NOW.** *The altitude law is `mkstruct_conseq` applied by hand.* Recording that gives a hard-won house law a twenty-year pedigree and a precise statement |

**Does §0.1 survive?** For the SLF/CakeML design, **yes** — `wpgen` is a Lean
function over our own AST with a machine-checked soundness theorem, and it is
LIBRARY, not DEFINITION: the interpreter stays the definition and `wpgen_sound`
is a theorem *about* it. For CFML-the-tool, **no**, and that is why it is
rejected.

---

## §4 Interaction trees and fuel-free models — the answer is NO, and the consolation prize is large

**The pain:** P3 (13 files carrying `∃ t, ∀ F ≥ t`).

### 4.1 The finding that matters, first — and it is not about interaction trees

Our threshold form is not an ad-hoc shape we invented. It is, character for
character, **Leroy & Grall's definition of denotation**:

> **Xavier Leroy & Hervé Grall, "Coinductive big-step operational semantics",
> *Information and Computation* 207(2):284–304, 2009, DOI
> 10.1016/j.ic.2007.12.004 (arXiv 0808.0586), §5** [read] — mechanised in Coq:
>
> `D(a, r) ≜ ∃p, ∀n, n ≥ p ⟹ Cₙ(a) = r`
>
> where `Cₙ` is a **fuel-indexed evaluator** returning a distinguished `⊥`
> meaning *"cannot complete within n recursive steps"* — **exactly our `Halt`,
> distinct from error.**

And §5 proves the kit we are re-deriving by hand at every fuel-recursive point:

| | statement |
|---|---|
| **Lemma 12** | monotonicity: `n ≤ m → Cₙ(a) ≤ Cₘ(a)` in the flat order `⊥ ≤ r` — **this is `fuelMono`** |
| **Lemma 13** | `D(a,r) → ∀n, Cₙ(a) = ⊥ ∨ Cₙ(a) = r` |
| **Lemma 14** | `r ≠ ⊥ ∧ Cₙ(a) = r` for **some** `n` → `D(a,r)` |
| **Lemma 15** | `D(a,⊥) ↔ ∀n, Cₙ(a) = ⊥` |
| **Lemma 16** | totality (classical) |
| **Lemma 17** | determinism of `D` |
| **Theorem 18** | `a ⇒ v` **iff** `D(a, v)` — the adequacy theorem, terminating case |
| **Theorem 19** | `a ⇒^∞` **iff** `D(a, ⊥)` — adequacy, diverging case |

**Lemma 14 is the prize.** Given monotonicity, for any non-`Halt` outcome the
existential-threshold statement **collapses**:

```
(∃ t, ∀ F ≥ t, exec F w = .ok w' v)   ↔   (∃ F, exec F w = .ok w' v)
```

and divergence becomes `∀ F, exec F w = .Halt` (Lemma 15) — **with no threshold
either**. CakeML's top-level `semantics` relies on exactly this: a plain `∃ c`
for termination and a plain `∀ c` for divergence, never a threshold.

> **If the bulk of the plumbing across the 13 files is the `∀ F ≥ t` half, a
> one-time fuel-monotonicity lemma over `exec` deletes most of it WITHOUT
> CHANGING THE MODEL AT ALL.** That is a days-scale fix to a pain we have been
> pricing as a quarters-scale migration.

This is the survey's second-best deal and it needs no new machinery, no new
dependency, and no ticket beyond re-checking the 13 files.

### 4.2 Interaction trees — the papers, and the honest verdict

**Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha,
Benjamin C. Pierce, Steve Zdancewic, "Interaction Trees: Representing Recursive
and Impure Programs in Coq", *PACMPL* 4(POPL), Article 51, 2020, DOI
10.1145/3371119 (arXiv 1906.00046)** [read].

```coq
CoInductive itree (E : Type → Type) (R : Type) :=
| Ret (r : R) | Tau (t : itree E R) | Vis {A} (e : E A) (k : A → itree E R)
```

`Tau` exists to make corecursion **guarded** — *"ITrees can express silently
diverging computations and avoid the non-compositionality of guardedness
conditions"* — and the reasoning relation is **`eutt`**, weak bisimulation
("equivalence up to taus"), because `bind`, `iter`, `mrec` and `interp` all
insert `Tau`s. `eutt` is a **nested coinduction–induction** (`ν euttF`, via
`paco`), and the paper is candid that transitivity and `bind`-congruence *"are
quite challenging to prove."* Effects are events plus handlers `E ⇝ M`, folded
by `interp`, which is a **monad morphism** — that is the real deliverable, and
Vellvm's central claim.

**Related and worth citing:** Capretta, "General recursion via coinductive
types", *LMCS* 1(2), 2005, DOI 10.2168/LMCS-1(2:1)2005 [secondary] — the delay
monad, which ITrees describe as *"an ITree without the `Vis` constructor"*; and
Danielsson, "Operational semantics using the partiality monad", ICFP 2012, DOI
10.1145/2364527.2364546 [read] — the worked Agda development.

### 4.3 Why the answer is NO — six arguments, in descending force

**1. It costs exactly the property fuel exists for.** ITrees are executable *by
extraction* (paper §6: the type *"extracts as a **lazy datatype**"* and an
external OCaml driver runs it). Nothing about a whole ITree is decidable in the
kernel: `eutt` is a coinductive `Prop` with **no `Decidable` instance anywhere
in the library**. The paper itself says Coq's evaluation of coinductive terms is
*"driven by **context**, rather than the term itself, which means that proofs
must rely on explicit (or tactic-driven) rewriting."* In Lean the analogue of
extraction is `native_decide` — which moves the Lean compiler and generated C
into the TCB, the precise trade *run, not admired* exists to refuse.

**2. In Lean, the fuel-free model is BUILT ON FUEL.** This is the finding that
settles it. Mathlib's `MvQPF.Cofix F α := Quot MvQPF.Mcongr`, and the M-type
underneath (`Mathlib/Data/PFunctor/Univariate/M.lean`) is:

```
inductive CofixA : ℕ → Type   -- "n level approximation of an M-type"
def AllAgree (x : ∀ n, CofixA F n) := ∀ n, Agree (x n) (x (succ n))
-- M F ≅ { approx : ∀ n, CofixA F n // AllAgree approx }
```

> **Lean's coinductive type is literally our fuel-indexed family, plus a
> coherence proof, plus a quotient.** We would trade an explicit `Fuel`
> parameter we own for an implicit approximation tower three abstraction layers
> down that we don't.

And the one-step unfolding is not definitional: `Cofix.dest_corec` is a
*theorem* whose proof goes through **`abs_repr`** — a propositional field of the
`MvQPF` class with no computational content in general — and both it and
`Cofix.dest` carry `set_option backward.isDefEq.respectTransparency false`.
`M.children` inserts a `cast`. **`#guard` does not survive this.**

**3. The only Lean ITree that exists ships a fuel-indexed runner and cannot
implement `interp`.** `boogie-org/lean-itrees` (Amazon, Apache-2.0, 4 commits,
`lean-toolchain = v4.12.0`) hand-builds the shape functor from `MvQPF.Comp`/
`Sigma`/`Const`/`Prj` with a source comment reading *"this unfortunately doesn't
work, hence the workaround below"*. Its README concedes: *"Not
universe-polymorphic, **which prevents us from implementing `interp`**"* —
`interp` is §3 of the POPL paper and the entire modularity story — and *"We
assume that `Quotient`ing ITrees along Eutt is possible."* And then
`ITree/RunFinite.lean` defines `run … (fuel : Nat)` returning `Option A`.
**That is `exec : Program → Fuel → World → Result` with a `Halt`, rebuilt on top
of a coinductive model by people who had already paid the full QPF cost.** Even
coq-itree's own finite-prefix operator is `Fixpoint burn (n : nat)`.

**4. The dependency is not at our pin.** Codata in Lean is library-only —
Alex Keizer's **QpfTypes**, whose `lean-toolchain` reads `v4.25.0`. We are at
**v4.33.0-rc1**, eight releases ahead. (Lean 4.25.0 did add a native
`coinductive` command — **restricted to `Prop`**, built on `PartialFixpoint`,
by Różowski and Breitner. Good news for a weak-bisimilarity *relation*; it is
not codata and gives no executable cofixpoints.)

**5. `partial_fixpoint` is not the escape either — and the census already said
so.** It landed in Lean 4.17.0 and is comfortably at our pin; it needs a
`Lean.Order.CCPO` and a `monotonicity` discharge, and it produces unfolding
equations plus `partial_correctness` theorems. But the reference manual is
explicit that applications *"are **not definitionally equal to their return
values**"*. `docs/lean-structures-census.md` §9.1 measured exactly this
independently — `eq_def` ✓, `partial_correctness` ✓, **kernel `rfl` ✗** — and
recorded the price: *"Cost to adopt: zero. **Cost to misuse: the tier's entire
non-vacuity discipline.**"* Two independent readings agreeing is worth
recording.

**6. The adequacy theorem does not delete the counting; it relocates it.**
Danielsson's direction (3) — denotation → operational, the one we would need —
is proved by defining the **size** of the bisimilarity proof (the count of
`laterˡ` constructors) and doing complete induction on it, and he calls it
*"a bit awkward when written out in detail, due to the use of sizes."* We would
hand-assemble a fuel-like measure **inside** a coinductive proof instead of
inside a fuel-indexed one.

### 4.4 And the field is walking the other way

* **CakeML** (Owens, Myreen, Kumar, Tan, ESOP 2016 — see §6.5) went
  clocked-relational → clocked-**functional** and kept the clock for *every*
  intermediate language. Reported wins: *"the same functional big-step semantics
  used for proof can also be **executed on test programs**"*; **better induction
  theorems** (their `For` loop: one case functional, **six** relational); *"this
  ability to perform symbolic evaluation within the logic is a handy tool"*.
* **The ITrees authors concede the closeness.** §8.5, on Owens et al.: *"In
  practice, the approach is **quite similar to ITrees**, except that we can omit
  the fuel."*
* **The ITrees authors named Lean specifically.** §9: *"**Lean … lacks
  coinductive types, making it seemingly inadequate to the task.**"* Six years
  on, at v4.33: `coinductive` for `Prop` only, no codata in core, the
  third-party codata library eight releases behind our pin.
* **No project is attested migrating FROM a fuel-indexed functional semantics
  TO a coinductive one and reporting it as a win.** The nearest success story,
  **Vellvm/VIR** (Zakowski et al., ICFP 2021, DOI 10.1145/3473572), moved from
  *relationally-specified* semantics and cashed out in extraction-based
  executability — **a capability we already have by other means**, and the
  argument runs in the opposite direction from ours.

### 4.5 One thing that IS worth reading later

**HITrees: Higher-Order Interaction Trees** (Fadaei Ayyam & Sammler, arXiv
2510.14558, Oct 2025) [skimmed] — *"the first variant of interaction trees to
support higher-order effects in a **non-guarded type theory**"*, implemented
**in Lean**, reaching ITree-like structure by making effect fixpoints
**inductive** and **defunctionalizing** higher-order outputs to first-order.
Defunctionalization is `Kont`. **If we ever want ITree-shaped modularity in
Lean, this is the design to read — not the QPF route.**

### 4.6 Price, risk, verdict

| item | price | risk | verdict |
|---|---|---|---|
| **Name the predicate.** `Denote w r := ∃ p, ∀ F ≥ p, exec F w = r` — Leroy & Grall's `D`. We already have it; give it a name and a rule set | one definition | none | **ADOPT-NOW** |
| **Prove Leroy & Grall Lemmas 12–17 once, generically over `exec`** | one file; `fuelMono` largely exists | Lean's ambient classicality makes Lemma 16 free where Danielsson needed `EM` | **ADOPT-NOW** |
| **Cash in Lemma 14** — replace `∃ t, ∀ F ≥ t, … = .ok …` with `∃ F, … = .ok …` throughout, and divergence with `∀ F, … = .Halt` | re-statement of the 13 files, mechanically | **the measurement is owed**: what fraction of the 13 files' plumbing is the `∀ F ≥ t` half? Nobody has counted | **PILOT — measure first, on ONE file.** `star_lab/spec.lean` (102 lines, `fuelMono` ×1) is the obvious probe |
| **Restate the 13 files against `Denote`** | mechanical once the kit exists | the shape changes in the rebuild anyway (fuel is spent per `Kont` level, not per node), so co-ordinate with that lane | **PILOT, after the probe** |
| **ITrees / QPF codata / `partial_fixpoint` as the interpreter** | ~— | **breaks kernel-reducible runs**, which is the tier's whole non-vacuity discipline | **NOT-FOR-US, because** all three fuel-free routes fail the hard constraint, and in Lean the fuel-free model is a quotient of a fuel-indexed tower anyway |
| **CakeML's ESOP 2016 argument** | free | none | **ADOPT-NOW as a citation.** `docs/family-architecture.md` §3.4's fuel ruling should cite it: our clock is a published design choice with reported benefits, not an apology |
| **HITrees** | free | none | **WATCH.** Read before any future ITree-shaped proposal |

**Does §0.1 survive?** Emphatically. Everything adopted here is a *restatement*
of claims we already make, proved equivalent by Leroy & Grall's own lemmas — no
∀ is narrowed. Everything rejected is rejected precisely **because** it would
weaken the definition layer's executability, which principle II's trust table
puts on the trusted side.

---

## §5 Outcome logic and incorrectness logic — the verdict taxonomy, named by the literature

**The pains:** P8 (the taxonomy is home-grown), and — unexpectedly — P11 (the
vacuity incidents), which this literature turns out to speak to directly.

### 5.1 The finding, first, because it is not the one the brief expected

Our three verdicts *are* a reinvention, and the literature *does* unify them
into a single statement form — **but the unifying operator is not the one the
brief guessed.** It is not outcome conjunction `⊕`. It is the pair of
**modalities `□`/`♢` sitting in the postcondition of one Outcome Logic triple**,
and `⊕` is the lower-level primitive that defines them. Writing our membership
sites with `⊕` would be **wrong**, for a reason worth stating loudly (§5.4).

### 5.2 The papers

* **Noam Zilberstein, Derek Dreyer, Alexandra Silva, "Outcome Logic: A Unifying
  Foundation for Correctness and Incorrectness Reasoning", *PACMPL* 7(OOPSLA1),
  Article 93, 2023, DOI 10.1145/3586045 (arXiv 2303.03111)** [read]. The triple
  is `⊨ ⟨φ⟩ C ⟨ψ⟩ iff ∀m ∈ MΣ. m ⊨ φ ⟹ ⟦C⟧†(m) ⊨ ψ` — Hoare's shape exactly,
  except that `m` ranges over a **monadic collection** rather than a single
  state, and `⟦C⟧†` is the Kleisli extension.
* **Noam Zilberstein, "Outcome Logic: A Unified Approach to the Metatheory of
  Program Logics with Branching Effects", *ACM TOPLAS* 47(3), Article 14, 2025,
  DOI 10.1145/3743131 (arXiv 2401.04594)** [secondary] — sound and **relatively
  complete** (Cook/Apt sense).
* **James Li, Noam Zilberstein, Alexandra Silva, "Total Outcome Logic: Unified
  Reasoning for a Taxonomy of Program Logics", arXiv 2411.00197 v2 (2025)**
  [read] — *preprint; no peer-reviewed venue found, and it should be cited as a
  preprint*. This is the paper that carries the unification we want.
* **Peter W. O'Hearn, "Incorrectness Logic", *PACMPL* 4(POPL), Article 10,
  2020, DOI 10.1145/3371078** [read], and its precursor **Edsko de Vries &
  Vasileios Koutavas, "Reverse Hoare Logic", SEFM 2011, LNCS 7041, 155–171**
  [secondary].
* **Lena Verscht & Benjamin Lucien Kaminski, "A Taxonomy of Hoare-Like Logics",
  *PACMPL* 9(POPL), 2025, DOI 10.1145/3704896 (arXiv 2411.06416)** [secondary] —
  sixteen logics on three axes: correctness vs incorrectness, totality vs
  partiality, **angelic vs demonic nondeterminism**. Those are our axes.
* **Noam Zilberstein, Dexter Kozen, Alexandra Silva, Joseph Tassarotti, "A
  Demonic Outcome Logic for Randomized Nondeterminism", *PACMPL* 9(POPL), 2025,
  DOI 10.1145/3704855** [secondary] — the ∀-resolution triple as a primitive.
* For under-approximate reasoning that is genuinely *interleaving*-aware:
  **Raad, Berdine, Dreyer & O'Hearn, "Concurrent Incorrectness Separation
  Logic", *PACMPL* 6(POPL), Article 34, 2022, DOI 10.1145/3498695** and
  **Raad, Vanegue, Berdine & O'Hearn, "A General Approach to Under-Approximate
  Reasoning About Concurrent Programs" (CASL), CONCUR 2023, DOI
  10.4230/LIPIcs.CONCUR.2023.25** [both skimmed].

### 5.3 The mechanism, and the three names we are missing

Total Outcome Logic defines, explicitly after dynamic logic (Pratt 1976), two
modalities on outcome assertions, and then proves that the whole taxonomy is
one triple with a different modality in the post:

| our verdict | TOL's form | what it is called |
|---|---|---|
| **∀-schedule MATCH** | `⟨⌈P⌉⟩ C ⟨□ Q⟩` | **demonic**; partial Hoare (TOL Thm 4.1) |
| **membership site** | `⟨⌈P⌉⟩ C ⟨□ (· ∈ permitted)⟩` | the same triple, disjunctive **state** predicate |
| **DIVERGE-with-witness** | `⟨⌈P⌉⟩ C ⟨♢ Q⟩` | **angelic**; a **LISBON TRIPLE** (TOL Thm 4.1) |

**The name we are missing is "Lisbon triple", and it matters.** A Lisbon triple
is `∀σ ⊨ P. ∃τ ∈ ⟦C⟧(σ). τ ⊨ Q` — *for every input, some execution reaches Q*.
That is our counterexample-schedule verdict **exactly**. It is named after a
POPL'19 conversation in Lisbon (Dreyer and Jung proposing them to O'Hearn and
Villard), and it *predates* Incorrectness Logic. Incorrectness Logic's triple is
a **different quantifier structure** — `∀τ ⊨ Q. ∃σ ⊨ P. (σ,τ) ∈ ⟦C⟧`, "every
state in the post is reachable from some pre-state" — and O'Hearn's reason for
preferring it (the reverse consequence rule lets a symbolic-execution engine
*drop disjuncts* to stay in bounded memory) is **a scalability concern that does
not apply to us**: we emit whole-program per-site verdicts and discharge them by
kernel evaluation.

> **Cite Lisbon Logic for DIVERGE-with-witness. Do not cite Incorrectness
> Logic for it.** Getting this wrong would attach our verdict to the wrong
> theorem.

### 5.4 The `⊕` trap — a warning worth more than the vocabulary

Outcome conjunction is BI-shaped (O'Hearn & Pym's Logic of Bunched Implications,
with *program outcomes* as the resource instead of heap cells):

```
m ⊨ φ ⊕ ψ   iff   ∃ m₁ m₂. m₁ ⋄ m₂ ≼ m ∧ m₁ ⊨ φ ∧ m₂ ⊨ ψ
S ⊨ P       iff   S ≠ ∅ ∧ ∀σ ∈ S. σ ⊨ P
```

The `S ≠ ∅` side condition is load-bearing: it makes `⊕` a **reachability**
claim. `S ⊨ P ⊕ Q` says both a `P`-outcome and a `Q`-outcome are *actually
reached*, and together they cover `S`. Their motivating example is
`⟨true⟩ b := shuffle(a) ⟨⊕_{π∈Π(a)} (b = π)⟩` — *every* permutation reachable
and nothing else.

**So writing an Ada bounded-error site as `⌈a⌉ ⊕ ⌈b⌉ ⊕ ⌈c⌉` would convert a
PERMISSION into an OBLIGATION.** The standard permits a conforming
implementation to produce *one* of the permitted outcomes; `⊕` would assert that
*all three are realizable*. That is a strictly stronger — and for Ada, false —
claim. Membership sites are `□` over a disjunctive state predicate and nothing
else.

Be careful in the other direction too: OL's `∨` is not what we want either.
`S ⊨ P ∨ Q` means *all* outcomes satisfy `P`, or *all* satisfy `Q`. The
disjunction belongs **inside** the atomic state predicate.

### 5.5 What `⊕` genuinely buys — a fourth verdict we cannot currently state

There is one claim `⊕` expresses that nothing in our vocabulary can:

> **every permitted outcome is realizable by some admissible schedule.**

That is the check for an **over-permissive** semantics — our permitted set is
too wide, or our schedule space is too coarse. It is a real and distinct
verdict, and it is a `⊕` claim. Recorded as available, not as owed.

### 5.6 The trichotomy — a genuine gap in our taxonomy, free to fix

OOPSLA'23 **Theorem 5.6** says a specification `⟨φ⟩ C ⟨⊕ᵢ Qᵢ⟩` is false iff
**exactly one** of three things holds:

1. a **desired outcome is never reached**;
2. an **undesired outcome is sometimes reached** (the only one IL can express);
3. the program **diverges**.

**Our taxonomy names (2) and (3) and does not name (1).** "The expected outcome
never occurs" and "a bad outcome occurs" are currently both DIVERGE-with-witness
with different witnesses. That is a real distinction and it is the one that
would have caught P11: `BoundRefines` was *false*, then *vacuous*, and
`recursionStep_vacuous` was a one-liner — the failure mode was precisely
"the expected outcome is unreachable", dressed as a theorem that could not fail
loudly. This costs a vocabulary entry and nothing else.

### 5.7 Price, risk, verdict

**What we would write in Lean 4** (statement-level only, no machinery):

```lean
-- (illustrative — the statement form, not a tree file)
def box  (P : Σ → Prop) : OAssert M Σ := fun m => ∀ σ ∈ supp m, P σ   -- □, demonic
def diam (P : Σ → Prop) : OAssert M Σ := fun m => ∃ σ ∈ supp m, P σ   -- ♢, angelic
```

**The obstacle, stated honestly: our monad does not branch.** OL's execution
model (Def. 3.3) needs (1) a monad, (2) a **partial commutative monoid**
`⟨MA, ⋄, ∅⟩` for every `A`, and (3) `⋄` distributing over `bind`.
`ExceptT ρ (StateT W Halt)` satisfies (1) and (3) and satisfies (2) only
**degenerately** — the sole PCM on a deterministic monad is the trivial one, and
under it `⊕` collapses to a disjunction-with-emptiness that buys nothing. To
make the apparatus bite you must first **reify** the schedule quantification
into the monad (`M Σ = Set (Except ρ Σ × W)`, the image of the run function over
the admissible schedule set) — and §3.4's ruling *"nondeterminism enters as an
explicit PARAMETER … the monad stays deterministic and the ∀ lives at theorem
level"* says we deliberately chose not to. **That ruling is not overturned by
this survey.** It is a good ruling: it is what keeps `fuelMono`, the threshold
form and `mvcgen` untouched.

**No Lean 4 (or Coq/Isabelle) mechanization of Outcome Logic or Incorrectness
Logic exists** — searched web, arXiv, GitHub and the project page; the papers
are pen-and-paper with appendix proofs. Building one would be first-of-kind,
which cuts both ways.

| item | price | risk | verdict |
|---|---|---|---|
| **The `□`/`♢` single-triple statement form, and the names** (demonic/angelic, Lisbon triple, manifest error) | a vocabulary section in `docs/family-architecture.md` §4.3/§5.2; **zero Lean** | none — it renames, it does not restate | **ADOPT-NOW** |
| **Theorem 5.6's trichotomy** — add "expected outcome unreachable" as a verdict distinct from "bad outcome reachable" | one vocabulary entry; the emitters already distinguish the cases in practice | low; §9.4's shared-vocabulary machinery is the landing place | **ADOPT-NOW** |
| **The `⊕` warning** — never spell a membership site with `⊕` | one sentence | **not adopting it is the risk**; it would silently strengthen every Ada verdict into a falsehood | **ADOPT-NOW (as a prohibition)** |
| **The full BI/PCM/⊕ apparatus in Lean** | PCM + BI frames + classical-BI `⊕` from scratch; no library exists | high; and it needs the schedule reification §3.4 declined | **NOT-FOR-US, because** the monad does not branch and the ruling that keeps it deterministic is a good one |
| **OL for concurrency** | — | — | **NOT-FOR-US, because** it is silent on our actual hard part: TOL contains **zero** occurrences of "concurrent", "interleaving" or "schedule". Nothing here helps derive admissible schedules from SV's event regions or Go's memory model |

**Does §0.1 survive?** Yes, and this is the cleanest case in the survey. Every
adopted item is a **name for a claim we already make**, so no ∀ is narrowed and
no definition changes. The one item that *would* have weakened something —
spelling membership with `⊕` — is rejected for exactly that reason, pointed the
other way: it would have **over**-claimed, which is the same fault.

---

## §6 Relational Hoare logic, product programs, simulation — and the paper that says don't have two semantics

**The pains:** P6 (`twinAgrees`, the unpaid adequacy bill), old-vs-new interpreter
transport, and the C twin's fidelity gate.

### 6.1 The finding, first

The brief asked whether there is a cheaper *relational* proof form than two WP
proofs plus a bridge. The survey's answer has three parts and only the first two
are what the brief expected.

1. **Relational Hoare logic is the wrong instrument for us, and it is wrong for a
   structural reason, not a maturity reason.** Its judgement is indexed by **two
   commands under one semantics**; ours is **one command under two semantics**.
2. **Simulation is the right instrument, and Lean 4 already has some of it.**
3. **The strongest result in this area is a paper arguing we should not have a
   second semantics at all — and it describes our current architecture as the
   good one.**

### 6.2 Why RHL does not fit, stated precisely

Benton, "Simple relational correctness proofs for static analyses and program
transformations", POPL 2004, pp. 14–25, DOI 10.1145/964001.964003 [secondary,
via Naumann's restatements — the primary PDF could not be retrieved]. The
judgement is `C ∼ C' : ℛ ⇒ 𝒮`, and the only rules that give leverage are the
**diagonal** ones:

* `dIf` (AltAgree) carries the side condition `ℛ ⇒ (e ≐ e')` — the two guards
  must **agree** on related stores;
* `dWh` (IterAgree) carries `𝒬 ⇒ (e ≐ e')` and requires the two loops to have
  the **same shape** and exit together.

**Our two interpreters violate both.** The fuel side takes an administrative
decrement at every recursive call and its guard includes `fuel > 0`; the
fuel-free side has no counterpart. `dWh`'s guard-agreement condition is not
merely hard to discharge — it is *unsatisfiable as stated*.

The fallbacks are the interesting part, because one of them is our status quo:

* **one-sided rules** (pair one side with `skip`) handle a **bounded** mismatch —
  peeling an iteration, a hoisted statement — not a data-dependent one;
* **`SeqProd`** drops to **self-composition** (Barthe, D'Argenio & Rezk, "Secure
  information flow by self-composition", CSFW 2004 [secondary]): rename the
  variables and prove one unary triple of `C; C'`. Nagasamudram & Naumann,
  "Alignment completeness for relational Hoare logics", LICS 2021 (arXiv
  2101.11730) [secondary] show `SeqProd` + Hoare logic is **Cook complete but
  not alignment complete**, and that recovering lockstep proofs through it
  *requires full functional specification of each side separately*.

> **That last sentence is a description of `twinAgrees`.** Two independent WP
> proofs plus a hand bridge **is** self-composition, and RHL's fallback rule
> re-derives it rather than improving on it. RHL cannot price down what it
> already is.

**Product programs** (Barthe, Crespo & Kunz, "Relational verification using
product programs", FM 2011, LNCS 6664, 200–214, DOI
10.1007/978-3-642-21437-0_17; and "Beyond 2-safety: asymmetric product programs
for relational program verification", LFCS 2013, LNCS 7734, DOI
10.1007/978-3-642-35722-0_3 [both secondary]) have the right pitch — build one
program encoding both executions, then run an **ordinary unary VC generator**,
so `mvcgen` survives. Two honest problems. (i) Fuel-vs-no-fuel is a
**refinement** (a ∀∃ property), not 2-safety, so we need the *asymmetric*
construction, not the FM 2011 one. (ii) **The construction demands the
alignment**, and for a structural mismatch the aligned product *is* the bridge
theorem written out. Alignment automation is an open problem: Shemer, Gurfinkel,
Shoham & Vizel, "Property directed self composition", CAV 2019; Churchill,
Padon, Sharma & Aiken, "Semantic program alignment for equivalence checking",
PLDI 2019, DOI 10.1145/3314221.3314596; Dickerson, Mukherjee & Delaware,
"KestRel: relational verification using e-graphs for program alignment", OOPSLA
2025 (arXiv 2404.08106) — all three are **heuristic searches**, none handles an
unbounded data-dependent shape difference unaided [all skimmed].

### 6.3 The one RHL-family result that fits — and the shortcut it hands us

**Kenji Maillard, Cătălin Hriţcu, Exequiel Rivas, Antoine Van Muylder, "The Next
700 Relational Program Logics", *PACMPL* 4(POPL), Article 4, 2020, DOI
10.1145/3371072 (arXiv 1907.05244)** [secondary]. Its distinguishing property is
exactly our case: it is **heterogeneous** — `M₁` and `M₂` may be *different*
monads. A relational specification monad `Wrel(A₁,A₂)` is a **relative** monad
over the product functor; a relational effect observation is a lax morphism
`θrel : M₁A₁ × M₂A₂ → Wrel(A₁,A₂)`; and the judgement is just
`θrel(c₁,c₂) ≤ w`. `Ret`, `Bind` and `Weaken` come for free from any such θ, and
Benton's RHL is recovered as one instance.

**But read it backwards and it collapses into something we can afford today.**
Both our interpreters map into the **same** unary specification monad — Lean
already provides it, as `Std.Do.wp`. So instead of instantiating a relational
logic, prove the single equation:

```lean
-- (illustrative — the collapse, not a tree file)
theorem wp_transport (p : Prog) (Q : PostCond α _) :
    wp⟦shallowTwin p⟧ Q = ⨆ n, wp⟦deepInterp n p⟧ Q
```

and every unary triple already proved on one side rewrites to the other. **When
two effect observations land in one specification monad and can be proved
*equal* rather than merely *related*, the relational logic degenerates to a
rewrite.** That is the single highest-leverage relational idea in this survey
for P6, and it costs no new logic.

Note the honest shape: it is a **sup over fuel**, not a bare equation, because
the fuel side can fail where the shallow side cannot. A sup is a refinement, and
refinement is ∀∃ — which is why §6.4's determinism side conditions earn their
keep.

### 6.4 Simulation — the right statement form, and Lean 4 has a start on it

CompCert's `common/Smallstep.v` (Leroy) [secondary, source-level restatement]
bundles a forward simulation as a well-founded `order`, a `match_states`
relation, and one diagram, with four shapes:

| shape | source step ⇒ target |
|---|---|
| `forward_simulation_step` | exactly one |
| `forward_simulation_plus` | one or more |
| `forward_simulation_opt` | zero or one, stuttering guarded by a `measure : state → Nat`, silent branch only |
| `forward_simulation_star` / `_star_wf` | zero or more, guarded by a measure or a well-founded order |

and the direction flip:

```
forward_simulation L1 L2 → receptive L1 → determinate L2 → backward_simulation L1 L2
```

**Three reasons this fits us and RHL does not.**

1. **Indexing.** A simulation is indexed by two `semantics` and quantifies over
   the program. That is our shape with no contortion.
2. **Stuttering is the whole point.** Our mismatch *is* stuttering — the fuel
   interpreter takes administrative steps the twin does not.
   `forward_simulation_star` with a measure exists for exactly that, and RHL's
   only analogue (one-sided rules) handles bounded mismatch only.
3. **Determinism buys the converse free.** Both our interpreters are
   deterministic, so `receptive`/`determinate` are near-trivial and the backward
   direction comes without a second proof. **That is the specific saving over
   two-proofs-plus-a-bridge.**

**Lean 4 support is real and partial.** `leanprover/cslib` — the Lean Computer
Science Library — ships `Cslib/Foundations/Semantics/LTS/Simulation.lean`
(`IsSimulation`, `Similarity`, `SimulationEquiv`, composition/union lemmas,
lifting to multi-step traces) and `Bisimulation.lean` (**heterogeneous**
bisimulation between two different LTSs, weak bisimulation over τ, up-to
techniques, and `Bisimilarity.deterministic_bisim_eq_traceEq`) [secondary].
It is LTS-flavoured rather than CompCert-flavoured — no `index`/`order`/measure
stuttering diagrams and no `forward_to_backward_simulation` — so those would be
ported. **This is the closest Lean 4 has to `Smallstep`, and it is a dependency
decision, not a research project.**

**What does NOT exist in Lean 4**, checked: `Std.Do` is strictly unary (no
relational entry point, no product-program support, no refinement judgement);
there is no maintained equivalent of Isabelle's `transfer`/`lifting`, which is
the cheap mechanized answer to old-vs-new interpreter transport in
Isabelle-land — **we would be building that ourselves.** The one relational
program logic in Lean 4 is domain-specific: `Verified-zkEVM/VCV-io` has a
pRHL-inspired `RelTriple` with `rvcgen`/`rvcstep` tactics over a probabilistic
oracle monad for cryptographic game hopping. Not reusable, but a proof of
concept that a **relational VC generator can be built in Lean 4**.

### 6.5 The paper that argues against the twin — and it describes our architecture

**Scott Owens, Magnus O. Myreen, Ramana Kumar, Yong Kuan Tan, "Functional
Big-Step Semantics", ESOP 2016, LNCS 9632, DOI 10.1007/978-3-662-49498-1_23**
[secondary]. In CakeML the **clocked (fuelled) recursive interpreter *is* the
official semantics**. There is no second relational semantics to reconcile.
Claimed advantages: a better induction theorem, **less duplication**,
accessibility, and easy symbolic simulation by rewriting. Every intermediate
language in the CakeML compiler is defined this way. The supporting lemmas are
**clock monotonicity** and **determinism** — which are `fuelMono` and our
`.ok`-uniqueness, already ours.

> **This is a peer-reviewed endorsement of the architecture we already have, and
> it is an argument against the shallow twin rather than for it.** Our fuel
> index is not a wart to be apologised for; it is the design a verified-compiler
> group chose deliberately and defended in print. The mvcgen pilot's ruling
> *"Python: bridge, do not migrate"* is CakeML's argument, arrived at
> independently.

Three corroborating data points, all of them warnings:

* **CompCert maintains two and pays.** Campbell, "An executable semantics for
  CompCert C", CPP 2012 [secondary], proves the executable interpreter both
  **sound and complete** against the inductive small-step semantics. And the
  honest signal: the twin later **drifted and was rewritten** upstream. That is
  our old-vs-new transport pain observed in the wild, and it is the
  model-always-matches-code law's external evidence.
* **JSCert/JSRef is exactly our architecture, and its residual assurance came
  from tests.** Bodin, Charguéraud, Filaretti, Gardner, Maffeis, Naudziuniene,
  Schmitt, Smith, "A trusted mechanised JavaScript specification", POPL 2014,
  DOI 10.1145/2535838.2535876 [secondary]: an inductive spec plus an extracted
  interpreter, with a Coq proof that JSRef is **correct w.r.t.** JSCert — *for
  chapters 8–14 only*, and **not** completeness, and **not** for the whole
  language. The rest came from **test262**. **That is a direct precedent for a
  fidelity gate by testing being the accepted price at this scale**, and it is
  the argument for keeping `ctwin`'s rule-14 gate rather than proving it.
* **K's founding argument** (Roșu & Șerbănuță, "An overview of the K semantic
  framework", *JLAP* 2010 [skimmed]) is that equivalence proofs between
  multiple semantics are so complex they consume years. Reported rather than
  quoted; the phrasing is unverified.

### 6.6 Price, risk, verdict

| item | price | risk | verdict |
|---|---|---|---|
| **The `wp_transport` collapse** — one sup-over-fuel equation, then unary triples rewrite | two induction lemmas we largely have (`fuelMono`, adequacy) + one `wp`-level corollary. **No new logic, no new tactic, `mvcgen` untouched.** | the two `wp`s may only be `≤`-related, not equal, if the fuel side can fail where the twin cannot — then it is refinement, and §6.4's determinism conditions are needed | **PILOT** — the cheapest form of P6, and it should be the *shape* `twinAgrees` is written in |
| **Simulation as the statement form** (`match_states`, stuttering measure, determinism flip); `cslib` as the substrate | define a `Semantics` record + `match_states`, discharge one diagram; port CompCert's `index`/`order`/measure shapes onto `cslib`'s LTS ones. **Inventing `match_states` is irreducible** — no technique in this survey removes it | a new dependency (`cslib`) against the core-only law; and if the twin ever uses `partial def`, "steps" is not well defined on that side | **PILOT** for `twinAgrees` and for **old-vs-new transport**, where §6.2 has nothing to offer |
| **CakeML's "one semantics" verdict** — do not acquire a second semantics we do not have to | free; it is a decision | none — it is what the pilot already recommended | **ADOPT-NOW as a citation.** `docs/family-architecture.md` §3.4's adequacy rule should cite ESOP 2016 rather than rest on our own reasoning |
| **JSCert precedent for a test-based fidelity gate** | free | none | **ADOPT-NOW as a citation** for `ctwin`'s gate and the differential harness |
| **Relational Hoare logic, Benton-style** | build the logic + rules + a tactic; nothing exists in Lean 4 | the leverage rules do not apply; you land in `SeqProd` = today's cost | **NOT-FOR-US for the interpreter twin.** Reconsider only for the **C twin**, which genuinely is two programs — nearest precedent Mazzucato, Mohamed, Lee, Barrett, Grundy, Harrison, Păsăreanu, "Relational Hoare logic for realistically modelled machine code", CAV 2025 (arXiv 2505.14348) [skimmed], HOL Light, s2n-bignum |
| **Product programs** | the asymmetric construction + projection lemmas | the alignment is the bridge theorem restated | **NOT-FOR-US-YET.** One live dissent: Wu, Wu & Cao, "Encode the ∀∃ relational Hoare logic into standard Hoare logic", OOPSLA 2025 (arXiv 2504.17444) [skimmed] claims the ∀∃ pattern can be pushed **inside assertions** via an `Exec` predicate so relational steps become standard unary steps — no ghost state, no invariant duplication. If that mechanizes cleanly it *is* the cheap relational form the brief asked for. Unmechanized in Lean; watch it |

**Does §0.1 survive?** Yes for everything adopted. `wp_transport` and simulation
are both *theorems about* the definition, not changes to it; the CakeML citation
strengthens the existing adequacy rule rather than relaxing it. The one item
that would touch the trust boundary — replacing the definition with the twin —
is exactly what the adequacy rule already forbids without a proof, and §6.5
supplies external evidence for that rule rather than against it.

---

## §7 Four more, each against a named pain

### 7.1 Loop invariants — Houdini is a REFUTATION engine, and that is why it ports

**The pain:** P10.

**Papers.** Cormac Flanagan & K. Rustan M. Leino, "Houdini, an Annotation
Assistant for ESC/Java", FME 2001, LNCS 2021, 500–517, DOI
10.1007/3-540-45251-6_29 [secondary]. Michael D. Ernst, Jake Cockrell, William
G. Griswold, David Notkin, "Dynamically Discovering Likely Program Invariants to
Support Program Evolution", *IEEE TSE* 27(2):99–123, 2001 (Daikon) [secondary].
Jeremy W. Nimmer & Michael D. Ernst, "Static verification of dynamically
detected program invariants: Integrating Daikon and ESC/Java", RV 2001
[secondary]. Juan P. Galeotti, Carlo A. Furia, Eva May, Gordon Fraser, Andreas
Zeller, "Inferring Loop Invariants by Mutation, Dynamic Analysis, and Static
Checking" (DYNAMATE), *IEEE TSE* 2015 (arXiv 1407.5286) [skimmed]. Background:
Cousot & Cousot, POPL 1977, DOI 10.1145/512950.512973; Bradley, "SAT-Based Model
Checking without Unrolling", VMCAI 2011, DOI 10.1007/978-3-642-18275-4_7 [both
skimmed].

**The mechanism, and why it is safe here.** Houdini does not *infer*; it
**refutes**. Hand it a large candidate set from cheap syntactic templates, assume
them all, run the checker, delete everything refuted, repeat. Termination is
trivial (the set shrinks), and the fixpoint is the **unique maximal subset of the
candidate set that is inductive**. **Inside Lean this carries zero soundness
risk by construction — the kernel is the filter.** The only question is
throughput.

This is the general pattern behind three of the four items in this section, and
it is worth naming: **untrusted oracle, checked certificate.** Houdini,
IC3/Spacer, Daikon-plus-prover and CIVL's SMT-discharged mover checks are all
"something guesses, the trusted core verifies".

**Two honest limits.**

* **The grammar gap.** Daikon's templates cover ranges, nullness, sortedness,
  linear scalar relations. They do **not** generate the invariant `mvcgen`
  loops actually need, which is fold-shaped: `out = f (xs.take i)`. That is
  derivable **syntactically from the loop body**, not by observation. So
  observation is a **side-condition** finder, not a main-invariant finder.
* **Houdini's failure mode.** The maximal inductive subset can still be too weak
  to prove the goal, and Houdini gives **no signal** about which missing
  conjunct would have saved you. It is conjunctive-only; disjunctive invariants
  are out of reach.

**The cheapest win is not on the list.** In Lean specifically, **many loops need
no invariant at all if reformulated as `List.foldl`/`Array.foldl` and proved via
a generalized induction lemma**. Strengthening the induction hypothesis is the
same intellectual problem, but it moves the work into a **reusable lemma
library** instead of a per-loop annotation. And this is *already how our estate
is shaped* — the R-track's `fold_depth1` is a fold. **Before investing in any
mining pipeline, measure what fraction of our loops that reformulation kills.**

**Verdict.**

| item | price | risk | verdict |
|---|---|---|---|
| **Measure the fold-reformulation fraction** | one census over the estate's loops; a Python instrument per §5.4 | none | **ADOPT-NOW** — it is a census, and censuses are what this project does before it builds |
| **Houdini loop over `mvcgen invariants`** — generate candidates, elaborate, drop the refuted conjunct, repeat | each iteration is a full Lean elaboration: ~30 candidates × ~5 rounds ≈ 150 `mvcgen`+`grind` runs per loop. **An offline batch job, not an interactive tactic** — and under Amendment 11 that is a large ticket | conjunctive-only; no signal on what is missing | **PILOT, and late.** Behind the fold census and behind §1.5 |
| **Daikon-style observation from our fixtures** for **side conditions only** (bounds, non-emptiness, monotone counters, index < length) | we already have the instrumentation point — a kernel-executable interpreter and a differential harness | fixture bias is a *cost* (one wasted elaboration), not a correctness hazard | **PILOT** — high-yield for exactly the class that makes `grind` fail on an otherwise-correct invariant |

### 7.2 Ghost state — the cheapest technique in this document

**The pain:** threading step counters, touched-key sets and schedule prefixes by
hand; and P4b's frame tower.

**Papers.** Susan Owicki & David Gries, "An axiomatic proof technique for
parallel programs I", *Acta Informatica* 6:319–340, 1976, DOI 10.1007/BF00268134
[secondary] — auxiliary variables, with the soundness condition that is the
whole content: an auxiliary variable may be **assigned** anywhere but may
**never be read by real code, never appear in a guard, never influence control
flow**. Jean-Christophe Filliâtre, Léon Gondelman, Andrei Paskevich, "The Spirit
of Ghost Code", CAV 2014, DOI 10.1007/978-3-319-08867-9_1; journal version
*FMSD*, DOI 10.1007/s10703-016-0243-x [secondary] — the criterion as a
type-and-effect discipline: ghost code must be erasable *"without any observable
difference in the program outcome"*, i.e. **ghost data cannot participate in
regular computations, and ghost code cannot mutate regular data or diverge**.
Jung, Krebbers, Jourdan, Bizjak, Birkedal, Dreyer, "Iris from the ground up",
*JFP* 28:e20, 2018 [secondary] — ghost state as an element of a user-chosen
resource algebra, which is strictly more than an extra field. Abadi & Lamport,
"The Existence of Refinement Mappings", LICS 1988 / *TCS* 82(2):253–284, 1991,
and Jung, Lepigre, Parthasarathy, Rapoport, Timany, Dreyer, Jacobs, "The future
is ours: prophecy variables in separation logic", *PACMPL* 4(POPL), 2020, DOI
10.1145/3371113; and the easier formulation, Lamport & Merz, "Prophecy Made
Simple", *TOPLAS* 44(2), Article 6, 2022, DOI 10.1145/3492545 [all secondary].

**The adoption shape, and it has no proof obligation at all.** Split the record
and keep the real step's *type* free of ghost data:

```lean
-- (illustrative — the discipline, not a tree file)
structure St where
  real  : RealState
  ghost : GhostState              -- steps : Nat, touched : List Key, sched : List Event

def step (a : Action) (s : St) : St := ⟨realStep a s.real, ghostStep a s⟩
```

Then the Owicki–Gries erasure obligation — `erase (step a s) = realStep a (erase s)`
with `erase := St.real` — is closed by **`rfl`**. **`realStep` literally cannot
read `s.ghost` because it is not in scope.** And Filliâtre et al.'s termination
clause, which people forget, is free in Lean: our functions are total.

**Risks, and they are real.**

* **Scope creep into control flow.** The moment someone writes
  `if s.ghost.steps > 100 then …` in a real transition, erasure breaks and every
  downstream theorem silently becomes a theorem about the *instrumented*
  program. **Lean will not warn you.** Mitigation is a type signature, not a
  lint: keep `realStep : Action → RealState → RealState` as the only thing that
  touches real state and never give it an `St`.
* **Proof-term bloat.** Ghost fields appear in every state-indexed goal and
  every `simp` set. Prefer `Nat` counters and `List` prefixes over set-like
  structures, whose decidability instances degrade `grind` across the whole
  development.
* **Prophecy is premature.** You need it only when the abstract model resolves a
  nondeterministic choice **later** than the concrete one. For SV (§7.3) the
  direction is the other way, which forward simulation handles. Do not reach for
  it until a forward simulation attempt actually fails — and when it does, read
  Lamport & Merz before Jung et al.

**Verdict: ADOPT-NOW** for the structural discipline (price ≈ zero; one field,
one projection, `rfl`), **NOT-FOR-US-YET** for resource algebras and prophecy.
Note the contrast with everything else in §7: ghost state is **not** an
oracle-plus-checker, it is a **discipline**, and its soundness rests on an
erasure obligation Lean will not remind you about. Structuring the record so
erasure is `rfl` is what removes that risk.

### 7.3 Refinement — we already have the right statement, and it has a name

**The pain:** P9 — SV's cycle model vs the event-region scheduler.

**Papers.** Ralph-Johan Back & Joakim von Wright, *Refinement Calculus: A
Systematic Introduction*, Springer 1998, DOI 10.1007/978-1-4612-1674-2; Carroll
Morgan, *Programming from Specifications*, Prentice Hall, 1990/1994 [both
skimmed]. **He, Hoare & Sanders, "Data Refinement Refined", ESOP 1986, LNCS 213,
187–196, DOI 10.1007/3-540-16442-1_14** [secondary] — *note the correction to
the brief: the author order is He, Hoare, Sanders, and the year is **1986**, not
1987*. Nancy Lynch & Frits Vaandrager, "Forward and Backward Simulations, Part
I: Untimed Systems", *Information and Computation* 121(2):214–233, 1995, DOI
10.1006/inco.1995.1134 [secondary]. Jean-Raymond Abrial, *Modeling in Event-B*,
CUP 2010, with the proof-obligation list per the Rodin User Manual [secondary].
Peter Lammich, "Refinement for Monadic Programs", *AFP* 2012, and "Automatic
Data Refinement" (Autoref), ITP 2013, DOI 10.1007/978-3-642-39634-2_9 [skimmed].

**The finding: `docs/sv-r1-scheduler.md` §5.3 already writes the right theorem.**

```lean
theorem cycleOf_runRegion (d : Design) (h : d.isCycleFragment = true)
    (σ : ScheduleOracle) (fuel : Nat) (stim : List SvState) :
    (runRegion d σ fuel stim).map cycleOf = run d σ fuel stim
```

That is **Event-B's INV + SIM**, with the *witness* obligations (WFIS, WWD)
vanishing because `cycleOf` is a **function**, not a relation — no `∃` to
witness — and GRD vanishing because both steps are total. Two theorems, and the
lane already priced the hard one honestly: *"That is a genuine theorem, and it
is the honest price of the rung."*

**What the literature adds is three things, all cheap.**

1. **The vocabulary and the obligation checklist.** Event-B's list — INV, GRD,
   MRG, SIM, FIS, WFIS, WWD, VAR, NAT, WD, THM, EQL — is the completeness check
   on a hand-rolled refinement. Notably: **deadlock-freedom is NOT generated**;
   Event-B makes you state relative deadlock freedom yourself. Worth knowing
   before we assume a refinement proof covers it.
2. **The name for the coupling: the *gluing invariant*.** And the practical
   warning that comes with it — **the gluing invariant is the artefact you
   iterate on.** Budget the effort at `Inv` (NBA queue well-formedness, no
   pending region transitions, event-queue invariants), not at the simulation
   square. This matches the SV lane's own "three things need real work".
3. **The precise trigger for backward simulation**, which is the one thing a
   hand-rolled refinement can get wrong silently: **forward simulation fails
   exactly when the concrete system resolves a nondeterministic choice EARLIER
   than the abstract one**, because you must pick the abstract witness at the
   moment of the concrete step and the deciding information is not yet
   available. Lynch & Vaandrager's contribution is that forward and backward are
   each **individually incomplete** and their **composition is complete** —
   which is the same fact Abadi & Lamport state as "history + prophecy suffice".
   *History variables are the ghost-state form of forward simulation; prophecy
   variables are the ghost-state form of backward simulation.* That sentence
   ties §7.2 and §7.3 together and is worth recording.

**The cheap test to run before committing:** does the abstract cycle model ever
defer a choice that the concrete scheduler has already made *and that is not
recoverable from the concrete state*? If not, forward is enough. Prefer to keep
it that way by making the abstract model resolve **at least as early**.

**One risk the SV lane should check before the shape is frozen:**
**mid-cycle observability.** If anything can observe a mid-region state — a
`$display` in the Observed region, a PLI callback, a testbench read — then a
boundary-only statement is too weak and the obligation becomes **trace-level**
rather than state-level. Retrofitting that is expensive. Given §6.3's ruling
that all fifteen regions including the six PLI regions are in scope, **this is
not a hypothetical.**

**Verdict.** **ADOPT-NOW as vocabulary and as a checklist** (Event-B's PO list,
"gluing invariant", the forward/backward trigger, the deadlock-freedom
exclusion). **NOT-FOR-US: building a general refinement framework in Lean.**
There is no Lean 4 equivalent of Lammich's Isabelle Refinement Framework, and
**building one for a single obligation is the trap** — the boundary-restricted
functional form the SV lane already has needs a `def` and two `theorem`s.

### 7.4 Lipton movers — the reference confirmed, and the theorem is about RACE-FREE DESIGNS

**The pain:** P7.

**The citation, confirmed exactly as the brief required:**

> **Richard J. Lipton, "Reduction: A Method of Proving Properties of Parallel
> Programs", *Communications of the ACM*, Volume 18, Issue 12, December 1975,
> pages 717–721, DOI 10.1145/361227.361234.**

Verified against dblp (`journals/cacm/Lipton75`) and cross-checked against the
CACM vol. 18 table of contents. **`docs/family-architecture.md` §3.6's
parenthetical citation is correct** — it is just under-specified, and this
document supplies the rest.

**The definitions and the theorem.** `a` is a **right mover** iff for every
action `b` of every *other* thread, `σ →ᵃ s →ᵇ σ'` implies `∃t. σ →ᵇ t →ᵃ σ'`;
**left mover** is the mirror; **both mover** is both. `P` (acquire) is a right
mover; `V` (release) is a left mover. **Reduction theorem:** a block matching
**`R* · A? · L*`** — any number of right movers, then at most one arbitrary
action, then any number of left movers — may be treated as **atomic**, so
properties proved of the coarse-grained program transfer to the fine-grained
one. Lipton treats halting and deadlock-freedom **separately**; the safety
transfer is the easy half.

**The modern line, for when we need it.** Elmas, Qadeer & Tasiran, "A calculus
of atomic actions" (QED), POPL 2009, DOI 10.1145/1480881.1480885 — alternate
**abstraction** (weaken an action to make it a better mover) with **reduction**
(merge adjacent actions), because the two are mutually enabling. Hawblitzel,
Petrank, Qadeer & Tasiran, CAV 2015, DOI 10.1007/978-3-319-21668-3_26; Kragl &
Qadeer, "Layered Concurrent Programs", CAV 2018, DOI
10.1007/978-3-319-96145-3_5 — CIVL. Flanagan & Freund, "Mover Logic", ECOOP
2024 (arXiv 2407.08070) — the cleanest declarative rule set. Chajed, Kaashoek,
Lampson & Zeldovich, "Verifying concurrent software using movers in CSPEC",
OSDI 2018 — **fully machine-checked in Coq, 13 layers**, the existence proof
that mover-based layering is tractable in an ITP. [all skimmed]

**Partial-order reduction is not an alternative here, and the reason is sharp.**
Flanagan & Godefroid, "Dynamic partial-order reduction for model checking
software", POPL 2005, DOI 10.1145/1040305.1040315 [skimmed]. **POR is a search
with a soundness meta-theorem; movers are a proof rule.** POR yields "no
counterexample within these bounds" for a *fixed finite* configuration.
Formalising the exploration algorithm and its soundness inside Lean and then
running it in the kernel would cost far more than the proof rule it replaces,
and it still would not give a ∀-schedule statement for an unbounded system.
**Movers are the right primitive for an ITP** — that answers the brief's
question directly.

**The adoption shape, and it is smaller than CIVL suggests.**

```lean
-- (illustrative — the minimal apparatus, not a tree file)
def footprint : Act → List Loc                     -- reads ∪ writes

theorem commute_of_disjoint {a b : Act} (h : Disjoint (footprint a) (footprint b)) :
    step a ∘ step b = step b ∘ step a

def RaceFree (d : Design) : Prop :=
  ∀ a b, SameRegion a b → a ≠ b → Disjoint (footprint a) (footprint b)

theorem schedule_independent (d : Design) (h : RaceFree d) :
    ∀ s t₁ t₂, RunRegion s t₁ → RunRegion s t₂ → t₁ = t₂
```

**`commute_of_disjoint` is the whole trick.** A realistic SV region alphabet is
~6–10 constructors, i.e. **30–90 ordered pairs** — genuinely unpleasant by
hand. Proving commutativity **once, parametrically in footprint disjointness**
turns 30–90 semantic proofs into **one semantic proof plus n² footprint
computations**, most of which close by `decide`/`simp`. That is exactly what
CIVL's *linear permissions* buy in the automated setting. And Mathlib supplies
the lift: `Relation.ReflTransGen` and `Relation.church_rosser` in
`Mathlib.Logic.Relation` take a local diamond to global confluence without
reproving Newman's lemma.

**THE HONEST POINT, and it is the most important sentence in §7:**

> **"∀ schedules produce the same outcome" is NOT a theorem about the
> scheduler. It is a theorem about RACE-FREE DESIGNS.** SystemVerilog
> deliberately leaves the outcome of same-region races unspecified — two
> blocking assignments to the same variable in the Active region legitimately
> produce schedule-dependent results. **`RaceFree` is not a technicality to
> discharge later; it is half the content**, and the theorem must be stated
> that way from day one.

This is also §0.1 principle I pointing at itself: the honest ∀-schedule theorem
carries a hypothesis, and dropping the hypothesis to make the theorem prettier
would be narrowing the ∀ — the one move the doctrine forbids. And it connects
straight to §7.3: `schedule_independent` is **what licenses `cycleOf` to be a
function at all**.

**Second risk, and it is the real attack surface: footprint soundness.** If
`footprint` under-approximates — a missed implicit read, a sensitivity-list
trigger, a shared queue — then `commute_of_disjoint` is still *true* but we
apply it where it does not hold, and the confluence theorem becomes vacuously
misleading. **Prove `footprint` sound against the semantics** (`step a s`
depends only on `s` restricted to `footprint a`) rather than asserting it. That
is P11's lesson in a new place.

**Third: safety only.** Reduction and confluence give same-final-state. They do
**not** give termination or deadlock-freedom; those need a variant or a
wait-for-graph argument, exactly as Lipton had to treat them separately.

**Fourth: Go is a bigger project than SV.** Go's memory model is weak, channel
operations are genuinely **one-sided** (a send right-moves past an unrelated
receive but not symmetrically), and racy programs are undefined. Expect the full
mover apparatus there, over the memory model rather than an interleaving of
source statements.

**Verdict.**

| item | price | risk | verdict |
|---|---|---|---|
| **Confirm and upgrade the Lipton citation** in §3.6 | free | none | **ADOPT-NOW** |
| **State the ∀-schedule theorem WITH its `RaceFree` hypothesis** | free; it is a statement decision | **not doing it is the risk** — the unqualified theorem is false | **ADOPT-NOW** |
| **`commute_of_disjoint` + `footprint` + `Relation.church_rosser`** for SV within-region | a few hundred lines, dominated by getting `footprint` **sound** | footprint under-approximation is silent | **PILOT** — and it is the SV lane's, not this one's |
| **Full `R*·A?·L*` mover apparatus** | larger | — | **NOT-FOR-US-YET.** Reach for it at the first genuinely one-sided action (a lock, a channel op, a bus grant). Read CSPEC's layer decomposition first |
| **CIVL's layered-program discipline, wholesale** | — | — | **NOT-FOR-US, because** its economics depend on SMT discharging the mover and gate checks. Without that backend, layering **multiplies** obligations rather than dividing them |
| **Partial-order reduction** | — | — | **NOT-FOR-US, because** it produces a bounded search result, not a universally quantified theorem |

---

## §8 THE TABLE — every idea, one row

Verdicts: **A** = adopt-now, **P** = pilot, **N** = not-for-us-because.
"Pain" refers to §0's ledger.

| # | idea | source | pain | what adopting looks like | price | risk | verdict |
|---|---|---|---|---|---|---|---|
| 1 | **`Std/Internal/Do/` + the `vcgen` tactic exist at our pin** — frame rule, `@[frameproc]`, `until`, `frames`, `with grind` | `[source]`, §2.1 | P1 P2 P4 P4b P5 | a census in `lean-structures-census.md`'s shape + one experiment file | ~1 day, 1 ticket | `Std.Internal` is explicitly unstable; `ExceptT`-outside undemonstrated; `Halt` needs a `WPMonad` | **A** |
| 2 | **`mvcgen`'s `jp` knob** — default is *"exponential blowup of VCs"*, `+jp` is *"linear in the number of control flow splits"* | `[source]`, §1.5 | P1 P2 | two runs on the existing four-deep gate + a 20-line repro | 1 ticket, ~hours | `+jp` is *"slightly lossy"*; may strand arms at `⊢ False` | **A** |
| 3 | **Leroy & Grall Lemma 14** — with `fuelMono`, `∃t.∀F≥t, … = .ok` ⟺ `∃F, … = .ok`; divergence is `∀F, … = .Halt` | I&C 207(2) 2009 §5 `[read]` | P3 | name `Denote`, prove Lemmas 12–17 once, restate the 13 files | days; probe on `star_lab/spec.lean` first | the *fraction* of the 13 files' plumbing this deletes is unmeasured | **P** |
| 4 | **`WP.Frames.of_wp_conjunctive`** — "F is preserved" ⟹ framing, with `⊓`, no `∗` | `[source]`, §2.2 | P4 P4b | one preservation lemma per primitive; `PstAt` is already the object | small, once #1 lands | needs `WPConjunctive` for our stack | **P** |
| 5 | **`wpgen`-style characteristic formulae** over our AST | Charguéraud ICFP 2010/2011, SLF, CakeML ESOP 2017 `[read]` | P1 P2 P12 | `Core/Wpgen.lean` + x-tactics; the interpreter is traversed **once, forever** | **1 100–2 300 lines** (≈half without `∗`) | reduction control; loops+fuel is research; ~1 000 lines of metaprogramming we maintain | **P**, gated on #1, #2 and a 150-line spike |
| 6 | **The modifies-clause metatheorem** — `exec F σ s = .ok σ' v → ∀ k ∉ writes s, σ'.heap[k]? = σ.heap[k]?` | Region Logic, *JACM* 60(3) 2013 `[secondary]` | P4 | 4 defs, ~5 lemmas, one induction; framing stated as an **iff** | small | fails exactly where two *unknown* sub-heaps must be disjoint | **P** (the fallback, and a good one) |
| 7 | **`WPMonad.of_frameClosure`** with a real `∗` on a **projection** of `W` | `[source]` + Nigron & Dagand ITP 2021 `[secondary]` | P4 P4b | ~250–350 lines by the in-core blueprint | 4 obligations: `PreservesSup`, assoc, unit, base `WPMonad` | unstable API; layer order undemonstrated | **P**, gated on #1 |
| 8 | **`wp_transport`** — one sup-over-fuel equation, then unary triples rewrite | "Next 700 Relational Program Logics", *PACMPL* 4(POPL) 2020, read backwards `[secondary]` | P6 | `wp⟦twin⟧ Q = ⨆ n, wp⟦deep n⟧ Q` | two induction lemmas we largely have | may be `≤` not `=`, i.e. refinement | **P** — the shape `twinAgrees` should be written in |
| 9 | **Simulation diagrams** (`match_states`, stuttering measure, determinism flip); `leanprover/cslib` as substrate | CompCert `Smallstep` `[secondary]`; cslib `[secondary]` | P6, old-vs-new transport | a `Semantics` record + `match_states` + one diagram | inventing `match_states` is irreducible | a new dependency vs the core-only law | **P** |
| 10 | **CakeML's "one semantics" argument** — the clocked functional interpreter *is* the semantics | Owens, Myreen, Kumar, Tan, ESOP 2016 `[secondary]` | P6 | a citation in §3.4's fuel ruling | free | none | **A** |
| 11 | **JSCert precedent** — spec + extracted interpreter, proof for chapters 8–14 only, **the rest from test262** | Bodin et al. POPL 2014 `[secondary]` | P6, `ctwin`'s gate | a citation defending the differential gate | free | none | **A** |
| 12 | **`□`/`♢` over ONE Outcome Logic triple**, and the name **Lisbon triple** for DIVERGE-with-witness | Total Outcome Logic (arXiv 2411.00197, **preprint**); O'Hearn POPL 2020 `[read]` | P8 | a vocabulary section in §4.3/§5.2; **zero Lean** | free | none — it renames, it does not restate | **A** |
| 13 | **Theorem 5.6's trichotomy** — "expected outcome unreachable" is a verdict we do not name | Outcome Logic, OOPSLA 2023 `[read]` | P8 P11 | one vocabulary entry under §9.4 | free | none | **A** |
| 14 | **The `⊕` prohibition** — never spell a membership site with outcome conjunction | Outcome Logic §5 `[read]` | P8 | one sentence | free | **not adopting it is the risk**: `⊕` turns a permission into an obligation | **A** |
| 15 | **Ghost state as a STRUCTURAL discipline** — split the record so `erase = St.real` and the Owicki–Gries obligation is `rfl` | Owicki & Gries 1976; "The Spirit of Ghost Code" CAV 2014 `[secondary]` | step counters, touched keys, schedule prefixes | one field, one projection, `rfl` | ≈ zero | scope creep into control flow is **silent**; proof-term bloat | **A** |
| 16 | **Event-B's PO checklist + "gluing invariant" + the forward/backward trigger** | Abrial 2010; Lynch & Vaandrager I&C 121(2) 1995; He, Hoare & Sanders ESOP **1986** `[secondary]` | P9 | vocabulary and a completeness check on `cycleOf_runRegion` | free | **deadlock-freedom is NOT generated**; mid-cycle observability would force a trace-level obligation | **A** |
| 17 | **Lipton's citation, confirmed** — *CACM* 18(12), Dec 1975, 717–721, DOI 10.1145/361227.361234 | dblp + CACM ToC `[secondary]` | P7 | upgrade §3.6's parenthetical | free | none | **A** |
| 18 | **State the ∀-schedule theorem WITH its `RaceFree` hypothesis** | §7.4 | P7 | a statement decision | free | **the unqualified theorem is false** — SV leaves same-region races unspecified | **A** |
| 19 | **`commute_of_disjoint` + `footprint` + `Relation.church_rosser`** | Lipton 1975; Mathlib `[secondary]` | P7 | prove commutativity **once**, parametric in disjointness: 30–90 pairs become footprint computations | a few hundred lines | **footprint under-approximation is silent** — prove `footprint` sound, do not assert it | **P** (SV lane's) |
| 20 | **Measure the fold-reformulation fraction** — how many of our loops need no invariant if written as `foldl` + a generalized induction lemma | §7.1 | P10 | a census instrument per §5.4 | small | none | **A** |
| 21 | **Houdini over `mvcgen invariants`** — candidates in, refuted conjuncts out, maximal inductive subset | Flanagan & Leino FME 2001 `[secondary]` | P10 | an offline batch job | ~150 elaborations per loop — a **large** Amendment-11 ticket | conjunctive-only; no signal on what is missing | **P**, late |
| 22 | **Daikon-style observation from our fixtures, for SIDE CONDITIONS only** | Ernst et al. TSE 2001; Nimmer & Ernst RV 2001 `[secondary]` | P10 | reuse the differential harness as the instrumentation point | small | the grammar cannot produce fold-shaped main invariants | **P** |
| 23 | **Time credits** — the literature's fuel-aware WP; threshold composition **is** credit addition | Atkey ESOP 2010; Charguéraud & Pottier *JAR* 2019; Mével, Jourdan & Pottier ESOP 2019 `[secondary]` | P3 | `⦃P ∗ $t⦄ e ⦃Q⦄` | needs `∗`, hence #7 | not independent — it is an **application** of the frame layer | **P**, far behind #7 |
| 24 | **`wpRec` + `petrol`** — a fuel-free WP whose soundness is stated against a fuel-driven runner | Swierstra & Baanen, *PACMPL* 3(ICFP) art. 103, 2019 §6 `[read]`; McBride MPC 2015 | P3 P10 | the statement form for a `Kont`-shaped WP | — | **partial correctness only** — `mayPT P (Step Abort _) = ⊤`, so it never yields `∃t` | **P** as a statement form; see #3 first |
| 25 | **Interaction trees / QPF codata / `partial_fixpoint` as the interpreter** | Xia et al. POPL 2020 `[read]`; Mathlib `[source-level]` | P3 | — | — | **breaks kernel-reducible runs**; and in Lean `MvQPF.Cofix` is a *quotient of a fuel-indexed tower* | **N** |
| 26 | **CFML the tool** (external OCaml→Coq generator + axioms) | ICFP 2010 §1.3, 2011 §2.4 `[read]` | — | — | — | **§0.1 principle I forbids it** — an unverified translator influencing the definition layer | **N** |
| 27 | **Relational Hoare logic, Benton-style**, for the interpreter twin | POPL 2004 `[secondary]` | P6 | — | — | wrong indexing; `dWh`'s guard-agreement is **unsatisfiable** for fuel-vs-no-fuel; the fallback `SeqProd` **is** today's cost | **N** for the twin; reconsider for the **C twin** |
| 28 | **Product programs / self-composition** | Barthe, Crespo & Kunz FM 2011 / LFCS 2013 `[secondary]` | P6 | — | — | the alignment **is** the bridge theorem restated; alignment automation is an open problem | **N-yet**; watch Wu, Wu & Cao OOPSLA 2025 (∀∃ into standard HL) |
| 29 | **The full BI/PCM/`⊕` apparatus for Outcome Logic** | Zilberstein et al. `[read]` | P8 | — | — | our monad **does not branch**, so `⊕` degenerates; making it bite needs schedule reification, which §3.4 deliberately declined | **N** |
| 30 | **Iris / `iris-lean`'s `ProgramLogic`** | JFP 2018 `[secondary]` | P4 | — | — | 3.4 MB and a `Language`/`EctxLanguage` interface `SemM` does not fit, to get a `∗` we can define in 30 lines | **N** |
| 31 | **CIVL's layered-program discipline, wholesale** | Kragl & Qadeer CAV 2018 `[skimmed]` | P7 | — | — | its economics need SMT discharging mover and gate checks; without it layering **multiplies** obligations | **N** |
| 32 | **Partial-order reduction** | Flanagan & Godefroid POPL 2005 `[skimmed]` | P7 | — | — | a bounded **search** with a soundness meta-theorem, not a universally quantified **theorem** | **N** |
| 33 | **Prophecy variables** | Abadi & Lamport 1988; Jung et al. POPL 2020; Lamport & Merz TOPLAS 2022 `[secondary]` | P9 | — | — | needed only when the abstract model resolves *later* than the concrete; SV's direction is the other way | **N-yet** — read Lamport & Merz first if forward simulation ever fails |
| 34 | **HITrees** — ITree structure in a non-guarded type theory, in Lean, by **defunctionalization** (which is `Kont`) | arXiv 2510.14558 `[skimmed]` | P3 | — | — | — | **WATCH** — read before any future ITree-shaped proposal |

---

## §9 THE TOP THREE

Ranked by (simplification × confidence) / cost. The ranking has an uncomfortable
shape and it is worth saying plainly:

> **The three best deals in a survey of the program-verification literature are
> two facts about our own toolchain and one theorem from 2009. None of them
> requires building anything, and all three were available before this document
> was written.**

### 1. Census `Std/Internal/Do/` and the `vcgen` tactic at the pin

**Because we have been pricing a build against a capability we may already own.**
`Std/Internal/Do/WP/Frame.lean` (© 2026 Lean FRO, Sebastian Graf) gives a frame
rule with **four obligations and no cancellativity, no step-indexing, no
resource algebra**; `@[frameproc]` gives frame inference; and the `vcgen`
tactic's grammar ships `until` (stop VC generation at a pattern — §3's
anti-duplication lever), `frames`, and `with grind` *"so it can share `vcgen`'s
internalised E-graph"* — which is `docs/lean-structures-census.md` §2's
grind-seam recommendation, measured there at **12 VCs → 0**, built into the
tactic instead of wired by a `macro_rules` line.

* **Simplification:** potentially the largest in this document — it touches P1,
  P2, P4, P4b and P5 at once.
* **Confidence:** **certain** that it is there (read twice, at the pin);
  **unknown** whether it applies to `ExceptT ρ (StateT W Halt)`. That is exactly
  what a census answers.
* **Cost:** one docs-only census plus one experiment file, in the shape
  `docs/mvcgen-pilot.lean` and `docs/lean-structures-census.lean` already
  established — out of the pinned build by construction. **One ticket.**
* **Risk:** `Std.Internal` is explicitly internal and will move. The census must
  report that as a first-class finding, not a footnote — an unstable API under a
  family-wide substrate is a supply-chain fact to price, exactly as
  `docs/mvcgen-pilot.md` §5.4 priced `mvcgen`'s experimental warning.

### 2. Re-measure the four-deep gate with `+jp`

**Because it is one token against a fourteen-minute wall.** Core's own docstring
says the default *"causes exponential blowup of VCs"* and that `+jp` yields a
formula *"linear in the number of control flow splits"*. Neither of our two
recorded measurements — P1's ceiling and P2's `⊢ False` — names its `jp`
setting, so **we do not currently know whether the four-deep gate has ever been
tried on the linear encoding.** That is §5.4a's provenance law applied to a
tactic option: *a number carries the state it was measured in, and the state
includes the tactic's configuration.*

* **Simplification:** if it closes, P1 dissolves and §3's 1 100–2 300 lines are
  not spent.
* **Confidence:** certain the knob exists and is documented; roughly even that
  it helps.
* **Cost:** two runs. **Take it in the same ticket as #1.**
* **Risk:** the lossiness may bite exactly where the gate needs the
  discriminant. Then we have a *characterised* wall instead of an unexplained
  one, plus a precise upstream report — and §3's case gets stronger, because
  characteristic formulae are the design that is **linear AND lossless**.

### 3. Cash in Leroy & Grall's Lemma 14

**Because the 13 fuel-family files may be carrying plumbing a 2009 theorem
deletes.** Our `∃ t, ∀ F ≥ t, exec F w = r` is *character for character* their
`D(a,r) ≜ ∃p, ∀n ≥ p, Cₙ(a) = r`, with `Cₙ` a fuel-indexed evaluator returning a
distinguished `⊥` that is our `Halt`. Given monotonicity (their Lemma 12, our
`fuelMono`), Lemma 14 collapses the threshold for every non-`Halt` outcome, and
Lemma 15 makes divergence `∀ F, exec F w = .Halt` with no threshold either.
CakeML's top-level `semantics` is built on exactly this.

* **Simplification:** 13 files, and it changes **nothing** about the model —
  `exec` stays total, structurally recursive and **kernel-reducible**, `#guard`
  keeps firing, nothing in the TCB moves.
* **Confidence:** high. The theorem is published and mechanised in Coq, and its
  only premise is one we largely have.
* **Cost:** a probe on one file first — `Examples/python/star_lab/spec.lean`
  (102 lines, one `fuelMono`) is the obvious candidate — then a generic
  Lemmas-12–17 file, then a mechanical restatement.
* **Risk:** **the fraction of the 13 files' plumbing that is the `∀ F ≥ t` half
  is unmeasured.** Measure it on one file before restating thirteen. And
  co-ordinate with the rebuild lane: the fuel structure changes there anyway
  (fuel is spent per `Kont` level, not per node).

**Honourable mentions**, in order: the `□`/`♢` + **Lisbon triple** + trichotomy
vocabulary (§5, free, and it retires three ad-hoc judgements); the **ghost-state
structural discipline** (§7.2, price ≈ zero, obligation `rfl`); and **`RaceFree`
as a hypothesis on every ∀-schedule theorem** (§7.4, free, and the unqualified
theorem is false without it).

---

## §10 NOT ADOPTED, FOR THE RECORD

Stated so a future reader does not re-propose them without new evidence:
**CFML the tool** (an unverified OCaml→Coq generator plus axioms — §0.1
principle I's exact prohibition); **interaction trees, QPF codata and
`partial_fixpoint` as the interpreter** (all three break kernel-reducible runs,
and in Lean the fuel-free model is a quotient of a fuel-indexed tower);
**Benton-style relational Hoare logic for the interpreter twin** (wrong
indexing; the leverage rules are unsatisfiable for fuel-vs-no-fuel and the
fallback is today's cost); **product programs** (the alignment is the bridge
theorem restated); **Outcome Logic's `⊕` apparatus** (our monad does not branch,
and reifying schedules into it would overturn §3.4's deliberate ruling);
**Iris / `iris-lean`'s `ProgramLogic`** (an `EctxLanguage` interface `SemM` does
not fit); **CIVL's layered discipline wholesale** (its economics are SMT's);
**partial-order reduction** (a bounded search, not a theorem); **prophecy
variables** (SV's nondeterminism resolves in the direction forward simulation
handles).

And two corrections to the brief's own citations, made before anything is cited:
**Rensink is not in the characteristic-formula lineage** (Aceto &
Ingólfsdóttir's survey cites him zero times), and **"Data Refinement Refined" is
He, Hoare & Sanders, ESOP 1986** — not 1987, and not that author order.

---

## §11 WHAT THIS SURVEY DID NOT DO

Stated plainly, because §5.4a's law cuts both ways and a survey that hides its
gaps is a flattering instrument.

1. **No Lean was run.** Amendment 11 covers all Lean execution and Thomas's
   training owns the machine. Every Lean-side claim is either a **source
   reading** at the pin (graded `[source]`, with file and line) or an **unrun
   hypothesis explicitly labelled as one**. In particular: **nothing in §1.5,
   §2.1 or §2.2 has been executed.** The `+jp` behaviour, the `⊢ False`
   mechanism, `WPMonad.of_frameClosure` at `ExceptT`-outside, and the existence
   of a `WPMonad` instance for `Halt` are all **owed measurements**.
2. **Three numbers are quoted from other lanes and re-measured by nobody here**
   — the 568 ms twin timing, the 8 M-heartbeat wall, and the 259-vs-12 VC
   count. Two of those already carry a provenance warning in their own lane's
   record.
3. **The `docs_check.py` marker convention was honoured**, and every Lean block
   in this document is either quoted verbatim from the pinned toolchain (with a
   path in prose) or marked `-- (illustrative — …)`. **None is a tree file.**
4. **Some identifiers are unverified**, and are marked as such at the point of
   use. Where a DOI or page range could not be resolved independently, the
   title, venue and year are given and the identifier is flagged. **Nothing was
   fabricated to fill a slot**; a missing identifier is recorded as missing.
   Three sources are **preprints without a peer-reviewed venue** and are labelled
   so: Total Outcome Logic (arXiv 2411.00197), HITrees (arXiv 2510.14558), and
   the ∀∃-into-standard-HL encoding (arXiv 2504.17444).
5. **No paper was vendored into the repository.** Everything is cited; nothing
   is copied beyond short quoted phrases, and no fetched file was added to the
   tree — so no per-file license question arises.
6. **The survey is biased toward what our pains name.** Whole areas with no
   recorded pain to attach to — probabilistic program logics, cost semantics
   beyond time credits, type-and-effect systems, synthesis — were not searched.
   That is deliberate and it is a limit.
