# The mvcgen pilot — measured

**The question.** *Do we have to implement an mvcgen tactic for each language?
Or can we convert everything into monads such that we can use the "default"
Lean mvcgen tactic?*

**The hypothesis under test** (validate or refute, not assume): one fuel-indexed
`StateT World (Except Refusal)` monad family + one `WPMonad` instance + Lean
std's `mvcgen` + per-language `Spec` lemmas replaces the hand-rolled per-language
VC machinery.

**Every claim below is a run.** The experiment file is
[docs/mvcgen-pilot.lean](mvcgen-pilot.lean) — zero `sorry`, zero
`native_decide`, `#print axioms` on every theorem, and **out of the pinned
build by construction** (`lakefile.toml`'s globs are the `LeanModels` lib root
and `Examples.+`; nothing under `docs/` is either). Run it with
`lake env lean docs/mvcgen-pilot.lean`. **No `lake build` was run for any
measurement in this report** — the build lock was never needed.

---

## THE VERDICT, first

**Split, and the split is not a hedge — it is where the measurement falls.**

1. **The monad half of the hypothesis is CONFIRMED, and it is cheaper than
   hoped.** `mvcgen` is on the pinned toolchain (`leanprover/lean4:v4.33.0-rc1`);
   the bump price is **zero**. The stack we need synthesizes a `WPMonad` with
   **zero instances written**. And the repo's own `Run σ α` **is** that stack —
   proved, not asserted: `ofRun`/`toRun` are mutually inverse in 22 lines
   (§2 of the experiment file). "Convert everything into monads" is not a rewrite
   of the semantics; it is a re-presentation of a type the tree already has.

2. **The fuel half is REFUTED as stated, and the refutation is sharp.** Three
   routes, all measured. Fuel *inside* the monad **does not elaborate at all** —
   it is a definability failure, not a proof failure. Fuel *outside* the monad
   (today's shape) is definable, but at a **symbolic** fuel `mvcgen` returns the
   goal **unchanged after 1 m 31 s**. Only the **fuel-free** route — an unbounded
   loop made total by a measure — is one `mvcgen` walks natively. So
   `∃ t, ∀ F ≥ t, run F = .ok w v` is not a thing `mvcgen` produces or consumes;
   it is assembled around it.

3. **Therefore: `mvcgen` does not replace the per-language VC machinery. It
   replaces the per-language *tactic*, on the fuel-free fragment only, and only
   if you also maintain a per-language *second semantics* and its adequacy
   proof.** GATE 3 (`value_scores`) is proved through the monadic route in §4 of
   the experiment file — the same fact, the same premises, clean axioms — but
   the subject is a shallow twin, not `execStmts sunfish (F + 10)`. The bridge
   between them is an adequacy theorem nobody has written and the differential
   harness does not validate.

**Recommendation.** Adopt the monad + `@[spec]` substrate for new tiers, use
`mvcgen` on fuel-free slices only, keep the threshold assembly by hand at the
fuel-recursive points, do **not** migrate Python mid-campaign, and take two of
the pilot's laws into `@[py_spec]` practice today at zero cost. Prices in §5.

---

## §0 RECKONING WITH THE 2026-08-13 SPIKE

`docs/backlog.md` §*`mvcgen` — SPIKED AND DECLINED, on shape, not on taste*
already answered a narrower question (*does leanpy use something like mvcgen?*)
and declined on three obstacles. **This pilot does not overturn that verdict for
Python. It retires one obstacle, confirms two with numbers, and adds a question
the spike was not asked.**

| the spike's obstacle | this pilot's measurement |
|---|---|
| **1. "`Run` is not a monad."** *A plain `inductive` with a hand-rolled bind, no `Monad` instance, no `WP` instance.* | **RETIRED as a permanent obstacle — it was a fact about the tree, not about the type.** `Run σ α` **is** `ExceptT PyErr (StateT σ (Except Loud))`, proved both ways in 22 lines (§2 of the experiment file), and that stack's `WPMonad` synthesizes with **zero instances written**. The instance was never unavailable; it was never asked for. |
| **2. "The verification object is DATA, not a program."** | **CONFIRMED, and now PRICED.** GATE 3 through mvcgen needed a monadic *shallow twin*; the bill is `twinAgrees`, an adequacy theorem for a second semantics (§5.1). But the obstacle is a **cost, not a wall**: the twin is executable through `toRun` (`#guard`ed on a fixture) so it could join the differential harness, and the fuel-free fragment it covers is large. |
| **3. "The fuel threshold has nowhere to live."** | **CONFIRMED, and now EXPLAINED.** Three routes measured (§2). In the monad: **not definable**. Outside it, at symbolic fuel: mvcgen returns the goal **unchanged after 1 m 31 s**. The only route it walks is fuel-free, which costs kernel-reducible runs — i.e. `#py_check`. |
| **"stock `mvcgen` adds nothing because this project already built its own generator"** | **Still true for Python, and the machinery has GROWN since:** `VC2.lean` 706 → **939**, `VCTactic.lean` 2 403 → **3 371**. That cuts both ways: it strengthens *"already built"* for Python, and it raises the bill for **each new tier that would have to build its own** — which is the question the spike was never asked. |

**What is genuinely new here** is §4: the per-language marginal cost for tiers
that do not exist yet. The 2026-08-13 spike scoped itself to leanpy, where the
generator is built and paid for. C, SV and Go have not paid, and the choice they
face is between ~120 lines of substrate per language and another 5 343-line
walker per language. That is the decision this pilot is evidence for.

---

## §1 THE CAPABILITY CENSUS

### 1.1 The toolchain: no bump, and no package

| question | measured answer |
|---|---|
| pin | `leanprover/lean4:v4.33.0-rc1` (`lean-toolchain`) |
| `Std.Do` at the pin | **yes** — 21 files under the toolchain's `src/lean/Std/Do/`, 2 under `Std/Tactic/Do/` |
| the `mvcgen` tactic at the pin | **yes** — `Lean/Elab/Tactic/Do/VCGen.lean`, syntax declared in `Std/Tactic/Do/Syntax.lean:436` |
| price of a toolchain bump | **zero — none is required** |
| package cost | **zero** — `Std.Do`/`Std.Tactic.Do` are CORE; `lakefile.toml` and `lake-manifest.json` are untouched |

The lane-wide risk a bump would have carried (it touches every lane) **does not
arise**. This retires the caveat in `docs/family-architecture.md` §3.4 by an
independent second measurement.

**One flag, recorded because it is real.** `mvcgen` warns on every use:

```
The `mvcgen` tactic is experimental and still under development.
Avoid using it in production projects.
```

(`Lean/Elab/Tactic/Do/VCGen.lean:456`; silenced by
`set_option mvcgen.warning false`, which the experiment file does.) A tactic
whose own authors say that is a supply-chain fact to price, not a footnote —
see §5.4.

### 1.2 The import boundary, measured

| symbol | import needed |
|---|---|
| `@[spec]` | **none** — it is a builtin attribute, which is why `LeanModels/Python/Logic.lean` already uses it |
| `Std.Do.Triple`, `PostShape`, `SPred`, `PostCond` | `import Std.Do` |
| the `mvcgen` / `mspec` / `vcgen` tactics | `import Std.Tactic.Do` |

Measured: a file importing only `LeanModels.Python.Semantics` answers
`unknown namespace Std.Do` and ``to use `mvcgen`, please include
`import Std.Tactic.Do` ``. So `Std.Do` is **not** transitively in scope from the
Python tier today; adopting it means two `import` lines per consuming file, of
core modules. The `core-only` law is not violated: these are Lean core.

### 1.3 mvcgen's contract on our monad shapes

`WPMonad` instances shipped at the pin (`Std/Do/WP/Monad.lean:53–105`): `Id`,
`StateT`, `ReaderT`, `ExceptT`, `OptionT`, `EStateM`, `Except`, `Option`,
`StateM`, `ReaderM`. They **compose**, so every stack this family needs resolves
with nothing written:

```
#synth WPMonad (StateT World (Except Refusal)) (.arg World (.except Refusal .pure))
-- StateT.instWPMonad
#synth WPMonad (ExceptT PyErr (StateT FrameState (Except Loud)))
               (.except PyErr (.arg FrameState (.except Loud .pure)))
-- ExceptT.instWPMonad
```

**THE LAYER ORDER IS FORCED — and `docs/family-architecture.md` §3.4 has it
backwards.** That document's illustrative substrate is

```
abbrev SemM (W : Type) (ρ : Type) := StateT W (ExceptT ρ Halt)
```

`StateT` **outside** `ExceptT` discards the state on a raise. `Run`'s `.exn`
**retains** it (docs/memory-model.md v2; AGENTS.md: *"state retained on `.ok`
AND `.exn`"*), and `PyPost.err : PyErr → FrameState → Prop` is state-aware for
exactly that reason. The difference is visible in the `PostShape` and is decided
by `rfl`:

```lean
-- docs/mvcgen-pilot.lean (excerpt — §1, the layer order)
/-- `StateT W (ExceptT ρ (Except L))` — the state is GONE in the `ρ` barrel. -/
example : ExceptConds (.arg W (.except ρ (.except L .pure)))
    = ((ρ → ULift Prop) × (L → ULift Prop) × Unit) := rfl

/-- `ExceptT ρ (StateT W (Except L))` — the `ρ` barrel SEES the world. -/
example : ExceptConds (.except ρ (.arg W (.except L .pure)))
    = ((ρ → W → ULift Prop) × (L → ULift Prop) × Unit) := rfl
```

The failure barrel of the first cannot mention `W` at all. So the substrate is
`ExceptT ρ (StateT W Halt)`, and the two are **not** interchangeable. This is a
one-line correction to a load-bearing sketch, and it is worth making before any
tier is written against it.

**And `Run σ α` IS that stack.** §2 of the experiment file gives the
isomorphism with both directions proved (`toRun_ofRun`, `ofRun_toRun`;
axioms `[Quot.sound]` and `[propext, Quot.sound]`), with
`Loud := Unit ⊕ String` carrying `.timeout`/`.unsupported` — the two arms that
discard state — and `PyErr` carrying `.exn`, which does not.

### 1.4 A bug in Std at this version, and its workaround

`Spec.throw_Except` (`Std/Do/Triple/SpecLemmas.lean:484`) is declared under a
`variable {m} {ps}` block it does not use:

```
@[spec]
theorem Spec.throw_Except [Monad m] [WPMonad m ps] :
  Triple (MonadExceptOf.throw e : Except ε α) (spred(Q.2.1 e)) Q := by simp [Triple.iff]
```

`m` and `ps` are not determined by the conclusion. Measured consequence: a bare
polymorphic `throw` inside `StateT W (Except ε)` leaves goals

```
case vc2.m  ⊢ Type ?u.89 → Type ?u.88
case vc3.ps ⊢ …
case vc4.inst / vc5.inst ⊢ …
```

and the declaration is rejected outright:

```
error: declaration `get!_spec` contains universe level metavariables at the expression
  Spec.throw_Except.{?u.89, ?u.88, 0}
```

**The workaround is what the architecture wants anyway:** never write a bare
`throw` in interpreter code — route every refusal through a **named** primitive
with its own `@[spec]` lemma (`refuse`/`liftRes` in the experiment file). Doing
so removed all four metavariable goals. Record it as a rule, not a hack: a
refusal is a first-class notion in this family, and mvcgen rewards making it one.

### 1.5 Loop invariants, and the shape mvcgen hands back

For an unbounded `while` in do-notation over `StateT W (Except ε)`, `mvcgen`
applies `Spec.repeatM` and leaves exactly this (measured, §3 of the experiment
file):

| goal | what it is | `py_vcgen`'s name for it |
|---|---|---|
| `inv1 : WhileVariant (Int × Int) ps` | the termination MEASURE | `(dec := …)` |
| `inv2 : WhileInvariant (Int × Int) (Int × Int) ps` | the loop INVARIANT, on an `α ⊕ β` cursor (`.inl` = continue, `.inr` = break) | `(inv := …)` |
| `vc1.step.isTrue` | preservation **and** strict measure decrease, one goal | preservation + decrease |
| `vc2.step.isFalse` | the exit algebra | exit algebra |
| `vc3.pre` | the initial invariant | initial invariant |
| `vc4.post.success` / `vc5.post.except` | the two landing arms | the `ret` fork |

**The correspondence is one-to-one.** `py_vcgen`'s interface was arrived at
independently and matches core's. `mvcgen` also suggests invariants
(`mvcgen [f] invariants?`), which produced a usable skeleton on the first try.
Usability note: the sugar `mvcgen? [f]` left the goal **untouched** in our runs;
`mvcgen [f] invariants?` is the form that works.

`Lean.Order.MonadTail` — what `Spec.repeatM` needs — has instances for `StateT`
(given `Nonempty σ`) and `Except`, so this too costs nothing.

---

## §2 THE FUEL QUESTION, answered by three runs

Our form is `∃ t, ∀ F ≥ t, run F = .ok w v` — a threshold plus monotonicity.
Where can the fuel live?

### Route A — fuel as a monad LAYER: **not definable**

```lean
abbrev FT := StateT Nat (StateT World (Except Refusal))
def tick : FT Unit := do match ← get with | 0 => throw .timeout | f + 1 => set f
def loopF : FT Int := do
  tick
  let w ← getThe World
  if w.n ≤ 0 then pure w.n else do
    modifyThe World (fun w => { w with n := w.n - 1 })
    loopF
```

```
error: fail to show termination for loopF
with errors
failed to infer structural recursion:
no parameters suitable for structural recursion

well-founded recursion cannot be used, `loopF` does not take any (non-fixed) arguments
```

**This is the whole answer to "a `FuelT` layer you would write ONCE".** Fuel's
job is to *be* the structural recursion argument. Hidden in monadic state it is
not an argument, so the interpreter does not exist to have a `WPMonad` instance.
No instance you could write repairs this. `docs/family-architecture.md` §3.4's
ruling — *"Fuel stays OUT of the monad"* — is confirmed, and the reason is
stronger than the one recorded there (*"every triple carries it"*): the
alternative does not typecheck.

### Route B — fuel as an explicit ARGUMENT (today's shape): **mvcgen does nothing**

```lean
def triF : Nat → Int → Int → Int → M Int
  | 0,      _, _,     _ => refuse .timeout
  | fuel+1, n, total, i => if i ≤ n then triF fuel n (total + i) (i + 1) else pure total

example (F : Nat) (n : Int) (hn : 0 ≤ n) :
    ⦃fun _ => ⌜True⌝⦄ triF F n 0 1 ⦃⇓ r => fun _ => ⌜2 * r = n * (n + 1)⌝⦄ := by
  mvcgen [triF]
```

leaves, after **1 m 31 s**, exactly one goal:

```
case vc1
⊢ ∀ (s : World), (wp⟦triF F n 0 1⟧ (PostCond.noThrow fun r x => ⌜2 * r = n * (n+1)⌝) s).down
```

The goal is the goal. `triF F` at a symbolic `F` does not reduce, so there is
nothing to walk. Nothing in `Std.Do` speaks about a **relation between two runs
at different fuels**: `Triple` is a unary predicate on one program, while
`fuelMono` and the threshold form are statements about a *family* indexed by
fuel. They stay outside the WP layer, exactly where `LeanModels/Python/VC.lean`
already puts them.

### Route C — no fuel, total by a MEASURE: **native, and it closes**

The `tri` of `Examples/python/tri`, written as a Lean monadic program with an
ordinary `while`, proved by `mvcgen` with a measure and an invariant, in §3 of
the experiment file. **13 lines of proof**, axioms
`[propext, Classical.choice, Quot.sound]`. Compare `py_vcgen`'s 8-line proof of
the same arithmetic through the *deep* interpreter (AGENTS.md's exemplar).

### What this means

The three routes are not three options; they are one available route and two
walls. To use `mvcgen` natively you must **remove fuel**, which removes
kernel-reducibility of runs — and `#py_check`, `py_check` and `py_vcgen`'s
captured runs are all kernel `rfl` at fuel 4096. That is not a proof-layer
change. It is a semantics change, and it deletes the tier's entire non-vacuity
discipline.

**But there is a real third thing, and it is what §3 exploits.** Large parts of
the interpreter need no fuel: `evalM` in the experiment file is *structural on
`Expr`*, and GATE 3's whole slice carries no fuel numeral anywhere. Fuel is owed
only at `callIn`/`execWhile`/`execFor`/`heapEq`/generators. **mvcgen is usable
exactly on the fuel-free fragment, and that fragment is not small.**

---

## §3 THE WORKED COMPARISON — GATE 3, both ways

The target is `value_scores` (`Examples/python/sunfish/value_bound.lean:270`),
GATE 3 of the `Position.value` inch: `score = pst[p][j] - pst[p][i]` on the
shipped sunfish, stated in the row's own entries so it names no 120-wide
constant. Statement and premises exist, and the backlog records the cost.

The monadic proof is `value_scores_M` (§4 of the experiment file): the **same
fact**, the gate's **own premises**, through a monadic shallow twin of the
`evalExpr` path the gate exercises.

### 3.1 The numbers

| | `value_scores` (real gate) | `value_scores_M` (monadic twin) |
|---|---|---|
| statement lines | **15** | **20** (13 extra `Span` binders, because the twin states the literal directly instead of `rw [hlit]`) |
| named premises | 14, plus `pstG` in supply | **14** — the same fourteen |
| proof lines | **8** | **14** (8 `have`s, `mvcgen`, 3 closing lines) |
| supply in the same file | `vlScore_lit` 6 + `pstG` 3 = **9** | primitives 30 + `@[spec]` lemmas 26 + twin interpreter 12 = **68** |
| substrate, shared across ALL gates | `VC.lean` 546 + `VC2.lean` 939 + `VCTactic.lean` 3371 + `LoopTactic.lean` 487 = **5343** | monad + `PostShape` + iso = **28** |
| FIRST gate, all in | 32 (+ 5343 substrate) | 102 (+ 28 substrate) |
| MARGINAL gate | statement + proof | statement + proof + a spec lemma per NEW primitive |
| `#print axioms` | `[propext, Classical.choice, Quot.sound]` | **identical** |
| fuel | `F + 10` | **none** — the slice is fuel-free |
| elaboration | file 24 s / 51 declarations (recorded: proofs 14 s, `#guard`s 10 s) | `mvcgen` step **568 ms**; the pilot's 13 declarations add **3–7 s** over an 8.5–10.4 s import |
| **subject** | **`execStmts sunfish (F + 10)` — the shipped interpreter on the real module literal** | **`execM` — a second semantics** |

The last row is the verdict. Everything above it favours the monadic route or is
a wash; that row is not a wash.

### 3.2 The fidelity gap, stated exactly

The twin drops **one premise and one mechanism**. The real `.name` arm consults
the static `globalsFold` before the live view — which is why the gate needs
`pstG` and why its proof erases `-globalsFold, -globalsStep`. The twin's
`resolve` is locals-then-globals and needs neither. So `value_scores_M` is the
same *statement* about a *slightly smaller* interpreter. Closing that gap is
part of the bridge, not separate from it.

The twin **is executable**: `toRun (execM …) ⟨fxW, fxE⟩` computes `score = 20` on
a fixture, pinned by `#guard` in the experiment file. So it *could* join
`harness/diff_test.py` and be validated against CPython like the real one. That
is the mitigation — and its price is a second interpreter to keep in sync, under
the standing law that the model always matches the code.

### 3.3 THE LAWS — which die, which persist, and one that is new

This table is the decision's substance.

| law | fate under `mvcgen` | the run that decided it |
|---|---|---|
| **altitude lemmas** (`boolChain_and_falsy`, `compare_one`) | **PERSISTS — and `@[spec]` is its registry.** The law is unchanged; it gains a first-class home. | Decisive: `mvcgen [execM, evalM, vlScoreLit, liftRes]` — primitives UNFOLDED — leaves **259+ VCs** and `mvcgen_trivial` fails outright. The same goal with the four primitives behind `@[spec]` triples leaves **12**, all pure, and closes. That is §L17's *"prove it ONCE at the chain with every operand symbolic"*, measured in mvcgen's own vocabulary. |
| **computed-shape / residue-spelling** | **PERSISTS verbatim.** | `simp [evalBinOp]` left `(match asInt (.int zj), asInt (.int zi) with …)` standing; `rfl` closed it. `hrowIdx`/`hjIdx`/`hiIdx` had to be spelled in `indexValH`'s own residue (`xs[i.toNat]?.getD .none`, after `simp` normalizes `Array.getD` to `getElem?`) — the gate's premises are spelled that way for the same reason. The law and its tactic (`show`, or here `rfl`) survive intact. |
| **two gates per `if`** | **DISSOLVES as a statement discipline; the arms remain.** You no longer write two theorems: `mvcgen` splits the `match`/`if` and hands one VC per arm **with that arm's hypothesis already in context**. The arm count is unchanged; the bookkeeping is gone. | The 4-deep `vlScore` expression tree produced 12 named VCs with `resolve s "pst" = …`-shaped hypotheses supplied, not restated. |
| **whnf-timeout = fuel-mismatch** | **MOOT on the fuel-free fragment; UNCHANGED elsewhere, because mvcgen does not reach there.** | No fuel numeral appears anywhere in `value_scores_M`, so there is no `F + 10` to mismatch. But §2 Route B shows mvcgen makes zero progress at a symbolic fuel, so at `callIn`/`execWhile` the law is not eased — the tool simply is not applicable. |
| **NEW — specs must be OUTPUT-DETERMINED** | a law mvcgen *adds*. The answer must be bound by the result binder, never taken as an input the caller guesses. | Two independent hits. (1) `get!_spec (i) (v)` with `v` an input made mvcgen instantiate `?v := b✝` — the loop *accumulator* — a wrong-but-typechecking unification that poisons every downstream VC. (2) The first `value_scores_M` left **23** VCs including dependent metavariables `?vc16 s h : RVal`. Restating both as `⇓ r => ⌜… = some r⌝` removed every metavariable: 3 VCs and 12 VCs respectively. **This applies verbatim to `@[py_spec]` and costs nothing to adopt.** |
| **NEW — `Triple` does not frame the state** | a read-only primitive must *say* it leaves the state unchanged, by pinning the pre-state (`⦃fun st => ⌜st = st0⌝⦄ … ⦃⇓ r => ⌜… ∧ st = st0⌝⦄`). | An unframed `get!_spec` leaves an unprovable `s✝ = s✝¹` in the loop's success VC. Std knows this and ships `Triple.observe` for it. `PyPost.next : FrameState → Prop` has the same shape and solves it the same way. |

**The convergence is the headline.** Four of the six rows say the campaign's
hard-won laws were the right laws. `boolChain_and_falsy` and `compare_one`
*are* `Spec` lemmas — not "in disguise", but literally: they transliterate to
`@[spec]` triples with the same premises and the same universally-quantified
operands, and the 259-vs-12 measurement is the price tag on forgetting them.

---

## §4 PHASE 3(a) — THE PER-LANGUAGE PRICE, priced on C

`docs/c-semantics-design.md`'s six pieces, each costed under the monadic
architecture (the counts are of `@[spec]` lemmas and type declarations, not of
tactic code):

| piece | monadic cost |
|---|---|
| **1 value model** (`CVal`, profile-driven widths) | **0** — not monad work; identical either way |
| **2 memory model** (`CWorld`, pointer = `(obj, offset)`) | `CWorld` is the `σ` of the `StateT` layer: **1 structure**. Primitives `load`/`store`/`alloc`/`realloc`/`free`/`addrOf`/`deref` → **~7 spec lemmas** |
| **3 UB taxonomy** (3 causes never pooled, 11 armed classes) | the causes are the `ρ` payload — either one sum or **one `.except` layer per cause**, both **free** (composition). **1** `refuse` primitive + **1** spec lemma |
| **4 the judgment** (`Run CWorld CVal`, ∃-fuel threshold, the DRAIN AMENDMENT) | the `WPMonad` is **free** by §1.3's iso. **The drain amendment at C's 181 short-circuit sites (`&&` 111, `\|\|` 28, `?:` 42) is the altitude law**: **3 `@[spec]` lemmas**, ~6 lines each by the measured pattern. **The ∃-fuel threshold is NOT free** — see the warning below |
| **5 `abort`/`exit`** | two more state-discarding arms in `Loud`: **0 instances**, **2 spec lemmas** |
| **6 `printf`** (eight conversions) | an output field on `CWorld`: **0 instances**, **1 spec lemma** |

**Total marginal cost per language: 2 type declarations + 2 `abbrev`s + ~14
`@[spec]` lemmas — call it 120 lines.** Against that, the Python tier's
hand-rolled machinery is **5 343 lines** (`VC.lean` 546, `VC2.lean` 939,
`VCTactic.lean` 3 371, `LoopTactic.lean` 487) — and that is genuinely
per-language, because it names Python's AST, Python's flow arms and Python's
loop shapes throughout.

**That saving is real, and it is bounded by §2.** `docs/family-architecture.md`
§3.4 says *"Per-language work is then exactly: the World type, the error type,
the primitive step functions, and `@[spec]` lemmas for the primitives. No
language writes a vcgen."* **True on the fuel-free fragment. False at the
fuel-recursive points**, where mvcgen makes no progress at all and each language
still needs its own threshold assembly (`execStmts_mono`, `callIn_of_…`,
`execWhile_at_least` and their kin). C's design **§4.2 explicitly chooses**
*"the ∃-fuel threshold form transfers unchanged"* — which by this pilot's
measurement is choosing the route mvcgen cannot walk at the loop and call
points. That should be a conscious decision, taken with §2's numbers on the
table, not an inheritance.

---

## §5 PHASE 3(b) — THE PYTHON BRIDGE, and 3(c) THE RECOMMENDATION

### 5.1 The adapter lemmas — signatures, not a migration

Nothing here proposes moving the `RecursionStep` campaign. These are the shapes
a bridge would take, stated so the price is visible.

`PyTriple m P ss Q := ∀ st, P st → ∃ t, ∀ F ≥ t, Q.holds (execStmts m F st ss)`
against `Std.Do.Triple x P Q := P ⊢ₛ wp⟦x⟧ Q`.

```lean
-- (illustrative — the bridge's shapes, not in the tree)

/-- `PyPost` has FIVE arms (`next`/`ret`/`brk`/`cont`/`err`); a `PostCond` has one
success barrel plus one per `.except` layer. So `ret`/`brk`/`cont` ride the SUCCESS
value as a flow sum — core's own idiom (`Spec.repeatM`'s `α ⊕ β` cursor). -/
def pyPostToPostCond (Q : PyPost) : PostCond PyFlow (PS FrameState)

/-- ADEQUACY. This is the whole price: the twin agrees with the shipped
interpreter above a threshold, statement by statement. -/
theorem twinAgrees (m : Module) (ss : List Stmt) (st : FrameState) :
    ∃ t, ∀ F ≥ t, execStmts m F st ss = toRun (execStmtsM m ss) st

/-- The bridge proper — `Std.Do.Triple` of the twin gives `PyTriple` of the
interpreter, and `twinAgrees` is what makes the ∃-threshold reappear. -/
theorem PyTriple.of_triple {m : Module} {ss : List Stmt}
    {P : FrameState → Prop} {Q : PyPost}
    (hagree : ∀ st, ∃ t, ∀ F ≥ t, execStmts m F st ss = toRun (execStmtsM m ss) st)
    (h : Std.Do.Triple (execStmtsM m ss) spred(⌜P⌝) (pyPostToPostCond Q)) :
    PyTriple m P ss Q
```

**`twinAgrees` is the elephant and it must be named as one.** It is an adequacy
theorem for a second semantics, over the same AST, and `harness/diff_test.py`'s
1 213 cases validate only the first. Two honest options: (a) prove it — a
whole-interpreter induction, per language; or (b) run the twin through
`leanmodels-run` and validate it differentially like the original — cheap
(the twin is executable, §3.2) but it makes the twin a *maintained second
interpreter*, which the standing "model always matches code" law then binds.
Neither is free, and neither is what "just use the default mvcgen" sounds like.

### 5.2 What to adopt NOW, at zero cost

Independent of any migration, and worth landing whatever else is decided:

1. **Output-determined specs.** Never take the answer as an input parameter;
   bind it with the result binder. This is a `@[py_spec]` rule as much as a
   `@[spec]` rule, and the measured failure mode (mvcgen unifying `?v` with the
   *loop accumulator*) is exactly the kind of silent wrongness the campaign's
   loudness doctrine exists to prevent.
2. **The altitude law, restated with its price tag.** *Primitives go behind
   spec lemmas; unfolding them into the walker costs 259 VCs where 12 suffice.*
   The tree already practises this; it now has a number.
3. **The layer-order correction** to `docs/family-architecture.md` §3.4 — one
   line, and it is load-bearing for every tier written against that sketch.
4. **Never write a bare polymorphic `throw`** in interpreter code (§1.4).

### 5.3 The recommendation

* **New tiers (C, SV, Go): adopt the substrate** — `ExceptT ρ (StateT W Halt)`,
  the free `WPMonad`, primitives behind `@[spec]`. Use `mvcgen` on the
  **fuel-free fragment** (expression evaluation, straight-line statement
  sequences, and any loop you are willing to make total by a measure instead of
  a fuel bound). Keep the threshold assembly by hand at `call` and loop points.
  Decide fuel's fate **before** writing the interpreter, not after.
* **Python: bridge, do not migrate.** The campaign is mid-flight and the
  substrate saving (5 343 lines of tactic) is not collectable without an
  adequacy theorem the campaign cannot afford to owe. Revisit when
  `RecursionStep` closes, with that day's numbers — never forced.
* **Do not treat `mvcgen` as the whole answer to "one vcgen".** It is one
  vcgen for the fuel-free half of the problem. The other half — fuel
  monotonicity, threshold composition, and `callIn`'s recursion — is where the
  per-language work actually lives, and mvcgen is silent there by construction.

### 5.4 Risks recorded

* `mvcgen` is **self-declared experimental**; its own warning says to avoid it
  in production. Every use in this family would carry
  `set_option mvcgen.warning false`, which is a decision to make once, loudly.
* One real bug found at the pin (§1.4) in twenty lines of probing. A tactic at
  this maturity will have more.
* `mvcgen?` is a no-op in our runs; `mvcgen [f] invariants?` is the working
  form. Small, but it is the kind of thing that costs a session if unrecorded.

---

## Appendix — the runs, and what each cost

| run | what it measured | cost |
|---|---|---|
| toolchain census | `Std/Do` (21 files) + `Std/Tactic/Do` (2) + `Lean/Elab/Tactic/Do/VCGen.lean` present at the pin | file listing |
| `#synth` probes | `WPMonad` for both candidate stacks, zero instances written | ~16 s |
| layer-order `rfl`s | the failure barrel sees `W` only under `ExceptT`-outside | in the landed file |
| `throw` probe | the `Spec.throw_Except` metavariable bug | ~21 s |
| toy `StateT`/`Except` loop | mvcgen's contract end to end; the output-determined law | ~26 s |
| `tri` fuel-free | Route C closes, 13-line proof | in the landed file |
| `triF` symbolic fuel | Route B: one VC, goal unchanged | **1 m 31 s** |
| `loopF` fuel-in-monad | Route A: not definable | ~5 s |
| GATE 3, primitives unfolded | **259+ VCs**, `mvcgen_trivial` fails | 1 m 54 s |
| GATE 3, answer-as-input specs | **23 VCs**, dependent metavariables | ~13 s |
| GATE 3, output-determined specs | **12 VCs**, closes; `mvcgen` step 568 ms | ~3 s |

No `lake build` was run. The machine-wide build lock was never taken because it
was never needed: `Std.Do` is at the pin, so the expensive newer-toolchain
experiment the brief anticipated **does not exist**.
