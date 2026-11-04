# The Lean-structures census — measured

**The question.** *We've been relying a lot on Lean's `mvcgen`. Are there other
Lean structures we can lean on?*

**The method is the mvcgen pilot's** (`docs/mvcgen-pilot.md`), and this report
is its sibling: every claim below is a run, at the pinned toolchain
`leanprover/lean4:v4.33.0-rc1`, with `#print axioms` on everything. The
experiment file is [docs/lean-structures-census.lean](lean-structures-census.lean)
— zero `sorry`, zero `native_decide`, zero `bv_decide`, and **out of the pinned
build by construction** (`lakefile.toml`'s globs are the `LeanModels` lib root
and `Examples.+`; nothing under `docs/` is either). Run it with

    lake env lean docs/lean-structures-census.lean

**No `lake build` was run for any measurement in this report.** The
machine-wide build lock was never taken because it was never needed: every
experiment is a scratch file that elaborates in seconds.

---

## THE VERDICT, first

**Yes — and the largest single win is not a new structure at all, it is a
COMPOSITION POINT between two we already have.**

1. **`grind` is at the pin and the tree already uses it 67 times. What the
   tree does NOT use is `grind`'s REGISTRY — `@[grind]` and its ten modifiers,
   **zero** occurrences — and the one line that makes the registry compose with
   `@[spec]`.** `mvcgen` discharges VCs through `mvcgen_trivial`, which core
   declares as delegating to the *user-extensible* `mvcgen_trivial_extensible`.
   Wiring `grind` there takes the pilot's own worked gate from **12 verification
   conditions to 0** — the proof loses its entire closing script and keeps
   identical axioms. One `macro_rules` line per tier. **This is recommendation 1.**

2. **`EStateM` is the substrate's corrected layer order, already shipped,
   already optimized, with seven `@[spec]` lemmas in core.** `docs/family-architecture.md`
   §3.4 arrived at `ExceptT ρ (StateT W Halt)` by `rfl`; core's
   `EStateM.instWPMonad` has `PostShape` `.except ε (.arg σ .pure)` — that same
   order — and core's own docstring for `EStateM` is `Run`'s `.exn` rule
   verbatim: *"exceptions do not automatically roll back the state."* It is
   **not** definitionally the pilot's stack (refuted), but the iso is 8 lines.
   Two measured caveats keep this from being free, and one of them cuts against
   the folklore: **EStateM is ~1.4× SLOWER in the kernel**, not faster.

3. **`bv_decide` IS `native_decide`-class at this pin whenever its SAT solver
   runs — same mechanism, different axiom name — and the axiom name is the trap.**
   `Lean/Meta/Native.lean`'s `nativeEqTrue` docstring says it outright:
   *"It is the basis for `native_decide` and `bv_decide` tactics."* Exact axiom
   sets, the mechanism, and the crossover prices against the two honest
   alternatives are in §8. **Thomas rules; this report only prices.**

**Two findings the census did not go looking for.** The pin ships a `cbv`
tactic that closes the *computed-shape residue* class `grind`, `simp` and
`unfold`+`grind` all fail on (§10.2). And at this pin **`native_decide` no
longer emits `Lean.ofReduceBool`** — a denylist gate greping for that name is
blind here (§8.4). `AGENTS.md`'s law is stated as an *allowlist* and therefore
already catches both.

---

## §1 THE AVAILABILITY TABLE

All at `leanprover/lean4:v4.33.0-rc1`. "core" means no package, no
`lakefile.toml` edit, no `lake-manifest.json` edit.

| structure | at the pin? | import needed | package cost | uses in the tree today |
|---|---|---|---|---|
| `grind` tactic | **yes, core** | none (builtin) | zero | **67**, in 22 files |
| `@[grind]` registry — `=`, `=_`, `_=_`, `←=`, `←`, `→`, `⇐`, `⇒`, `.`, `usr`, `cases`, `cases eager`, `intro`, `ext`, `inj`, `funCC`, `norm` | **yes, core** (`Init/Grind/Attr.lean`) | none | zero | **0** |
| `cbv` tactic + `@[cbv_eval]` attribute | **yes, core** (`Init/Tactics.lean`) | none | zero | **0** |
| `mvcgen_trivial_extensible` (the composition point) | **yes, core** (`Std/Tactic/Do/Syntax.lean:374`) | `Std.Tactic.Do` | zero | **0** |
| `EStateM` + `EStateM.instWPMonad` | **yes, core** | `Std.Do` | zero | 0 (as a substrate) |
| core `@[spec]` lemmas for `EStateM` | **yes — 7** (`get`, `set`, `modifyGet`, `throw`, `tryCatch`, `orElse`, `adaptExcept`) | `Std.Do` | zero | 0 |
| `deriving ToJson` / `FromJson` | **yes** | `import Lean` | zero | **0** (2 618 lines of hand loaders instead) |
| `deriving Repr`/`Inhabited`/`BEq`/`DecidableEq` | **yes, core** | none | zero | 225 / 204 / 173 / 114 |
| `deriving Lean.ToExpr` | **yes** | `import Lean` | zero | **107** |
| `Std.HashMap` + `Lemmas` | **yes, core — 1 354 theorems** | `Std.Data.HashMap.Lemmas` | zero | 0 |
| `Std.TreeMap` (953) / `Std.DHashMap` (1 878) | **yes, core** | ditto | zero | 0 |
| `Fintype` | **NO — not in core at all** | Mathlib only | puts Mathlib in the consumer's closure | — |
| core `Decidable (∀ …)` instances | **only** `Bool`, `Fin n`, `Ordering`, bounded `Nat` (`decidableBallLT`), `Option` membership; `Char` via Batteries | none | zero | — |
| `Plausible` | **yes — in the dep tree**, inherited via Mathlib | `import Plausible` | already in `lake-manifest.json` | 0 |
| `Aesop` | **yes — in the dep tree**, inherited via Mathlib | `import Aesop` | already in the manifest | 0 |
| `partial_fixpoint` | **yes, core** | none | zero | 0 |
| `bv_decide` | **yes, core** | `Std.Tactic.BVDecide` | zero package — **but an AXIOM cost, §8** | 0 |
| `decide +kernel` / `+native` | **yes, core** (`DecideConfig`) | none | zero | 0 |

**One structural fact worth stating plainly, because two candidates depend on
it: Mathlib is ALREADY a required dependency of this tree.** `lakefile.toml`
requires `mathlib` at `v4.33.0-rc1`, and 26 files under `LeanModels/` import it
(the Circuit and Spice tiers). So Aesop, Plausible, Batteries and Qq are all
built and present. **The core-only law is a per-tier discipline, not a
repository-wide absence** — adopting Aesop or Plausible in the Python/C/Sv
tiers would newly put Mathlib in *their* closure, and that is the cost to
weigh, not a package fetch.

**Import baselines, measured** (they dominate every small experiment):
core-only ≈ **1.0–1.4 s**; `LeanModels.Python.Semantics` ≈ **3–4 s**;
`Plausible` ≈ **2.7 s**; `Aesop` ≈ **12.6 s**.

---

## §2 CANDIDATE 1 — `grind`: the tactic is adopted, the registry is untouched

### 2.1 The worked gate, four ways

The subject is the mvcgen pilot's `value_scores_M` — GATE 3's fact
(`score = pst[p][j] - pst[p][i]`) through the monadic twin, with the gate's own
fourteen premises. Only the *closing* changes.

| closing | proof lines after the 8 `have`s | VCs left | wall clock | `#print axioms` |
|---|---|---|---|---|
| the pilot's (`all_goals intros` / `subst_vars` / `simp_all [8 lemmas]`) | **4** | 0 | **7.23 s** | `[propext, Classical.choice, Quot.sound]` |
| `mvcgen [...]` then `all_goals grind` | **2** | 0 | **4.00 s** | identical |
| `mvcgen [...]` alone | 1 | **12** (`vc1`…`vc12`) | 4.14 s | `sorryAx` (unclosed) |
| **`mvcgen [...]` alone, with `grind` wired into `mvcgen_trivial_extensible`** | **1** | **0** | **4.00 s** | **identical** |

**The wiring is one line and it is core-sanctioned:**

```lean
-- docs/lean-structures-census.lean (excerpt — §1, the composition point)
macro_rules | `(tactic| mvcgen_trivial_extensible) => `(tactic| grind)
```

Core's own docstring for `mvcgen_trivial` says *"Users are encouraged to extend
`mvcgen_trivial_extensible` instead of this tactic in order not to override the
default behaviour."* So this is the intended seam, not a hack.

**How the two registries compose:** `@[spec]` says what `mvcgen` **applies**
(the altitude layer — primitives behind triples); `@[grind]` says what
**closes** what is left. They do not overlap and they do not conflict. The
measurement is that the second registry is currently empty, so every VC is
closed by a hand-written `simp_all` naming its lemmas — and `grind` needs no
naming at all, because it takes the local hypotheses without being told.

### 2.2 Where `grind` STOPS — and the residue law survives it intact

The pilot recorded *"computed-shape / residue-spelling PERSISTS verbatim."*
This is that row measured in `grind`'s own vocabulary, on the gate's four real
residues:

| residue (real, from `value_bound.lean`'s premises) | `grind` | what does close it |
|---|---|---|
| `resolve ⟨w,e⟩ "pst" = some (.ref pa)` — two-level name lookup | **CLOSES** (`grind [resolve]`) | — |
| `indexValH w.heap (.ref pa) (.str pc) = .ok (.tuple xs)` — heap index | **CLOSES** (`grind [indexValH, heapIndex, hashableKey]`) | — |
| `indexValH w.heap (.tuple xs) (.int j) = .ok (.int zj)` — the COMPUTED-SHAPE tuple index (`normIndex`/`asInt`) | **FAILS**, with and without a `simp only` prelude | the hand `simp` carrying the `if_neg`/`if_pos` **decisions** |
| `evalBinOp .sub (.int zj) (.int zi) = .ok (.int (zj - zi))` | **FAILS** — and so do `grind [= evalBinOp]`, `simp [evalBinOp]`, and `unfold evalBinOp; grind` | `rfl` **or** the pin's new `cbv` (§10.2) |

**The split is clean and it is the law's own line.** `grind` is E-matching plus
congruence closure: it settles residues that are *lookups*. It does not
*compute* a `match` down to a value, which is exactly what the residue-spelling
law is about. Four tactics failed on a goal one `rfl` token closes.

### 2.3 Price

**Adoption cost: one `macro_rules` line per tier that uses `mvcgen`, plus
`@[grind]` annotations as they earn their place.** No import (the attribute is
core), no package, no toolchain move. Measured risk: none observed — the wired
run was 0.14 s *faster* than the unwired one on the real gate, because `grind`
replaced work `simp_all` was doing anyway. The one thing to know before turning
it on: `grind` failing is *loud* (it prints a goal-diagnostics dump), so a wired
`mvcgen` that used to leave 12 tidy VCs will instead leave 12 grind dumps when
something breaks. That is a debugging-ergonomics cost, not a soundness one.

---

## §3 CANDIDATE 2 — `EStateM`: the corrected layer order, shipped

### 3.1 The type identity: iso, not defeq

| claim | result |
|---|---|
| `EStateM ε σ α = (σ → EStateM.Result ε σ α)` | `rfl` ✓ |
| `ExceptT ε (StateT σ Id) α = (σ → (Except ε α × σ))` | `rfl` ✓ |
| `EStateM ε σ α = ExceptT ε (StateT σ Id) α` | **REFUTED** — `rfl` gives *"Type mismatch… has type `?m = ?m` but is expected to have type…"*. `Result` is an inductive with two constructors; the other is a product of a sum. |
| the ISO, both directions | proved in **8 lines**, axioms `[Quot.sound]` |

Core's own docstring already says the equivalence and says why the difference
exists: *"`EStateM ε σ` is equivalent to `ExceptT ε (StateM σ)`, but it is more
efficient."*

### 3.2 The layer order is the CORRECTED one, and it is shipped

```lean
instance EStateM.instWPMonad : WPMonad (EStateM ε σ) (.except ε (.arg σ .pure))
```

`.except ε` **outside** `.arg σ` — the order `docs/family-architecture.md` §3.4
reached by `rfl` after the pilot refuted its first sketch. Decided again here:

```lean
-- docs/lean-structures-census.lean (excerpt — §2, the layer order)
example : ExceptConds (.except ε (.arg σ .pure)) = ((ε → σ → ULift Prop) × Unit) := rfl
example : ExceptConds (.arg σ (.except ε .pure)) = ((ε → ULift Prop) × Unit) := rfl
```

And the semantics matches the tier's, not by coincidence: core's `EStateM`
docstring is *"A combined state and exception monad in which exceptions do not
automatically roll back the state"* — which is `docs/memory-model.md` v2's
*"state retained on `.ok` AND `.exn`"*, and the reason `PyPost.err` is
state-aware.

### 3.3 What core ships for it, and one bug it does NOT have

**Seven `@[spec]` lemmas, in core** (`Std/Do/Triple/SpecLemmas.lean:537–568`):
`Spec.get_EStateM`, `set_EStateM`, `modifyGet_EStateM`, `throw_EStateM`,
`tryCatch_EStateM`, `orElse_EStateM`, `adaptExcept_EStateM`.

**The mvcgen pilot's §1.4 bug does not arise here, and that is a real win.**
There, a bare polymorphic `throw` inside `StateT W (Except ε)` left four
metavariable goals and the declaration was *rejected* for universe
metavariables, because `Spec.throw_Except` is declared under a
`variable {m} {ps}` block its conclusion does not determine.
`Spec.throw_EStateM`'s conclusion determines everything. Measured: the bare
`throw` below elaborates and closes with no workaround at all.

```lean
-- docs/lean-structures-census.lean (excerpt — §2, the bare polymorphic throw)
def bareThrow : M2 Nat := do
  let n ← get
  if n = 0 then throw "zero" else pure n
```

`bareThrow_spec` : `[propext, Quot.sound]`. The pilot's rule *"never write a
bare polymorphic `throw` in interpreter code"* is a workaround for a stack
EStateM replaces.

**And a mechanism the tier will want: `EStateM.Backtrackable`.** Exception
handlers save and restore a `δ`-part of the state; the **default instance is
`δ = Unit`, i.e. no rollback** — which is Python's rule exactly. A tier that
later needs partial rollback (a transaction, a speculative frame) has a
first-class place to put it instead of threading it by hand.

### 3.4 The two prices, both measured

**Price 1 — the Halt barrel becomes state-AWARE.** The substrate needs a
third, state-*discarding* layer (`.timeout`, `.unsupported`). Stacking it on
EStateM synthesizes a `WPMonad` with zero instances written, but:

```lean
-- docs/lean-structures-census.lean (excerpt — §2, the Halt barrel)
example : ExceptConds (.except L (.except ε (.arg σ .pure)))
    = ((L → σ → ULift Prop) × (ε → σ → ULift Prop) × Unit) := rfl
example : ExceptConds (.except ε (.arg σ (.except L .pure)))
    = ((ε → σ → ULift Prop) × (L → ULift Prop) × Unit) := rfl
```

The pilot's stack can **say** the state is gone on a timeout. The EStateM-based
stack can only decline to mention it. That is a loss of faithfulness in the
type, and `Run.timeout` genuinely carries no state.

**Price 2 — EStateM is SLOWER in the kernel, not faster.** The "more efficient"
in core's docstring is about compiled runtime (an unboxed `Result`), and the
tier's hot path is kernel `rfl` at fuel 4096 (`#py_check`, `py_check`,
`py_vcgen`'s captured runs). Measured on a `countdown` of `n` `modify` steps,
`rfl` at `maxHeartbeats 0`:

| steps | `EStateM ε σ` | `ExceptT ρ (StateT σ (Except L))` |
|---|---|---|
| 1 000 | 2.93 s | 3.00 s |
| **4 096** | **50.1 s** | **35.3 s** |

Both blow the default 200 000-heartbeat budget at 4 096 (they need
`maxHeartbeats 0`), and EStateM is **~1.4× slower** at the size that matters.
Whatever EStateM is for, it is not for making the tier's `rfl`s cheaper.

### 3.5 Price and urgency for the rebuild lane

**FLAGGED, but not urgent — and the reason is price 2.** The brief asked
whether this could change the rebuild lane's foundation. It could: the corrected
layer order, seven free spec lemmas, a fixed `throw`, and a `Backtrackable`
hook are all real. But the substrate is three layers, not two, and the third
layer is where EStateM's advantages stop and its faithfulness loss begins —
while its kernel cost is *worse* on the one operation the tier does most.

**The recommendation is therefore narrow: rest the substrate's TWO-LAYER CORE
on `EStateM` and keep the Halt layer outside it**, taking the seven spec lemmas
and the `throw` fix, and pricing the state-aware Halt barrel as a documentation
obligation (the tier must state that its Halt postconditions never mention the
state). Decide it **before** the rebuild writes its interpreter, not after — the
same rule §3.4 already gives for fuel.

---

## §4 CANDIDATE 3 — `deriving ToJson`/`FromJson`: a round-trip codec, not a reader

### 4.1 What the derived codec actually speaks

Derived on a C-tier-shaped AST (`CSpan`, `TypeNode`, `Expr` with clang's
fields), the round trip works — both `#guard`s pass — but the **wire format is
Lean's own**:

```
{"binop": {"ty": "int", "span": {"line": 1, "endLine": 3, "endCol": 4, "col": 2}, …}}
```

Constructor-tagged nesting, and field names are the Lean identifiers
(`endLine`). The envelope the C tier actually reads is clang's:

```
{"kind": "BinaryOperator", "op": "-", "lhs": {…}, "span": {"end_line": 3, …}}
```

Measured against the real spelling:

| input | derived `fromJson?` says |
|---|---|
| `{"line":1,"col":2,"end_line":3,"end_col":4}` | `Except.error "E3.CSpan.endLine: Natural number expected"` |
| `{"kind":"BinaryOperator","op":"-",…}` | `Except.error "no inductive tag found"` |
| `{"bogus":1}` | `Except.error "no inductive constructor matched"` |

**There is no field-name customization** in the deriving handler at the pin
(`Lean/Elab/Deriving/FromToJson.lean` has no attribute or option for it).

### 4.2 Price

| | hand loader (`LeanModels/C/Json.lean`) | `deriving FromJson` |
|---|---|---|
| reads the extractor's schema | **yes** — that is its whole job | **no** |
| lines | **318** (C); 2 618 across four tiers (Python 1 660, Sv 374, C 318, Es 266) | 0 |
| error message on a bad node | nested path: `withCtx kind` → `"BinaryOperator: field 'lhs': …"` | struct fields named (`CSpan.endLine`); **inductives give no path at all** |
| unknown `kind` handling | a deliberate, documented refusal | `"no inductive constructor matched"` |

**Verdict: the C/Ada/ES envelope loaders CANNOT derive, and the reason is
structural, not cosmetic.** They read a schema fixed by clang / libadalang /
the extractor — a *foreign* format that the derived codec does not speak and
cannot be taught. Deriving would require changing the **extractor** to emit
Lean's encoding, which trades away the spec-mirroring principle those envelope
schemas exist to uphold (`docs/c-envelope-schema.md` mirrors clang's AST dump
on purpose) and would buy uninformative errors in exchange.

**Where it IS the right tool, and this is worth taking:** the tree's *own*
serialized artifacts — harness job files, envelope caches, census JSON that
Lean both writes and reads. Nothing there is a foreign schema, both ends move
together, and the round trip is exactly what is wanted. `deriving Lean.ToExpr`
is already used **107 times** on the same reasoning; `ToJson`/`FromJson` is the same
move for data that leaves the process.

---

## §5 CANDIDATE 4 — Std's verified containers vs `DictCalc.lean`

### 5.1 The coverage, and the fact that decides it

| container | theorems at the pin | `@[grind]`-tagged |
|---|---|---|
| `Std.HashMap` | **1 354** | 151 in `Lemmas.lean` alone |
| `Std.DHashMap` | 1 878 | — |
| `Std.TreeMap` | 953 | — |

**The decisive fact is the typeclass the lemmas assume.** They are stated under
`[EquivBEq α] [LawfulHashable α]` — **`BEq` need only be an EQUIVALENCE
RELATION, not `Eq`.** Core: *"`EquivBEq` says that the `BEq` implementation is
an equivalence relation."*

That is precisely Python's `==` on hashable keys, and precisely what
`DictCalc.lean` §1 already proves about `keyEq` — `keyEq_refl`, `keyEq_symm`,
`keyEq_trans`, through the `keyNF` normal form, *"reflexivity, symmetry and
transitivity then cost one line each."* **DictCalc §1 is not merely compatible
with `EquivBEq`; it is `EquivBEq`'s obligation, already discharged.**

Verified by instantiation on a key type carrying DictCalc's two "forced" facts
(`True == 1`; a namedtuple compares as a plain tuple): the instances are **six
lines** given the normal form, and `LawfulHashable` follows because the hash is
taken of the normal form.

```lean
-- docs/lean-structures-census.lean (excerpt — §4, the whole obligation)
instance : EquivBEq K where
  rfl   := by simp
  symm  := by intro a b h; simp_all
  trans := by intro a b c h1 h2; simp_all
```

Not `LawfulBEq`: `(K.bool true == K.int 1) = true` while
`K.bool true ≠ K.int 1`, both by `decide`.

### 5.2 The honest overlap table — `DictCalc.lean`'s 47 theorems

| DictCalc section | theorems | fate under Std |
|---|---|---|
| **§1–§1c** the `keyNF` normal form, `keyEq` refl/symm/trans, `hashableKey` | **~10** (`keyEq_iff_nf`, `keyEqList_iff_nf`, `hashableKey_iff_nf`, `hashableKeyList_iff_nf`, `keyEq_refl`/`symm`/`trans`, `hashableKey_of_keyEq`, `keyEq_false_of_keyEq`, `some_eq_map_tup`, `tup_lift`) | **BECOMES THE INSTANCE.** Not deleted — *promoted*: the same content, restated once as `EquivBEq`/`LawfulHashable`, after which 1 354 lemmas apply. |
| **§2** `dictFind`/`dictStore` algebra (`dictFind_nil`/`cons`, `dictStore_nil`/`cons`, `dictFind_store_self`, `dictFind_store_ne`, `dictFind_sound`, `dictStore_mem`) | **8** | **SUBSUMED.** `getElem?_insert_self`, `getElem?_insert`, `getKey?_insert`, `getD`. Verified: all three close by `simp`/`grind` one-liners. |
| **§3** `Bracket`, `TableOK` + its two rules, `Holds.congr`/`le` | 6 | **OURS FOREVER.** A domain invariant over a *schema*, not a container law. |
| **§4** `TableAt` at a heap slot, preserved by `heapStore`/`Heap.update`, read by `heapGet` | 4 | **OURS FOREVER** — this is the *heap frame*, which Std has no notion of. |
| **§5–§7** pair keys `(k, depth)`, depth-invisibility, `keyInt`/`pairKey` congruence, the two `KeyDetermined` results | ~12 | **OURS FOREVER.** Facts about *our schema*, decided by the key comparison. |
| **§8** `SubtreeWrites` — probe stability, `tableAt`, `trans`, `sw_push`/`sw_append` | 7 | **OURS FOREVER** — and see §9: this is the shape *Aesop* helps with. |

**Roughly 18 of 47 subsumed or promoted; ~29 are ours permanently.** The
Bracket/TableAt/SubtreeWrites layer is exactly the part that is about a *table
in a heap under a recursion*, which is the campaign's own contribution.

### 5.3 The two mismatches, located exactly — and they are blockers

**Mismatch 1 — `insert` REPLACES the key; Python's `dictStore` KEEPS it.**
`Semantics.lean:1855`'s `dictStore` returns `(k', v) :: rest` — the *stored*
key `k'`, not the probing key `k` — and its docstring says why: *"stored key
and insertion position retained — `{True: _}` updated through `1` still lists
`[True]`."* Std's `getKey?_insert_self` says `(m.insert k v).getKey? k = some k`:
the new key wins. The matching Std arm is `insertIfNew` (keeps the key, but does
not update the value), so Python's `dictStore` is `insertIfNew`-then-`modify`,
never `insert`. Verified both ways in the experiment file.

**Mismatch 2 — Python's dict is INSERTION-ORDERED; `Std.HashMap` is not.**
The strongest thing Std says about iteration is a permutation:

```
Std.HashMap.toList_insert_perm : (m.insert k v).toList.Perm ((k,v) :: m.toList.filter …)
```

`dictStore` is *defined* to preserve position, `RVal.WFList` reads
`es.toList.map Prod.fst`, and `es.size` is observable. `Std.TreeMap` is ordered
too — but by a *comparator*, not by insertion, so it does not match either.
**No Std container has Python's dict's order.** (Mitigating, and worth knowing:
the tier currently refuses live dict iteration outright — `sorted`/`max`/`min`
over dict keys and dict unpacking are all `unsupported` — so order is not yet
*observed*, only *modelled*.)

### 5.4 Price

**Adoption is not a rewrite of `DictCalc.lean`; it is a re-basing of its §1–§2
onto Std, and it is blocked on the two mismatches above being decided first.**
The prize is real and large: 1 354 lemmas, **151 of them already `@[grind]`-
tagged**, which means recommendation 1 and this one compound — adopting Std
containers *also* buys grind automation over them for free. The blocker is real
too: the key-retention rule and the insertion order are both *observable Python
semantics*, and a container that cannot state them is not a model of a Python
dict. **Recommended as a scoped experiment, not a migration** — see §11.

---

## §6 CANDIDATE 5 — `Decidable` exhaustion: three lines, and a sharp wall

### 6.1 Core has no `Fintype`, and that is the first finding

`decide` on `∀ a b : Logic, …` **fails at the pin**: *"failed to synthesize
`Decidable (∀ (a b : Logic), …)`"*. Core ships `Decidable (∀ …)` for `Bool`,
`Fin n`, `Ordering`, bounded `Nat` (`decidableBallLT`) and `Option` membership
— hand-written, per type — and **no generic `Fintype`**. Mathlib has it
(`Fintype.decidableForallFintype`, `deriving Fintype`), at the cost of putting
Mathlib in the Sv tier's import closure.

**The core-only route costs three lines** and is what the experiment file uses:

```lean
-- docs/lean-structures-census.lean (excerpt — §5, the three lines)
instance instDecForallLogic (p : Logic → Prop) [DecidablePred p] : Decidable (∀ a, p a) :=
  decidable_of_iff (p .l0 ∧ p .l1 ∧ p .lx ∧ p .lz)
    ⟨fun ⟨h0, h1, hx, hz⟩ a => by cases a <;> assumption, fun h => ⟨h _, h _, h _, h _⟩⟩
```

### 6.2 The frontier, measured on the real 4-state type

`LeanModels.Sv.Logic` (IEEE 1800-2017 §6.3.1), `k`-argument associativity,
`by decide`, all axioms `[propext]`:

| arity | cases | wall clock |
|---|---|---|
| 3 | 64 | ~1 s |
| 6 | 4 096 | **2.25 s** |
| 7 | 16 384 | **5.21 s** |
| 8 | **65 536** | **19.3 s** |
| 9 | 262 144 | **heartbeat timeout** at the default 200 000 |

**The practical wall is ~10⁵ cases at default settings.** `decide +kernel` at
arity 8 measured **23.8 s** — *no* speed-up on this shape (the machine carried
other lanes' builds at load ≈14, so treat absolute times as upper bounds and
the ratio as the signal).

### 6.3 Where it works, where it stops — on the real ∀-schedule shape

`LeanModels.Sv.ScheduleOracle` is a **structure with a function field**
(`choose : Nat → List Nat → List Nat`, plus a permutation proof). `∀ σ` is a
quantifier over a function space: **no `Decidable` instance exists and none can
be written.** That is exactly where this technique stops, and it is not a
tooling gap — it is the quantifier.

**But reified at a bound it becomes decidable, and the reification is one the
tier already has.** `ScheduleOracle.revWhen (p : Nat → Bool)` reverses exactly
the invocations `p` selects; at `k` invocations that is `k` Booleans, a finite
domain. On a two-process toy in that shape:

```lean
-- docs/lean-structures-census.lean (excerpt — §5, the reified schedule)
theorem sched_first_irrelevant : ∀ r1 r2 : Bool, run r1 r2 (0, 0) = run false r2 (0, 0) := by
  decide
...
theorem sched_race : ¬ (∀ r1 r2 : Bool, (run r1 r2 (0, 0)).1 = (run false false (0, 0)).1) := by
  decide
```

The first is `Sv/Obs.lean`'s `choose_singleton` shape — σ-irrelevance — settled
by exhaustion, no axioms at all. The second is a **race, exhibited by the same
call**.

**And one datum this census owes honestly: `decide` refuted the author's first
draft.** The initial `sched_indep` claimed cell 1 was schedule-independent;
`decide` answered *"Tactic `decide` proved that the proposition … is false"*.
A refuting `decide` is a counterexample finder, not only a prover — which is
the same job §7 hires Plausible for, at kernel strength, where the domain is
finite.

### 6.4 Price

**Cheap, core-only, and bounded by arithmetic.** Three lines per finite type;
then any ∀-property under ~10⁵ cases is kernel-checked with axioms `[propext]`
or none. It replaces a census battery only where the domain is genuinely finite
— the `Logic` operator tables, bounded-`k` schedules, small enum products.
It stops dead at: unbounded fuel, `Nat`/`Int`-indexed anything, `String`,
`Array` of unbounded size, and any `∀ σ` over an oracle that stays a function.

---

## §7 CANDIDATE 6 — Plausible: the search half, and only that

**Available**: in the dep tree already (`lake-manifest.json`, inherited via
Mathlib), `import Plausible`, ~2.7 s.

On a **false** ∀-schedule claim in the reified shape:

```
Found a counter-example!
σ := []
issue: 0 = 1 does not hold
(0 shrinks)
```

On a **false** C-shaped claim (32-bit wrap is not the identity):

```
Found a counter-example!
a := 0
b := -5
issue: 4294967291 = -5 does not hold
```

On a **true** claim: `Unable to find a counter-example`, and the declaration is
left using `sorry`.

**Price.** It is a **refuter, never a prover** — the `sorry` is the point, and
under the campaign's laws a Plausible-closed goal is an unclosed goal. Its
place is the *pre-proof* step: state the theorem, run `plausible`, and only
then spend the proof effort. Two cautions from the runs: the shrinker drives to
the *cheapest* counterexample, which was the degenerate empty schedule `[]`
here (informative about the statement, not about the schedule); and adopting it
in a core-only tier newly puts Mathlib in that tier's closure. **Recommended as
a scratch-file instrument, not a tree dependency** — exactly how it was used
here.

---

## §8 CANDIDATE 8 — `bv_decide`: THE POLICY ITEM

**This section states the trust situation precisely and neutrally, and prices
both alternatives. Thomas rules.**

### 8.1 The exact axiom facts

Four runs at the pin, same file:

| tactic | `#print axioms` |
|---|---|
| `decide` | `[propext]` / `[propext, Quot.sound]` |
| **`bv_decide`, where the NORMALIZER closes the goal (SAT never runs)** | `[propext, Classical.choice, Quot.sound]` — **clean** |
| **`bv_decide`, where the SAT SOLVER RUNS** | `[propext, Classical.choice, Quot.sound, `**`mulComm8._native.bv_decide.ax_1_5`**`]` |
| `native_decide` | `[`**`nd._native.native_decide.ax_1_1`**`]` |

**The generated axiom, printed:**

```
axiom mulComm8._native.bv_decide.ax_1_5 :
  Std.Tactic.BVDecide.Reflect.verifyBVExpr mulComm8._expr_def_1_1 mulComm8._cert_def_1_1 = true
```

That is: bv_decide reifies the goal to a `BVExpr`, emits the SAT solver's LRAT
certificate as a term, and **asserts by axiom** that the verified checker
evaluates to `true` — rather than proving that by kernel reduction.

### 8.2 The mechanism, from core's own source

`Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:39` calls
`nativeEqTrue \`bv_decide reflectionTerm`. And `Lean/Meta/Native.lean`'s
docstring for `nativeEqTrue` says:

> …that value, check that it evaluates to `true`, and if so, will **add an
> axiom** asserting `e = true` and return that axiom.
>
> **It is the basis for `native_decide` and `bv_decide` tactics.**

The body `addAndCompile`s the term and evaluates it with `unsafe evalConst Bool`.

**So the answer to the `ofReduceBool`/`trustCompiler` question is: neither name
appears, and the mechanism is the same one anyway.** At v4.33.0-rc1
`bv_decide` and `native_decide` are the *same* trust mechanism —
compile-and-evaluate, then axiomatize the result — differing only in what is
evaluated (an LRAT certificate checker vs. a `Decidable` instance) and in the
generated axiom's name. **Whenever bv_decide's SAT solver runs, it is
`native_decide`-class.** When bv_decide's *normalizer* closes the goal without
calling SAT, no axiom is added and the result is ordinary.

**Two things this does not say, and should not be read as saying.** The
evaluated object is a *verified* LRAT checker with a soundness theorem, so the
trusted step is "the compiler evaluated this checker correctly", not "the SAT
solver was right" — that is a materially smaller trusted step than a bare
`native_decide` over arbitrary user code. And the axiom is per-theorem and
always visible to `#print axioms`; nothing is hidden.

### 8.3 The crossover — the same facts, three ways

Both facts are instantiated on real shapes, not toys.

**FACT-C** — `LeanModels/Rv/Exec.lean`'s `divRem .div` overflow arm, the
neighbour of `LeanModels.C.C23.UB.divideOverflow` (*"`INT_MIN / -1`: the
quotient is unrepresentable"*): `a.sdiv (allOnes w) = -a`.

| route | 8 | 12 | 16 | 32 | 64 | 128 | **∀ w** | axioms |
|---|---|---|---|---|---|---|---|---|
| **symbolic**, width-parametric | — | — | — | — | — | — | **✓, 6 proof lines, ~0.25 s** | `[propext, Classical.choice, Quot.sound]` |
| **`decide`** | 2.46 s | 8.53 s | **timeout** | — | — | — | ✗ | `[propext, Quot.sound]` |
| **`bv_decide`** | 1.49 s | — | 1.55 s | 1.56 s | 1.47 s | 1.50 s | ✗ | **clean — the NORMALIZER closed it; SAT never ran** (verified by trace) |

**FACT-SV** — `LeanModels.Sv.Logic`'s 4-state De Morgan
(`¬(a ∧ b) = ¬a ∨ ¬b`, IEEE 1800-2017 §11.4.8) on the `(value, unknown)`
BitVec-pair encoding an efficient `LVec` twin would use.

| route | 2 | 3 | 4 | 8 | 16 | 32 | 64 | 128 | **∀ w** | axioms |
|---|---|---|---|---|---|---|---|---|---|---|
| **symbolic**, bitwise | — | — | — | — | — | — | — | — | **✓, 18 proof lines** | `[propext, Classical.choice, Quot.sound]` |
| **`decide`** | 19.0 s | 17.8 s | **timeout** | — | — | — | — | — | ✗ | `[propext, Quot.sound]` |
| **`bv_decide`** | — | — | — | 19.0 s | 10.3 s | 11.3 s | 22.6 s | 12.1 s | ✗ | **+2 `_native` axioms at EVERY width** (`svDM._native.bv_decide.ax_1_8`, `…ax_1_13`) |

**bv_decide's own ceiling, measured.** Multiplier commutativity
(`a * b = b * a`): **8-bit closes in 0.59 s of SAT; 12-bit, 16-bit and 32-bit
all hit the default 10 s solver timeout.** So bv_decide is not uniformly
"width-free" — it is free on bit-parallel structure and falls off a cliff on
multipliers.

### 8.4 Two consequences worth taking regardless of the ruling

**(a) A DENYLIST gate is blind at this pin.** Stated precisely: the
`ofReduceBool` family still *exists* in the environment — but `native_decide`
no longer *emits* it. What `#print axioms` shows at v4.33.0-rc1 is
`<thm>._native.native_decide.ax_N_M`, and a source grep for `native_decide` is
evaded by `decide +native` besides. So a gate that greps for either name
catches nothing.

**This is independently corroborated inside the tree, from the other
direction.** `harness/lean_kernel_census.py:136` already records that *"Upstream
is RETIRING in-kernel native reduction: the whole `ofReduceBool` family carries
a dated `@[deprecated …]` attribute"* — the Lean tier's census noticed the
deprecation; this census measures what replaced it at the call site. (That
instrument is a **census, not a gate**: its own docstring says it is
*"deliberately NOT wired into CI"*, and it measures the kernel's vocabulary, not
this tier's axiom discipline.)

**`AGENTS.md`'s law is already the robust form** — *"`#print axioms` of every
`@[spec]` theorem must show only `[propext, Classical.choice, Quot.sound]`"* —
an **allowlist**, which catches bv_decide's extra axiom, `native_decide`'s, and
anything future, because it names what is PERMITTED rather than what is
forbidden. That is worth recording as a deliberate property of the law, not
luck. Measured: no automated gate in `harness/` or `tools/` enforces it today;
it is enforced by reading.

**(b) The symbolic route is not merely axiom-cleaner; it is more
INFORMATIVE.** The width-parametric FACT-C proof needed the side condition
`1 < w`, and forced out the edge case: **at `w = 1`, `intMin 1 = 1#1`, the side
condition genuinely fails, and the fact is a different fact**
(`a.sdiv (allOnes 1) = a`, not `-a`). No bv_decide run at 8/16/32/64/128 could
have surfaced that. Relatedly, the first probe in this census stated the C fact
with a redundant `a ≠ intMin` hypothesis; `bv_decide` proved it and said
nothing, and it was the *unused-variable linter* that noticed. A fixed-width
oracle answers the question you asked; it does not tell you the question was
wrong.

### 8.5 Price, for the ruling

| | symbolic, width-parametric | `decide` | `bv_decide` |
|---|---|---|---|
| **axioms** | ordinary three | `[propext]` (+`Quot.sound`) | **+1 per SAT call**, `_native`-named |
| **generality** | **all widths at once** | one width | one width |
| **author cost** | 6–18 lines, and 2–3 iterations each (this census's own experience) | one token | one token |
| **reach** | needs library lemmas to exist; they did here (`sdiv_neg`, `sdiv_one`, `msb_intMin`) | dies at ~10⁵ cases → widths ≤ 12 | dies on multipliers ≥ 12 bits |
| **informativeness** | exposes edge cases and redundant hypotheses | exposes counterexamples | silent on both |
| **who checks it** | the kernel | the kernel | the Lean compiler, on a *verified* checker |

**A shape the ruling could take, offered without prejudice:** allow `bv_decide`
in **scratch and exploration** (where it is excellent — it settled 128-bit
4-state De Morgan in 11 s), forbid it in **landed proofs** under the existing
allowlist law, and treat a bv_decide success as a *signal to go find the
width-parametric proof* — which is how it was used in this census. That keeps
the axiom set unchanged and still collects the tool's real value. **But this is
Thomas's call, and the numbers above are the whole basis for it.**

---

## §9 CANDIDATES 7 & 9 — `partial_fixpoint` and Aesop

### 9.1 `partial_fixpoint` — model-side only, and the kernel says so

At the pin. On a toy interpreter loop with no fuel argument:

| | result |
|---|---|
| definition without a measure or fuel | **✓** |
| `loop.eq_def` (the unfolding equation) | **✓** — `rw [loop.eq_def]` works, axioms `[propext, Classical.choice, Quot.sound]` |
| `loop.partial_correctness` | **✓** — a genuine proof rule, quoted in the experiment file |
| `#eval loop 5 0` | **✓** `some 15` (the compiler) |
| **`theorem : loop 5 0 = some 15 := rfl`** | **✗** — *"Not a definitional equality: the left-hand side `loop 5 0` is not definitionally equal to the right-hand side `some 15`"* |

**Demonstrated, exactly as the brief anticipated: it does not compute in the
kernel.** And `partial_correctness` is *partial* — its conclusion is
`loop n acc = some r → motive n acc r`. Termination is never on offer.

**Price.** This is a **model-side instrument only** — the fuel-free `fuelModel`,
an idealized reference function, a specification the observable interpreter is
proved to refine. It can never be the observable interpreter itself, because
`#py_check` / `py_check` / `py_vcgen`'s captured runs are kernel `rfl` at fuel
4096 and `partial_fixpoint` deletes exactly that. Cost to adopt: zero (core, no
import). Cost to misuse: the tier's entire non-vacuity discipline.

### 9.2 Aesop — a real win on one shape, with a structural tax

**Available** (dep tree, via Mathlib), import ~12.6 s — the heaviest of any
candidate.

**The structural tax is real and undocumented-feeling:** a rule set is **not
usable in the file that declares it** (*"Declared rule sets are not visible in
the current file; they only become visible once you import the declaring
file."*), and the `attribute [aesop … (rule_sets := [tier])]` lines cannot live
there either. A working setup needs **three modules**: declare the rule set /
declare the relation and its attributes / use it.

**With that paid, it wins on exactly our hardest shape.** `DictCalc.lean` §8's
`Bracket.SubtreeWrites` is a transitively-closed inductive relation. On a
miniature of it, same goal, four tactics:

| tactic | 2-step chain | 3-step chain |
|---|---|---|
| **`aesop (rule_sets := [tier])`** (safe `refl`/`push`, unsafe 50% `trans`) | **✓**, no axioms | **✓**, no axioms |
| `aesop` (default rule sets) | ✗ *"made no progress"* | — |
| `grind` with `@[grind intro]` on the relation | ✗ `grind` failed | — |
| by hand | ✓ | ✓ (and it grows with the chain) |

**Price.** Aesop is the right instrument for *proof search over an inductively
defined relation closed under composition* — which is `SubtreeWrites`,
`Runs`/`⊑`-chains in `Sv/Obs.lean`, and any future refinement relation. It is
the wrong instrument for everything else here, and it costs Mathlib in the
closure plus a three-module layout plus 12.6 s of import. **Recommended
narrowly: one `Rules` module per tier that has a composition-closed relation,
and nowhere else.**

---

## §10 CANDIDATE 10 — what the census found without being sent to look

### 10.1 `mvcgen_trivial_extensible` — the composition point (§2)

Already the headline. Recorded here as a *finding* rather than a candidate
because nothing in the brief pointed at it: the question was how `@[grind]`
composes with `@[spec]`, and the answer turned out to be a one-line seam core
deliberately provides.

### 10.2 `cbv` — a new tactic that closes the residue class `grind` cannot

`Init/Tactics.lean:2391` declares a `cbv` tactic (call-by-value evaluation)
with its own registry, `@[cbv_eval]` (`Init/Tactics.lean:2498`) — a **third**
registry alongside `@[spec]` and `@[grind]`. Zero uses in the tree.

On the residue that defeated `grind`, `grind [= evalBinOp]`, `simp [evalBinOp]`
and `unfold evalBinOp; grind`:

```lean
-- docs/lean-structures-census.lean (excerpt — §1.3, the residue `cbv` closes)
theorem resid_binop_cbv : evalBinOp .sub (.int zj) (.int zi) = .ok (.int (zj - zi)) := by
  cbv
```

**Closes in one token**, axioms `[propext, Classical.choice, Quot.sound]`.
Non-vacuity checked: the false variant (`.add` for `.sub`) leaves unsolved
goals, so `cbv` is not closing everything indiscriminately.

**Bounded, honestly:** `cbv` blew `maxRecDepth` (at 40 000) on the *heap*-index
residue — it unfolds eagerly and the heap walk is too deep. So its reach is the
**pure arithmetic / small-`match`** residues, which is a real and recurring
class, not the heap-walking ones.

This is the census's genuine surprise: the pilot's law *"computed-shape /
residue-spelling PERSISTS verbatim"* is still true of `grind`, but the pin
shipped a *different* instrument aimed squarely at it.

### 10.3 Std's container lemmas are already `@[grind]`-registered

151 `@[grind]`/`@[grind =]` annotations in `Std/Data/HashMap/Lemmas.lean` alone.
This makes recommendations 1 and 3 **compound**: adopting Std containers buys
grind automation over them at no extra cost, and wiring grind into
`mvcgen_trivial_extensible` makes that automation reach into VCs.

### 10.4 `decide +kernel` exists, and the double-reduction it avoids is real

`DecideConfig.kernel`: *"use only kernel reduction… This is more efficient,
since the default mode reduces twice (once in the elaborator and again in the
kernel), however kernel reduction ignores transparency settings."* That is
aimed at the recorded whnf-storm pain. **Measured: no win on our exhaustion
shape** (23.8 s vs 19.3 s at 65 536 cases, on a loaded machine). Recorded as an
available knob with a measurement attached, not as a recommendation.

### 10.5 `native_decide`'s axiom was renamed at this pin

Covered in §8.4. Flagged separately because it is the only finding here that
affects an **existing** law rather than proposing a new one.

---

## §11 THE RECOMMENDATION

### Top 3, in order

**1. Wire `grind` into `mvcgen_trivial_extensible`. Do it now.**
*One line per tier that uses `mvcgen`.* Measured on the pilot's own worked gate:
**12 VCs → 0**, the entire closing script deleted, **identical axioms**, and
0.14 s *faster* than the hand-written closing. No import, no package, no
toolchain move, and it is the seam core documents for exactly this. The only
cost is debugging ergonomics when something breaks (grind dumps instead of tidy
VCs). Then populate `@[grind]` — currently **zero** uses against 67 calls to the
tactic — starting with the tier's altitude and residue lemmas.

**2. Rest the substrate's TWO-LAYER CORE on `EStateM`; decide it before the
rebuild writes its interpreter.**
Buys: the corrected layer order **already instantiated**, seven core `@[spec]`
lemmas, the pilot's §1.4 bare-`throw` bug **gone** rather than worked around,
and `Backtrackable` as a first-class place for future partial rollback. Costs,
both measured, both to be written down rather than discovered later: the Halt
barrel becomes **state-aware** (the type can no longer *say* a timeout discards
state — a documentation obligation), and kernel `rfl` is **~1.4× slower at fuel
4096** (50.1 s vs 35.3 s), which is the tier's hottest operation. **Not urgent
enough to interrupt anything, structural enough that deciding it late is
expensive.**

**3. Re-base `DictCalc.lean` §1–§2 onto `Std.HashMap`, as a scoped experiment
gated on two named decisions.**
Buys: **1 354 theorems**, 151 already `@[grind]`-tagged (compounds with
recommendation 1), and ~18 of DictCalc's 47 theorems subsumed or promoted —
§1 does not disappear, it becomes the `EquivBEq`/`LawfulHashable` instance, six
lines on the `keyNF` the tier already has. `EquivBEq` accepting a
*non-`Eq` equivalence* is the fact that makes this possible at all, and it is
verified. **Blocked on two decisions that are Python semantics, not tooling:**
`insert` replaces the stored key where `dictStore` retains it, and no Std
container has insertion order. Land the instance and the §2 correspondence
first; do not touch Bracket/TableAt/SubtreeWrites, which are ours permanently.

### Runners-up, worth taking cheaply

* **`cbv` for the pure-arithmetic residue class** (§10.2) — one token, core, and
  it closes what four other tactics could not. Bounded to shallow residues.
* **Three-line `Decidable (∀ …)` instances for the Sv tier's finite types**
  (§6) — core-only, kernel-checked, good to ~10⁵ cases, and it turns bounded
  ∀-schedule questions into `decide` calls. Keeps Mathlib out of the closure.
* **Plausible as a scratch-file refuter** (§7) — before spending proof effort,
  never as a closer.
* **Aesop, in exactly one module per composition-closed relation** (§9.2) —
  it beat both `grind` and hand proofs on the `SubtreeWrites` shape.

### Declined, with reasons

* **`deriving ToJson`/`FromJson` for the envelope loaders** — structurally
  cannot read a foreign schema, and no field-name customization exists (§4).
  *Do* use it for the tree's own serialized artifacts.
* **`partial_fixpoint` for anything observable** — does not compute in the
  kernel, demonstrated (§9.1). Model-side only.
* **`Fintype`/`deriving Fintype`** — Mathlib-only, and the core-only route is
  three lines (§6.1).

### Referred to Thomas

* **`bv_decide`** (§8). It is `native_decide`-class whenever its SAT solver runs
  — same `nativeEqTrue` mechanism, per-theorem `_native` axiom — and clean when
  only its normalizer fires. The crossover prices against width-parametric
  symbolic proofs and against `decide` are in §8.3; the informativeness
  argument, including the `w = 1` edge case a fixed-width run cannot surface, is
  in §8.4(b). **The report takes no position.**

---

## Appendix — the runs, and what each cost

| run | what it measured | cost |
|---|---|---|
| toolchain census | every row of §1's availability table | file listing + greps |
| GATE 3, four closings | 12 VCs → 0; 7.23 / 4.00 / 4.14 / 4.00 s | ~20 s total |
| residue matrix (8 tactic/goal pairs) | `grind` closes lookups, fails computations | ~8 s |
| `cbv` on the residues | closes the pure one, `maxRecDepth` on the heap one | ~6 s |
| EStateM defeq / iso / PostShape / bare `throw` | refutation + 8-line iso + the §1.4 bug's absence | **1.3 s** |
| `countdown` kernel `rfl`, 2 stacks × 2 sizes | EStateM 1.4× slower at 4 096 | 92 s |
| derived JSON round trip + real-schema reads | wire format, field names, error text | 3.3 s |
| `Std.HashMap` instantiation on a Python-`==` key | `EquivBEq` satisfiable; 3 lemmas; 2 mismatches | **1.2 s** |
| `decide` exhaustion ladder, 4³…4⁹ | the ~10⁵-case wall | ~55 s |
| `decide +kernel` at 4⁸ | 23.8 s — no win | 24 s |
| Plausible, 3 claims | counterexamples + the `sorry` on a true claim | 2.7 s |
| `partial_fixpoint` | `eq_def` ✓, `partial_correctness` ✓, kernel `rfl` ✗ | 2 s |
| bv_decide axiom probes (5 variants) | the exact axiom names + `nativeEqTrue` | ~20 s |
| bv_decide trace probes | **proved the 128-bit run never called SAT** | ~15 s |
| FACT-C crossover, 3 routes × 6 widths | §8.3 table | ~60 s |
| FACT-SV crossover, 3 routes × 8 widths | §8.3 table | ~130 s |
| multiplier ceiling, 8/12/16/32 | 8-bit 0.59 s, ≥12-bit timeout | ~40 s |
| Aesop rule set, 3 modules, 4 tactics | rule set wins where grind and default aesop fail | ~20 s |
| the landed experiment file | 0 errors, 0 warnings, 0 `sorry`, 23 axiom checks | **3.9 s** |

**No `lake build` was run.** The machine-wide build lock was never taken because
it was never needed — every measurement above is a scratch file under
`lake env lean`, and the whole census cost under ten minutes of CPU.
