import LeanModels.Sv.Param2

/-!
# Generate loops in the Design2 path (`LeanModels.Sv` — `instantiate2` lemmas)

`Param2.lean` instantiates a symbolic sv-0.2 envelope into the semantic tier
(`PDesign.instantiate2` / `instantiateD2`), expanding generate items with the
mutual well-founded recursion `GenItem.expand2` / `expandList2` /
`expandIters2`. This file is the PROOF HANDLE on that pipeline: it lets a
theorem about a parametric `Design2` family (`∀ N, …`) compute the
instantiated process list SYMBOLICALLY, without fixing `N`.

Design laws:

* **Never unfold the recursion by hand.** The expansion functions are
  well-founded (not structural) — their only interface here is the
  per-constructor rewrite lemmas (`GenItem.expand2_process`, `…_genIf_*`,
  `…_genFor_of`, `expandList2_cons`, `expandIters2_cons`, …) and the family
  lemmas ported from the M0 path (`expandIters2_eq_flatten`,
  `mem_expandIters2`, `expandIters2_length_const`). A generate-for whose body
  is plain processes collapses in one step to a `flatMap` over the genvar
  sequence (`expandIters2_processes`); a body whose items' expansions are
  known (nested loops, mixed bodies) goes through `expandList2_eq_flatMap` /
  `expandList2_append_ok`.
* **Genvar sequences come from `genvarSeq_ascending`** (`Param.lean`,
  shared with the M0 path — `genvarSeq` is one definition): the canonical
  `for (g = i0; g s< e; g++)` loop is `intRange i0 (N - i0).toNat`
  (`GenItem.expand2_genFor_ascending`; `…_processes` for plain-process
  bodies, `…_flatMap` for nested loops — the inner loop is expanded under the
  outer genvar's binding on the loop's range). `genvarSeq_ascending_of` is
  the bound-agnostic generalization (any bound whose value is zero exactly
  from `N` on — `<`, `s<`, `<=`, …, via the `b2i`-free `evalInt_lt_of`
  family), and `intRange_eq_map`/`intRange_zero` turn the `Int` sequence
  into `List.range` over `Nat`, which is how a symbolic `∃ i < N, …`
  characterization is reached.
* **`instantiate2` decomposes, it is not unfolded.** `PDesign.paramEnv2`
  names the pre-declaration environment; `PDesign.instantiate2_eq` is the
  `do`-flattened equation and `PDesign.instantiate2_eq_ok_iff` its inversion:
  `m.processes` is the instantiated static processes, THEN the generate
  expansion, THEN `others` as loud `unsupported` processes; `m.decls` is
  `buildDecls`' result (`PDesign.instantiate2_processes`; the declaration
  surface is parameter-independent, `PDesign.instantiate2_declSig`).
  `PDesign.instantiateD2_of_ok` drops to the total family. Declared widths
  compute through `PType.width_packed_cons` (a public handle on
  `Param.lean`'s private `dimsWidth`).
* **Symbolic parameters by `simp`.** `evalInt` on genvar/parameter
  arithmetic, `instLhs2`, `fitExpr2`, `instExpr2`, `instProcess2` all
  compute with a symbolic `N` and genvars bound to symbolic integers once
  the `Except` monad steps (`Gen2.except_ok_bind`). Since 2026-10-28
  `evalInt` is width-exact outside the INT class (`PExpr.isInt`: integers,
  genvars, `vals`-bound parameters under `+ - * / % ** << >>`), so the
  compositional `evalInt_*_of` lemmas, `evalInt_slt` and the
  `expand2_genFor_ascending*` family carry INT side conditions — `rfl` for
  genvars and integers, `isInt_paramRef_of` from the same `vals` lookup
  that evaluates a parameter, `isInt_binary_of` above them; `simp` decides
  them itself (`PExpr.isInt` is a simp definition). Two interfaces: targeted
  conditional lemmas (`instExpr2_bitSel_ident`, `fitExpr2_bitSel_ident`,
  `instLhs2_bitSel`, `instProcess2_assignL`, …) and the documented recipe
  `sv2_inst_simp [facts]` (a `simp` call with the instantiation equations),
  exercised by the `example`s at the end of the file — the probe shapes
  `x[i]`, `x[i*N+j]`, `x[(i-1)*W+j+1]`, constant part-selects, `& | ^`,
  concatenation, literals, and a nested `N×N` generate.

## What `fitExpr2` inserts (measured, and stated as lemmas)

`fitExpr2 env elems (some w) e` wraps `e` in an explicit `.resize w` node
exactly when `e` is RIGID (`rigidExpr`: literals, identifiers, selects,
concatenations, replications, reductions — and casts of those) AND its
self-determined width is known and differs from `w`
(`fitExpr2_of_rigid_ne`). Otherwise it is `instExpr2` at the context width
(`fitExpr2_of_rigid_eq`, `fitExpr2_of_not_rigid`, `fitExpr2_none`). In
particular a gate-level bit expression `a[i] ^ b[i]` assigned to a 1-bit
target lowers with NO resize nodes: the bitwise operators push the context
width into both operands (`instExpr2_xor` …), and each operand is a
1-bit select at context 1 (`fitExpr2_bitSel_ident`). A select of an
identifier with a constant-evaluating index lowers to `Expr2.slice (.ident n)
(i.toNat * elemW) elemW` (`instExpr2_bitSel_ident`); a non-constant index to
`Expr2.index` (`instExpr2_bitSel_ident_dyn`); a constant part-select to a
`slice` of width `((m - l).toNat + 1) * elemW` (`instExpr2_partSel_ident`).
Unsized integers (`.int v`) materialize as `.lit (LVec.ofInt (ctx.getD 32)
v)` (`instExpr2_int`).

The ripple-carry acceptance (a `load_design_sv2` envelope) lives in
`Examples/system-verilog/ripple_add/gen.lean`, not here: `LeanModels` has no
envelope build inputs (`lakefile.toml` — envelopes are `Examples` material).
-/

namespace LeanModels.Sv

/-! ## Monad stepping -/

namespace Gen2

/-- Bind on a decided `Except.ok` steps into the continuation — what lets
`simp [evalInt]` compute symbolic genvar/parameter arithmetic (core has no
such simp lemma for `Except`'s own bind). NOT a global simp lemma (it is a
statement about core's `Except`, so it must not change `simp` outside this
layer): this file enables it locally, `sv2_inst_simp` passes it explicitly,
and client proofs cite it by name. -/
theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

/-- `Except.error` short-circuits bind (local simp, like `except_ok_bind`). -/
theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

/-- Associativity of `Res`'s bind (flattens nested `do` blocks — the
`instantiate2` decomposition step). -/
theorem res_bind_assoc {α β γ : Type} (x : Res α) (f : α → Res β) (g : β → Res γ) :
    (x >>= f) >>= g = x >>= fun a => f a >>= g := by
  cases x <;> rfl

/-- Nonnegativity of genvar arithmetic, as a conditional rewrite for the
`sv2_inst_simp` recipe (`x[i+1]` with a `Nat`-cast genvar `i`: simp
discharges `0 ≤ ↑i` and `0 ≤ 1` and closes the select's sign check). -/
theorem int_add_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
  Int.add_nonneg ha hb

/-- Multiplicative twin of `int_add_nonneg` (`x[i*N+j]`). -/
theorem int_mul_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
  Int.mul_nonneg ha hb

/-- A `flatMap` of singletons is a `map` (the shape a one-process loop
body expands to). -/
theorem flatMap_singleton_map {α β : Type} (f : α → β) (l : List α) :
    (l.flatMap fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

end Gen2

attribute [local simp] Gen2.except_ok_bind Gen2.except_error_bind

/-! ## Expansion equations (one per `GenItem` constructor) -/

section expansion

variable {env : IEnv} {elems : List (String × Nat)} {F : Nat}

/-- A process item instantiates in place. -/
@[simp] theorem GenItem.expand2_process (p : PProcess) :
    (GenItem.process p).expand2 env elems F = .ok [instProcess2 env elems p] := by
  rw [GenItem.expand2]

/-- An out-of-tier item stays a loud process. -/
@[simp] theorem GenItem.expand2_unsupported (k t : String) :
    (GenItem.unsupported k t).expand2 env elems F = .ok [.unsupported k t] := by
  rw [GenItem.expand2]

/-- A generate-if whose condition evaluates nonzero expands its then-branch. -/
theorem GenItem.expand2_genIf_of_ne {cond : PExpr} {thenB elseB : List GenItem} {v : Int}
    (hc : evalInt env cond = .ok v) (hv : v ≠ 0) :
    (GenItem.genIf cond thenB elseB).expand2 env elems F = expandList2 env elems F thenB := by
  rw [GenItem.expand2, hc]
  simp [hv]

/-- A generate-if whose condition evaluates to zero expands its else-branch
(`[]` when the source has no `else`). -/
theorem GenItem.expand2_genIf_of_eq {cond : PExpr} {thenB elseB : List GenItem}
    (hc : evalInt env cond = .ok 0) :
    (GenItem.genIf cond thenB elseB).expand2 env elems F = expandList2 env elems F elseB := by
  rw [GenItem.expand2, hc]
  simp

/-- A generate-if whose condition is not a constant is loud. -/
theorem GenItem.expand2_genIf_of_error {cond : PExpr} {thenB elseB : List GenItem} {e : String}
    (hc : evalInt env cond = .error e) :
    (GenItem.genIf cond thenB elseB).expand2 env elems F =
      .unsupported s!"generate if: {e}" := by
  rw [GenItem.expand2, hc]

/-- A generate-for with a decided header (start value `i0`, step `δ`) is
its genvar sequence's iteration bind. -/
theorem GenItem.expand2_genFor_eq_bind {label : Option String} {g : String}
    {initE bound step : PExpr} {rc : Option Nat} {body : List GenItem} {i0 δ : Int}
    (hi : evalInt env initE = .ok i0) (hs : stepDelta g step = .ok δ) :
    (GenItem.genFor label g initE bound step rc body).expand2 env elems F =
      (genvarSeq env g bound δ F i0 >>= fun vs => expandIters2 env elems F g vs body) := by
  rw [GenItem.expand2, hi, hs]

/-- A generate-for whose genvar sequence is known expands to the
per-value iteration of its body template. -/
theorem GenItem.expand2_genFor_of {label : Option String} {g : String}
    {initE bound step : PExpr} {rc : Option Nat} {body : List GenItem} {i0 δ : Int}
    {vs : List Int}
    (hi : evalInt env initE = .ok i0) (hs : stepDelta g step = .ok δ)
    (hv : genvarSeq env g bound δ F i0 = .ok vs) :
    (GenItem.genFor label g initE bound step rc body).expand2 env elems F =
      expandIters2 env elems F g vs body := by
  rw [GenItem.expand2_genFor_eq_bind hi hs, hv]
  rfl

/-- The empty item list expands to no processes. -/
@[simp] theorem expandList2_nil : expandList2 env elems F [] = .ok [] := by
  rw [expandList2]

/-- Item-list expansion: the head's processes, then the tail's. -/
theorem expandList2_cons (it : GenItem) (rest : List GenItem) :
    expandList2 env elems F (it :: rest) =
      (it.expand2 env elems F >>= fun ps =>
        expandList2 env elems F rest >>= fun qs => .ok (ps ++ qs)) := by
  rw [expandList2]

/-- `expandList2_cons` with both halves decided. -/
theorem expandList2_cons_ok {it : GenItem} {rest : List GenItem} {ps qs : List Process2}
    (h1 : it.expand2 env elems F = .ok ps) (h2 : expandList2 env elems F rest = .ok qs) :
    expandList2 env elems F (it :: rest) = .ok (ps ++ qs) := by
  rw [expandList2_cons, h1, h2]
  rfl

/-- A one-item list expands to that item's processes. -/
theorem expandList2_singleton_ok {it : GenItem} {ps : List Process2}
    (h : it.expand2 env elems F = .ok ps) :
    expandList2 env elems F [it] = .ok ps := by
  rw [expandList2_cons_ok h expandList2_nil, List.append_nil]

/-- Item-list expansion distributes over `++`. -/
theorem expandList2_append_ok {l₁ l₂ : List GenItem} {ps qs : List Process2}
    (h₁ : expandList2 env elems F l₁ = .ok ps) (h₂ : expandList2 env elems F l₂ = .ok qs) :
    expandList2 env elems F (l₁ ++ l₂) = .ok (ps ++ qs) := by
  induction l₁ generalizing ps with
  | nil =>
      rw [expandList2_nil] at h₁
      cases h₁
      simpa using h₂
  | cons it rest ih =>
      rw [expandList2_cons] at h₁
      simp only [Res.bind_eq_ok] at h₁
      obtain ⟨a, ha, b, hb, hab⟩ := h₁
      cases hab
      rw [List.cons_append, expandList2_cons_ok ha (ih hb), List.append_assoc]

/-- A list of plain process items instantiates pointwise. -/
theorem expandList2_processes (ps : List PProcess) :
    expandList2 env elems F (ps.map GenItem.process) = .ok (ps.map (instProcess2 env elems)) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      rw [List.map_cons, expandList2_cons_ok (GenItem.expand2_process p) ih]
      rfl

/-- Item-list expansion when every item's expansion is known: the
`flatMap` of the items (generalizes `expandList2_processes`; a body mixing
processes and nested loops goes through here). -/
theorem expandList2_eq_flatMap {f : GenItem → List Process2} :
    ∀ {items : List GenItem}, (∀ it ∈ items, it.expand2 env elems F = .ok (f it)) →
      expandList2 env elems F items = .ok (items.flatMap f) := by
  intro items
  induction items with
  | nil => intro _; simp
  | cons it rest ih =>
      intro h
      rw [expandList2_cons_ok (h it (List.mem_cons_self ..))
        (ih fun j hj => h j (List.mem_cons_of_mem _ hj))]
      simp

/-- No genvar values: no processes. -/
@[simp] theorem expandIters2_nil (g : String) (body : List GenItem) :
    expandIters2 env elems F g [] body = .ok [] := by
  rw [expandIters2]

/-- One genvar value: the body template under that binding, then the rest. -/
theorem expandIters2_cons (g : String) (v : Int) (vs : List Int) (body : List GenItem) :
    expandIters2 env elems F g (v :: vs) body =
      (expandList2 (env.bindVal g v) elems F body >>= fun ps =>
        expandIters2 env elems F g vs body >>= fun qs => .ok (ps ++ qs)) := by
  rw [expandIters2]

end expansion

/-! ## The family lemmas (ports of `Param.lean`'s M0 handles) -/

section family

variable {env : IEnv} {elems : List (String × Nat)} {F : Nat} {g : String}
  {body : List GenItem}

/-- `expandIters2` **is** flatten-of-map: if each iteration's body
expansion is known, the whole family is their concatenation in genvar
order (the `Design2` twin of `expandIters_eq_flatten`). -/
theorem expandIters2_eq_flatten {f : Int → List Process2} :
    ∀ {vs : List Int},
      (∀ v ∈ vs, expandList2 (env.bindVal g v) elems F body = .ok (f v)) →
      expandIters2 env elems F g vs body = .ok (vs.map f).flatten := by
  intro vs
  induction vs with
  | nil => intro _; simp
  | cons v vs ih =>
      intro h
      have hv := h v (List.mem_cons_self ..)
      have hrest := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
      rw [expandIters2_cons, hv, hrest]
      simp

/-- Membership in an expanded family: exactly the per-iteration processes,
for some genvar value of the loop (twin of `mem_expandIters`). -/
theorem mem_expandIters2 {f : Int → List Process2} {vs : List Int} {ps : List Process2}
    (hf : ∀ v ∈ vs, expandList2 (env.bindVal g v) elems F body = .ok (f v))
    (h : expandIters2 env elems F g vs body = .ok ps) (p : Process2) :
    p ∈ ps ↔ ∃ v ∈ vs, p ∈ f v := by
  rw [expandIters2_eq_flatten hf] at h
  cases h
  simp only [List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨l, ⟨v, hv, rfl⟩, hp⟩; exact ⟨v, hv, hp⟩
  · rintro ⟨v, hv, hp⟩; exact ⟨f v, ⟨v, hv, rfl⟩, hp⟩

/-- Family size, uniform-template case: a body that expands to `c`
processes at every genvar value gives `c * |vs|` processes (twin of
`expandIters_length_const`). -/
theorem expandIters2_length_const {f : Int → List Process2} {c : Nat}
    {vs : List Int} {ps : List Process2}
    (hf : ∀ v ∈ vs, expandList2 (env.bindVal g v) elems F body = .ok (f v))
    (hc : ∀ v ∈ vs, (f v).length = c)
    (h : expandIters2 env elems F g vs body = .ok ps) : ps.length = c * vs.length := by
  rw [expandIters2_eq_flatten hf] at h
  cases h
  clear hf
  induction vs with
  | nil => simp
  | cons v vs ih =>
      have hi := ih fun w hw => hc w (List.mem_cons_of_mem _ hw)
      simp [List.flatten_cons, hc v (List.mem_cons_self ..), hi,
            Nat.mul_succ, Nat.add_comm]

/-- A generate-for body of plain processes: the family is the `flatMap`
of the per-value instantiation (no side conditions — every process item
expands). -/
theorem expandIters2_processes (vs : List Int) (ps : List PProcess) :
    expandIters2 env elems F g vs (ps.map GenItem.process) =
      .ok (vs.flatMap fun v => ps.map (instProcess2 (env.bindVal g v) elems)) := by
  rw [expandIters2_eq_flatten (f := fun v => ps.map (instProcess2 (env.bindVal g v) elems))
    (fun v _ => expandList2_processes ps)]
  rw [List.flatMap_def]

end family

/-! ## Genvar sequences -/

/-- The `g++` step decodes to `+1`. -/
@[simp] theorem stepDelta_inc (g : String) : stepDelta g (.unary .inc (.genvarRef g)) = .ok 1 := by
  simp [stepDelta]

/-- The `g--` step decodes to `-1`. -/
@[simp] theorem stepDelta_dec (g : String) :
    stepDelta g (.unary .dec (.genvarRef g)) = .ok (-1) := by
  simp [stepDelta]

/-- `intRange` is `List.range` shifted: the bridge from the `Int` genvar
sequence to `Nat` indices (`∃ i < N, …` statements). -/
theorem intRange_eq_map : ∀ (n : Nat) (i0 : Int),
    intRange i0 n = (List.range n).map fun k : Nat => i0 + (k : Int)
  | 0, _ => rfl
  | n + 1, i0 => by
      rw [intRange, intRange_eq_map n (i0 + 1), List.range_succ_eq_map, List.map_cons,
        List.map_map]
      congr 1
      · simp
      · apply List.map_congr_left
        intro k _
        simp only [Function.comp_apply]
        push_cast
        omega

/-- `intRange 0 n` is `List.range n`, cast to `Int`. -/
theorem intRange_zero (n : Nat) : intRange 0 n = (List.range n).map fun k : Nat => (k : Int) := by
  rw [intRange_eq_map]
  simp

/-- **Bound-agnostic ascending genvar sequence**: a `+1` loop from `i0`
whose bound evaluates (under the genvar's binding) to SOME constant that is
zero exactly when the genvar has reached `N` — `g < e`, `g s< e`,
`g <= e - 1`, … — produces `i0, …, N-1`, provided the fuel exceeds the trip
count. (`genvarSeq_ascending` in `Param.lean` is the `s<` instance;
this is its generalization, proved the same way.) -/
theorem genvarSeq_ascending_of {env : IEnv} {g : String} {bound : PExpr} {N : Int}
    (hb : ∀ i : Int, ∃ c, evalInt (env.bindVal g i) bound = .ok c ∧ (c = 0 ↔ N ≤ i)) :
    ∀ {fuel : Nat} (i0 : Int), (N - i0).toNat < fuel →
      genvarSeq env g bound 1 fuel i0 = .ok (intRange i0 (N - i0).toNat) := by
  intro fuel
  induction fuel with
  | zero => intro i0 h; omega
  | succ fuel ih =>
      intro i0 hfuel
      obtain ⟨c, hc, hciff⟩ := hb i0
      by_cases hlt : i0 < N
      · have hc0 : c ≠ 0 := fun h => by have := hciff.mp h; omega
        have hcount : (N - i0).toNat = (N - (i0 + 1)).toNat + 1 := by omega
        have hrec := ih (i0 + 1) (by omega)
        rw [hcount]
        simp [genvarSeq, hc, hc0, hrec, intRange]
      · have hc0 : c = 0 := hciff.mpr (by omega)
        have hz : (N - i0).toNat = 0 := by omega
        rw [hz]
        simp [genvarSeq, hc, hc0, intRange]

section genfor

variable {env : IEnv} {elems : List (String × Nat)} {F : Nat}

/-- **The canonical ascending generate-for** (`for (g = i0; g s< e; g++)`
with a loop-invariant bound `e ⇓ N` and enough fuel) expands to the body
template iterated over `intRange i0 (N - i0).toNat` — via the shared
`genvarSeq_ascending`. -/
theorem GenItem.expand2_genFor_ascending {label : Option String} {g : String}
    {initE e : PExpr} {rc : Option Nat} {body : List GenItem} {i0 N : Int}
    (hi : evalInt env initE = .ok i0)
    (hei : ∀ i : Int, e.isInt (env.bindVal g i) = true)
    (he : ∀ i : Int, evalInt (env.bindVal g i) e = .ok N)
    (hF : (N - i0).toNat < F) :
    (GenItem.genFor label g initE (.binary .slt (.genvarRef g) e)
        (.unary .inc (.genvarRef g)) rc body).expand2 env elems F =
      expandIters2 env elems F g (intRange i0 (N - i0).toNat) body :=
  GenItem.expand2_genFor_of hi (stepDelta_inc g) (genvarSeq_ascending hei he i0 hF)

/-- The bound-agnostic form of `GenItem.expand2_genFor_ascending`
(any bound characterized as in `genvarSeq_ascending_of`). -/
theorem GenItem.expand2_genFor_ascending_of {label : Option String} {g : String}
    {initE bound : PExpr} {rc : Option Nat} {body : List GenItem} {i0 N : Int}
    (hi : evalInt env initE = .ok i0)
    (hb : ∀ i : Int, ∃ c, evalInt (env.bindVal g i) bound = .ok c ∧ (c = 0 ↔ N ≤ i))
    (hF : (N - i0).toNat < F) :
    (GenItem.genFor label g initE bound (.unary .inc (.genvarRef g)) rc body).expand2 env elems F =
      expandIters2 env elems F g (intRange i0 (N - i0).toNat) body :=
  GenItem.expand2_genFor_of hi (stepDelta_inc g) (genvarSeq_ascending_of hb i0 hF)

/-- The canonical ascending loop over ANY body whose per-value expansion is
known on the loop's range — the nested-loop handle (`f v` is, e.g., the
inner `for (j …)` loop's expansion under `g := v`). -/
theorem GenItem.expand2_genFor_ascending_flatMap {label : Option String} {g : String}
    {initE e : PExpr} {rc : Option Nat} {body : List GenItem} {i0 N : Int}
    {f : Int → List Process2}
    (hi : evalInt env initE = .ok i0)
    (hei : ∀ i : Int, e.isInt (env.bindVal g i) = true)
    (he : ∀ i : Int, evalInt (env.bindVal g i) e = .ok N)
    (hF : (N - i0).toNat < F)
    (hf : ∀ v : Int, i0 ≤ v → v < N → expandList2 (env.bindVal g v) elems F body = .ok (f v)) :
    (GenItem.genFor label g initE (.binary .slt (.genvarRef g) e)
        (.unary .inc (.genvarRef g)) rc body).expand2 env elems F =
      .ok ((intRange i0 (N - i0).toNat).flatMap f) := by
  rw [GenItem.expand2_genFor_ascending hi hei he hF, expandIters2_eq_flatten (f := f), List.flatMap_def]
  intro v hv
  rw [mem_intRange] at hv
  exact hf v hv.1 (by omega)

/-- The canonical ascending loop over a body of plain processes, in one
step: the `flatMap` of the per-genvar instantiation over `intRange`. -/
theorem GenItem.expand2_genFor_ascending_processes {label : Option String} {g : String}
    {initE e : PExpr} {rc : Option Nat} {ps : List PProcess} {i0 N : Int}
    (hi : evalInt env initE = .ok i0)
    (hei : ∀ i : Int, e.isInt (env.bindVal g i) = true)
    (he : ∀ i : Int, evalInt (env.bindVal g i) e = .ok N)
    (hF : (N - i0).toNat < F) :
    (GenItem.genFor label g initE (.binary .slt (.genvarRef g) e)
        (.unary .inc (.genvarRef g)) rc (ps.map GenItem.process)).expand2 env elems F =
      .ok ((intRange i0 (N - i0).toNat).flatMap fun v =>
        ps.map (instProcess2 (env.bindVal g v) elems)) := by
  rw [GenItem.expand2_genFor_ascending hi hei he hF, expandIters2_processes]

end genfor

/-! ## The `instantiate2` decomposition -/

/-- The environment `instantiate2` builds BEFORE the declarations: the
parameters zipped with `args`, the localparams and enum tables in order,
the typed-parameter width table (`pwidths`), and the packed-array geometry
table (`dims` — `dimTable`, evaluated once in that declaration scope).
Verbatim the first half of `PDesign.instantiate2`'s `do` block. -/
def PDesign.paramEnv2 (d : PDesign) (args : List Int) : Res IEnv := do
  let env0 ← bindParamsRes {} d.params args
  let env1 ← bindLocals env0 d.localParams
  let env2 ← bindEnums env1 d.enums
  let pws ← (d.params.map (fun p => (p.name, p.type?))
              ++ d.localParams.map (fun lp => (lp.name, lp.type?))).filterMapM
    fun (n, ty?) =>
      match ty? with
      | none => pure none
      | some ty =>
          match ty.width env2 with
          | .ok w => pure (some (n, w))
          | .error e => Res.unsupported s!"parameter '{n}' type: {e}"
  let env2 := { env2 with pwidths := pws }
  .ok { env2 with dims := dimTable env2 d.decls }

/-- The process-and-declaration environment: `env` with the declared widths
of `decls` (what `instantiate2` instantiates processes and generates in). -/
abbrev IEnv.withDecls (env : IEnv) (decls : List Decl) : IEnv :=
  { env with widths := decls.map fun dc => (dc.name, dc.width) }

/-- The `Design2` assembled by `instantiate2` from its parts: the
instantiated static processes, then the generate expansion `gens`, then the
out-of-tier members as loud `unsupported` processes. -/
def PDesign.assemble2 (d : PDesign) (env : IEnv) (decls : List Decl)
    (elems : List (String × Nat)) (gens : List Process2) : Design2 :=
  { name := d.name
    decls := decls.toArray
    processes :=
      ((d.processes.map (instProcess2 (env.withDecls decls) elems)) ++ gens
        ++ d.others.map fun kt => Process2.unsupported kt.1 kt.2).toArray }

/-- **`instantiate2` decomposed** (arity respected): the parameter
environment, then declarations, element widths, generate expansion, and the
assembled design — the `do` block of `PDesign.instantiate2` with its
parameter half named `paramEnv2`. -/
theorem PDesign.instantiate2_eq (d : PDesign) (args : List Int) (F : Nat)
    (harity : args.length = d.params.length) :
    d.instantiate2 args F =
      (d.paramEnv2 args >>= fun env =>
        buildDecls env d.decls >>= fun decls =>
        buildElems env d.decls >>= fun elems =>
        expandList2 (env.withDecls decls) elems F d.generates >>= fun gens =>
        .ok (d.assemble2 env decls elems gens)) := by
  unfold PDesign.instantiate2 PDesign.instantiate2From PDesign.paramEnv2
  simp only [harity, bne_self_eq_false, Bool.false_eq_true, if_false, Gen2.res_bind_assoc,
    Res.ok_bind]
  rfl

/-- Inversion of a successful `instantiate2`: every stage succeeded, and the
result is the assembled design. -/
theorem PDesign.instantiate2_eq_ok_iff {d : PDesign} {args : List Int} {F : Nat}
    {m : Design2} :
    d.instantiate2 args F = .ok m ↔
      args.length = d.params.length ∧
      ∃ env decls elems gens,
        d.paramEnv2 args = .ok env ∧
        buildDecls env d.decls = .ok decls ∧
        buildElems env d.decls = .ok elems ∧
        expandList2 (env.withDecls decls) elems F d.generates = .ok gens ∧
        m = d.assemble2 env decls elems gens := by
  by_cases harity : args.length = d.params.length
  · rw [PDesign.instantiate2_eq d args F harity]
    simp only [Res.bind_eq_ok, harity, true_and]
    constructor
    · rintro ⟨env, h1, decls, h2, elems, h3, gens, h4, h5⟩
      exact ⟨env, decls, elems, gens, h1, h2, h3, h4, (Res.ok.inj h5).symm⟩
    · rintro ⟨env, decls, elems, gens, h1, h2, h3, h4, rfl⟩
      exact ⟨env, h1, decls, h2, elems, h3, gens, h4, rfl⟩
  · have hne : (args.length != d.params.length) = true := by simpa using harity
    unfold PDesign.instantiate2 PDesign.instantiate2From
    simp [hne, harity]

/-- The constructive direction: decided stages assemble the design. -/
theorem PDesign.instantiate2_of_ok {d : PDesign} {args : List Int} {F : Nat} {env : IEnv}
    {decls : List Decl} {elems : List (String × Nat)} {gens : List Process2}
    (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (h2 : buildDecls env d.decls = .ok decls)
    (h3 : buildElems env d.decls = .ok elems)
    (h4 : expandList2 (env.withDecls decls) elems F d.generates = .ok gens) :
    d.instantiate2 args F = .ok (d.assemble2 env decls elems gens) :=
  PDesign.instantiate2_eq_ok_iff.mpr ⟨harity, env, decls, elems, gens, h1, h2, h3, h4, rfl⟩

@[simp] theorem PDesign.assemble2_processes (d : PDesign) (env : IEnv) (decls : List Decl)
    (elems : List (String × Nat)) (gens : List Process2) :
    (d.assemble2 env decls elems gens).processes.toList =
      d.processes.map (instProcess2 (env.withDecls decls) elems) ++ gens
        ++ d.others.map fun kt => Process2.unsupported kt.1 kt.2 := by
  simp [PDesign.assemble2]

@[simp] theorem PDesign.assemble2_decls (d : PDesign) (env : IEnv) (decls : List Decl)
    (elems : List (String × Nat)) (gens : List Process2) :
    (d.assemble2 env decls elems gens).decls.toList = decls := by
  simp [PDesign.assemble2]

@[simp] theorem PDesign.assemble2_name (d : PDesign) (env : IEnv) (decls : List Decl)
    (elems : List (String × Nat)) (gens : List Process2) :
    (d.assemble2 env decls elems gens).name = d.name := rfl

/-- The process list of a successful instantiation: static processes,
generate expansion, loud `others` — in that order. -/
theorem PDesign.instantiate2_processes {d : PDesign} {args : List Int} {F : Nat}
    {m : Design2} (h : d.instantiate2 args F = .ok m) :
    ∃ env decls elems gens,
      d.paramEnv2 args = .ok env ∧
      buildDecls env d.decls = .ok decls ∧
      buildElems env d.decls = .ok elems ∧
      expandList2 (env.withDecls decls) elems F d.generates = .ok gens ∧
      m.processes.toList =
        d.processes.map (instProcess2 (env.withDecls decls) elems) ++ gens
          ++ d.others.map (fun kt => Process2.unsupported kt.1 kt.2) ∧
      m.decls.toList = decls ∧ m.name = d.name := by
  obtain ⟨_, env, decls, elems, gens, h1, h2, h3, h4, rfl⟩ :=
    PDesign.instantiate2_eq_ok_iff.mp h
  exact ⟨env, decls, elems, gens, h1, h2, h3, h4, by simp, by simp, rfl⟩

/-- Instantiation preserves the declaration surface (names and port
directions; the `instantiate2` twin of `instantiate_declSig`). -/
theorem PDesign.instantiate2_declSig {d : PDesign} {args : List Int} {F : Nat} {m : Design2}
    (h : d.instantiate2 args F = .ok m) :
    m.decls.toList.map (fun dc => (dc.name, dc.isInput, dc.isOutput)) = d.declSig := by
  obtain ⟨_, decls, _, _, _, h2, _, _, _, hd, _⟩ := PDesign.instantiate2_processes h
  rw [hd]
  simpa [PDesign.declSig] using buildDecls_sig h2

/-- Declared names are parameter-independent. -/
theorem PDesign.instantiate2_declNames {d : PDesign} {args : List Int} {F : Nat} {m : Design2}
    (h : d.instantiate2 args F = .ok m) :
    m.decls.toList.map (·.name) = d.declNames := by
  have hs := PDesign.instantiate2_declSig h
  have h1 : (m.decls.toList.map (fun dc => (dc.name, dc.isInput, dc.isOutput))).map Prod.fst
      = d.declSig.map Prod.fst := by rw [hs]
  simpa [PDesign.declSig, PDesign.declNames, List.map_map, Function.comp_def] using h1

/-- The instantiated design's name is the source module name. -/
theorem PDesign.instantiate2_name {d : PDesign} {args : List Int} {F : Nat} {m : Design2}
    (h : d.instantiate2 args F = .ok m) : m.name = d.name := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hn⟩ := PDesign.instantiate2_processes h
  exact hn

/-- The total family agrees with a successful instantiation at the
surface fuel. -/
theorem PDesign.instantiateD2_of_ok {d : PDesign} {args : List Int} {m : Design2}
    (h : d.instantiate2 args (PDesign.surfaceFuel args) = .ok m) :
    d.instantiateD2 args = m := by
  simp [PDesign.instantiateD2, h]

/-! ## Declaration widths (public handles on `Param.lean`'s private
`dimsWidth`) -/

/-- A scalar packed type is one bit wide. -/
@[simp] theorem PType.width_packed_nil (env : IEnv) (r : Option Nat) :
    (PType.packed [] r).width env = .ok 1 := rfl

/-- Packed widths multiply, outermost dimension first. -/
theorem PType.width_packed_cons (env : IEnv) (d : PDim) (ds : List PDim) (r : Option Nat) :
    (PType.packed (d :: ds) r).width env =
      (d.width env >>= fun w => (PType.packed ds r).width env >>= fun ws => .ok (w * ws)) := rfl

/-- One packed dimension `[msb:lsb]`: `|msb - lsb| + 1`. -/
theorem PType.width_packed_single_of {env : IEnv} {msb lsb : PExpr} {m l : Int}
    (r : Option Nat) (hm : evalInt env msb = .ok m) (hl : evalInt env lsb = .ok l) :
    (PType.packed [⟨msb, lsb⟩] r).width env = .ok ((m - l).natAbs + 1) := by
  rw [PType.width_packed_cons]
  simp [PDim.width, hm, hl]

/-- A packed type's element width: `1` for scalars and 1-D vectors. -/
@[simp] theorem PType.elemWidth_packed_single (env : IEnv) (d : PDim) (r : Option Nat) :
    (PType.packed [d] r).elemWidth env = .ok 1 := rfl

@[simp] theorem PType.elemWidth_packed_nil (env : IEnv) (r : Option Nat) :
    (PType.packed [] r).elemWidth env = .ok 1 := rfl

/-! ## Symbolic-parameter support: the constant tier (`evalInt`) -/

section evalInt

variable {env : IEnv}

@[simp] theorem IEnv.bindVal_vals (env : IEnv) (n : String) (v : Int) :
    (env.bindVal n v).vals = (n, v) :: env.vals := rfl

@[simp] theorem IEnv.bindVal_widths (env : IEnv) (n : String) (v : Int) :
    (env.bindVal n v).widths = env.widths := rfl

@[simp] theorem IEnv.withDecls_vals (env : IEnv) (decls : List Decl) :
    (env.withDecls decls).vals = env.vals := rfl

@[simp] theorem IEnv.bindVal_dims (env : IEnv) (n : String) (v : Int) :
    (env.bindVal n v).dims = env.dims := rfl

@[simp] theorem IEnv.withDecls_dims (env : IEnv) (decls : List Decl) :
    (env.withDecls decls).dims = env.dims := rfl

@[simp] theorem IEnv.withDecls_widths (env : IEnv) (decls : List Decl) :
    (env.withDecls decls).widths = decls.map fun dc => (dc.name, dc.width) := rfl

@[simp] theorem IEnv.bindVal_stale (env : IEnv) (n : String) (v : Int) :
    (env.bindVal n v).stale = env.stale := rfl

@[simp] theorem IEnv.withDecls_stale (env : IEnv) (decls : List Decl) :
    (env.withDecls decls).stale = env.stale := rfl

@[simp] theorem IEnv.bindVal_nvals (env : IEnv) (n : String) (v : Int) :
    (env.bindVal n v).nvals = env.nvals := rfl

@[simp] theorem IEnv.withDecls_nvals (env : IEnv) (decls : List Decl) :
    (env.withDecls decls).nvals = env.nvals := rfl

@[simp] theorem evalInt_int (v : Int) : evalInt env (.int v) = .ok v := rfl

theorem evalInt_paramRef_of {n : String} {v : Int} (h : env.vals.lookup n = some v) :
    evalInt env (.paramRef n none) = .ok v := by
  simp [evalInt, h]

/-- A parameter bound in `vals` is in the INT class (`PExpr.isInt`) — the
side condition of the compositional `evalInt_*_of` lemmas below. -/
theorem isInt_paramRef_of {n : String} {v : Int} (h : env.vals.lookup n = some v) :
    (PExpr.paramRef n none).isInt env = true := by
  simp only [PExpr.isInt, h, Option.isSome_some]

/-- INT-class operands of an INT operator make an INT-class node. -/
theorem isInt_binary_of {op : SymBinOp} {l r : PExpr} (hop : op.intArith = true)
    (hl : l.isInt env = true) (hr : r.isInt env = true) :
    (PExpr.binary op l r).isInt env = true := by
  simp only [PExpr.isInt, hop, hl, hr, Bool.and_self]

theorem evalInt_genvarRef_of {n : String} {v : Int} (h : env.vals.lookup n = some v) :
    evalInt env (.genvarRef n) = .ok v := by
  simp [evalInt, h]

theorem evalInt_add_of {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary (.m0 .add) l r) = .ok (a + b) := by
  simp [evalInt, hil, hir, hl, hr]

theorem evalInt_sub_of {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary (.m0 .sub) l r) = .ok (a - b) := by
  simp [evalInt, hil, hir, hl, hr]

theorem evalInt_mul_of {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary .mul l r) = .ok (a * b) := by
  simp [evalInt, hil, hir, hl, hr]

theorem evalInt_m0_mul_of {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary (.m0 .mul) l r) = .ok (a * b) := by
  simp [evalInt, hil, hir, hl, hr]

/-- Signed `<` as an `if` (the generate-bound shape, `b2i`-free). -/
theorem evalInt_slt_of {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary .slt l r) = .ok (if a < b then 1 else 0) := by
  simp only [evalInt, hil, hir, Bool.and_self, if_true, hl, hr, Gen2.except_ok_bind]
  by_cases h : a < b
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

/-- Unsigned-spelled `<` (`.m0 .lt`) on constants: same as `s<`. -/
theorem evalInt_lt_of {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary (.m0 .lt) l r) = .ok (if a < b then 1 else 0) := by
  simp only [evalInt, hil, hir, Bool.and_self, if_true, hl, hr, Gen2.except_ok_bind]
  by_cases h : a < b
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

theorem evalInt_sle_of {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary .sle l r) = .ok (if a ≤ b then 1 else 0) := by
  simp only [evalInt, hil, hir, Bool.and_self, if_true, hl, hr, Gen2.except_ok_bind]
  by_cases h : a ≤ b
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

theorem evalInt_le_of {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary (.m0 .le) l r) = .ok (if a ≤ b then 1 else 0) := by
  simp only [evalInt, hil, hir, Bool.and_self, if_true, hl, hr, Gen2.except_ok_bind]
  by_cases h : a ≤ b
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

theorem evalInt_eq_of {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary (.m0 .eq) l r) = .ok (if a = b then 1 else 0) := by
  simp only [evalInt, hil, hir, Bool.and_self, if_true, hl, hr, Gen2.except_ok_bind]
  by_cases h : a = b
  · subst h; rw [if_pos rfl, beq_self_eq_true]; rfl
  · rw [if_neg h, beq_false_of_ne h]; rfl

theorem evalInt_ne_of {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary (.m0 .ne) l r) = .ok (if a = b then 0 else 1) := by
  simp only [evalInt, hil, hir, Bool.and_self, if_true, hl, hr, Gen2.except_ok_bind]
  by_cases h : a = b
  · subst h; rw [if_pos rfl, bne_self_eq_false]; rfl
  · rw [if_neg h, bne_iff_ne.mpr h]; rfl

theorem evalInt_sgt_of {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary .sgt l r) = .ok (if a > b then 1 else 0) := by
  simp only [evalInt, hil, hir, Bool.and_self, if_true, hl, hr, Gen2.except_ok_bind]
  by_cases h : a > b
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

theorem evalInt_gt_of {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary (.m0 .gt) l r) = .ok (if a > b then 1 else 0) := by
  simp only [evalInt, hil, hir, Bool.and_self, if_true, hl, hr, Gen2.except_ok_bind]
  by_cases h : a > b
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

theorem evalInt_sge_of {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary .sge l r) = .ok (if a ≥ b then 1 else 0) := by
  simp only [evalInt, hil, hir, Bool.and_self, if_true, hl, hr, Gen2.except_ok_bind]
  by_cases h : a ≥ b
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

theorem evalInt_ge_of {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary (.m0 .ge) l r) = .ok (if a ≥ b then 1 else 0) := by
  simp only [evalInt, hil, hir, Bool.and_self, if_true, hl, hr, Gen2.except_ok_bind]
  by_cases h : a ≥ b
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

/-- The width-exact constant evaluator on a select of a signal: loud (the
same message the INT path gives), whatever the labels. -/
@[simp] theorem evalSized_bitSel_ident (n : String) (idx : PExpr) :
    evalSized env (.bitSel (.ident n) idx) = .error s!"signal '{n}' in a constant context" := rfl

@[simp] theorem evalSized_partSel_ident (n : String) (msb lsb : PExpr) :
    evalSized env (.partSel (.ident n) msb lsb) =
      .error s!"signal '{n}' in a constant context" := rfl

/-- A select of a signal is never a constant (the `instExpr2` select arm
falls through to the declared-signal tier). -/
@[simp] theorem evalInt_bitSel_ident (n : String) (idx : PExpr) :
    evalInt env (.bitSel (.ident n) idx) = .error s!"signal '{n}' in a constant context" := rfl

@[simp] theorem evalInt_partSel_ident (n : String) (msb lsb : PExpr) :
    evalInt env (.partSel (.ident n) msb lsb) =
      .error s!"signal '{n}' in a constant context" := rfl

end evalInt

/-! ## Symbolic-parameter support: the value tier -/

section valueTier

variable {env : IEnv} {elems : List (String × Nat)}

@[simp] theorem rigidExpr_lit (v : LVec) : rigidExpr (.lit v) = true := rfl
@[simp] theorem rigidExpr_ident (n : String) : rigidExpr (.ident n) = true := rfl
@[simp] theorem rigidExpr_bitSel (b i : PExpr) : rigidExpr (.bitSel b i) = true := rfl
@[simp] theorem rigidExpr_partSel (b m l : PExpr) : rigidExpr (.partSel b m l) = true := rfl
@[simp] theorem rigidExpr_concat (ps : List PExpr) : rigidExpr (.concat ps) = true := rfl
@[simp] theorem rigidExpr_repl (c a : PExpr) : rigidExpr (.repl c a) = true := rfl
@[simp] theorem rigidExpr_reduce (op : RedOp) (a : PExpr) : rigidExpr (.reduce op a) = true := rfl
@[simp] theorem rigidExpr_cast (s : Bool) (a : PExpr) : rigidExpr (.cast s a) = rigidExpr a := rfl
@[simp] theorem rigidExpr_binary (op : SymBinOp) (l r : PExpr) :
    rigidExpr (.binary op l r) = false := rfl
@[simp] theorem rigidExpr_unary (op : SymUnaryOp) (a : PExpr) :
    rigidExpr (.unary op a) = false := rfl
@[simp] theorem rigidExpr_ternary (c t e : PExpr) : rigidExpr (.ternary c t e) = false := rfl
@[simp] theorem rigidExpr_int (v : Int) : rigidExpr (.int v) = false := rfl

@[simp] theorem elemOf_ident (n : String) : elemOf elems (.ident n) = elems.lookup n := rfl

@[simp] theorem selfWidth2_lit (v : LVec) : selfWidth2 env elems (.lit v) = some v.width := by
  simp [selfWidth2]

@[simp] theorem selfWidth2_ident (n : String) :
    selfWidth2 env elems (.ident n) = env.widths.lookup n := by
  simp [selfWidth2]

/-- A select of a declared signal: its element width (`none` when the
signal is undeclared — a signal select is never a constant). -/
@[simp] theorem selfWidth2_bitSel_ident (n : String) (i : PExpr) :
    selfWidth2 env elems (.bitSel (.ident n) i) = elems.lookup n := by
  cases h : elems.lookup n <;> simp [selfWidth2, h]

/-- A select of a base with an element width: that width. -/
theorem selfWidth2_bitSel_of {b i : PExpr} {ew : Nat} (h : elemOf elems b = some ew) :
    selfWidth2 env elems (.bitSel b i) = some ew := by
  simp [selfWidth2, h]

/-- A select's width is its base's element width whenever the base has one
(a conditional rewrite: a parameter/genvar-CONSTANT select such as `i[0]`,
whose base has none, is one bit instead). -/
theorem selfWidth2_bitSel {b i : PExpr} (h : (elemOf elems b).isSome) :
    selfWidth2 env elems (.bitSel b i) = elemOf elems b := by
  obtain ⟨ew, hew⟩ := Option.isSome_iff_exists.mp h
  rw [selfWidth2_bitSel_of hew, hew]

theorem selfWidth2_partSel_of {b msb lsb : PExpr} {ew : Nat} {m l : Int}
    (hb : elemOf elems b = some ew) (hm : evalInt env msb = .ok m)
    (hl : evalInt env lsb = .ok l) (h : 0 ≤ l ∧ l ≤ m) :
    selfWidth2 env elems (.partSel b msb lsb) = some (((m - l).toNat + 1) * ew) := by
  simp [selfWidth2, hb, hm, hl, h.1, h.2]

@[simp] theorem selfWidth2_concat (ps : List PExpr) :
    selfWidth2 env elems (.concat ps) = selfWidthSum2 env elems ps := by
  simp [selfWidth2]

@[simp] theorem selfWidthSum2_nil : selfWidthSum2 env elems [] = some 0 := by
  simp [selfWidthSum2]

theorem selfWidthSum2_cons_of {p : PExpr} {ps : List PExpr} {a b : Nat}
    (hp : selfWidth2 env elems p = some a) (hps : selfWidthSum2 env elems ps = some b) :
    selfWidthSum2 env elems (p :: ps) = some (a + b) := by
  simp [selfWidthSum2, hp, hps]

@[simp] theorem instExpr2_lit (ctx : Option Nat) (v : LVec) :
    instExpr2 env elems ctx (.lit v) = .lit v := by
  simp [instExpr2]

@[simp] theorem instExpr2_ident (ctx : Option Nat) (n : String) :
    instExpr2 env elems ctx (.ident n) = .ident n := by
  simp [instExpr2]

/-- Unsized integers materialize at the context width (32 without one). -/
@[simp] theorem instExpr2_int (ctx : Option Nat) (v : Int) :
    instExpr2 env elems ctx (.int v) = .lit (LVec.ofInt (ctx.getD 32) v) := by
  simp [instExpr2]; rfl

theorem instExpr2_paramRef_of (ctx : Option Nat) {n : String} {v : Int}
    (h : env.vals.lookup n = some v) :
    instExpr2 env elems ctx (.paramRef n none) = .lit (LVec.ofInt (ctx.getD 32) v) := by
  simp [instExpr2, h]; rfl

theorem instExpr2_genvarRef_of (ctx : Option Nat) {n : String} {v : Int}
    (h : env.vals.lookup n = some v) :
    instExpr2 env elems ctx (.genvarRef n) = .lit (LVec.ofInt (ctx.getD 32) v) := by
  simp [instExpr2, h]; rfl

/-- Bitwise `&` pushes the context width into both operands. -/
@[simp] theorem instExpr2_and (w : Nat) (l r : PExpr) :
    instExpr2 env elems (some w) (.binary (.m0 .and) l r) =
      .binary .and (fitExpr2 env elems (some w) l) (fitExpr2 env elems (some w) r) := by
  simp [instExpr2]

@[simp] theorem instExpr2_or (w : Nat) (l r : PExpr) :
    instExpr2 env elems (some w) (.binary (.m0 .or) l r) =
      .binary .or (fitExpr2 env elems (some w) l) (fitExpr2 env elems (some w) r) := by
  simp [instExpr2]

@[simp] theorem instExpr2_xor (w : Nat) (l r : PExpr) :
    instExpr2 env elems (some w) (.binary (.m0 .xor) l r) =
      .binary .xor (fitExpr2 env elems (some w) l) (fitExpr2 env elems (some w) r) := by
  simp [instExpr2]

/-- `+` pushes the context width into both operands when no operand that
can carry x is wider than the context (`ctxOpWidth2`); otherwise the sum
runs at the operands' width and is truncated (`instExpr2`). -/
theorem instExpr2_add (w : Nat) (l r : PExpr)
    (hw : (ctxOpWidth2 env elems l r).getD w ≤ w) :
    instExpr2 env elems (some w) (.binary (.m0 .add) l r) =
      .binary .add (fitExpr2 env elems (some w) l) (fitExpr2 env elems (some w) r) := by
  simp [instExpr2, hw]

theorem instExpr2_sub (w : Nat) (l r : PExpr)
    (hw : (ctxOpWidth2 env elems l r).getD w ≤ w) :
    instExpr2 env elems (some w) (.binary (.m0 .sub) l r) =
      .binary .sub (fitExpr2 env elems (some w) l) (fitExpr2 env elems (some w) r) := by
  simp [instExpr2, hw]

/-- Concatenation parts are self-determined. -/
@[simp] theorem instExpr2_concat (ctx : Option Nat) (ps : List PExpr) :
    instExpr2 env elems ctx (.concat ps) = .concat (instParts2 env elems ps).toArray := by
  simp [instExpr2]

@[simp] theorem instParts2_nil : instParts2 env elems [] = [] := by
  simp [instParts2]

@[simp] theorem instParts2_cons (p : PExpr) (ps : List PExpr) :
    instParts2 env elems (p :: ps) =
      instExpr2 env elems (selfWidth2 env elems p) p :: instParts2 env elems ps := by
  simp [instParts2]

/-- **Constant-index select of a declared signal**: an `elemW`-wide
`slice` at offset `i * elemW` (the genvar-index shape `x[i]`, `x[i*N+j]`,
… once the index evaluates). -/
theorem instExpr2_bitSel_ident (ctx : Option Nat) {n : String} {idx : PExpr} {ew : Nat}
    {i : Int} (hel : elems.lookup n = some ew) (hi : evalInt env idx = .ok i) (h0 : 0 ≤ i) :
    instExpr2 env elems ctx (.bitSel (.ident n) idx) = .slice (.ident n) (i.toNat * ew) ew := by
  simp [instExpr2, hel, hi, h0]

/-- Non-constant-index select of a declared signal: a dynamic `index`. -/
theorem instExpr2_bitSel_ident_dyn (ctx : Option Nat) {n : String} {idx : PExpr} {ew : Nat}
    {e : String} (hel : elems.lookup n = some ew) (hi : evalInt env idx = .error e) :
    instExpr2 env elems ctx (.bitSel (.ident n) idx) =
      .index (.ident n) (instExpr2 env elems (selfWidth2 env elems idx) idx) ew := by
  simp [instExpr2, hel, hi]

/-- Constant part-select `n[msb:lsb]` of a declared signal. -/
theorem instExpr2_partSel_ident (ctx : Option Nat) {n : String} {msb lsb : PExpr} {ew : Nat}
    {m l : Int} (hel : elems.lookup n = some ew) (hm : evalInt env msb = .ok m)
    (hl : evalInt env lsb = .ok l) (h : 0 ≤ l ∧ l ≤ m)
    (h31 : msb.isInt env = true ∨ m < 2 ^ 31) :
    instExpr2 env elems ctx (.partSel (.ident n) msb lsb) =
      .slice (.ident n) (l.toNat * ew) (((m - l).toNat + 1) * ew) := by
  rcases h31 with h31 | h31
  · simp [instExpr2, hel, hm, hl, h.1, h.2, h31]
  · have h31n : m < 2147483648 := by simpa using h31
    simp [instExpr2, hel, hm, hl, h.1, h.2, h31n]

/-- Without a context width, `fitExpr2` is plain instantiation. -/
@[simp] theorem fitExpr2_none (e : PExpr) :
    fitExpr2 env elems none e = instExpr2 env elems none e := by
  simp [fitExpr2]

/-- A context-directed (non-rigid) expression takes the context width. -/
theorem fitExpr2_of_not_rigid {e : PExpr} (w : Nat) (h : rigidExpr e = false) :
    fitExpr2 env elems (some w) e = instExpr2 env elems (some w) e := by
  simp [fitExpr2, h]

/-- A rigid expression already at the context width is not resized. -/
theorem fitExpr2_of_rigid_eq {e : PExpr} {w : Nat} (hr : rigidExpr e = true)
    (hw : selfWidth2 env elems e = some w) :
    fitExpr2 env elems (some w) e = instExpr2 env elems (some w) e := by
  simp [fitExpr2, hr, hw]

/-- **The one node `fitExpr2` inserts**: a rigid expression of a known,
different width is wrapped in `.resize w` (instantiated at its own width). -/
theorem fitExpr2_of_rigid_ne {e : PExpr} {w sw : Nat} (hr : rigidExpr e = true)
    (hw : selfWidth2 env elems e = some sw) (hne : sw ≠ w) (hs : e.signedCast = false) :
    fitExpr2 env elems (some w) e = .resize w (instExpr2 env elems (some sw) e) := by
  simp [fitExpr2, hr, hw, hne, hs, -PExpr.signedCast]

/-- A rigid expression of unknown width is instantiated at the context. -/
theorem fitExpr2_of_rigid_none {e : PExpr} (w : Nat) (hr : rigidExpr e = true)
    (hw : selfWidth2 env elems e = none) :
    fitExpr2 env elems (some w) e = instExpr2 env elems (some w) e := by
  simp [fitExpr2, hr, hw]

/-- Operator expressions are never resized at their root. -/
@[simp] theorem fitExpr2_binary (w : Nat) (op : SymBinOp) (l r : PExpr) :
    fitExpr2 env elems (some w) (.binary op l r) = instExpr2 env elems (some w) (.binary op l r) :=
  fitExpr2_of_not_rigid w rfl

theorem fitExpr2_ident {n : String} {w : Nat} (hw : env.widths.lookup n = some w) :
    fitExpr2 env elems (some w) (.ident n) = .ident n := by
  rw [fitExpr2_of_rigid_eq rfl (by simpa using hw)]
  simp

theorem fitExpr2_ident_resize {n : String} {w sw : Nat} (hw : env.widths.lookup n = some sw)
    (hne : sw ≠ w) :
    fitExpr2 env elems (some w) (.ident n) = .resize w (.ident n) := by
  rw [fitExpr2_of_rigid_ne rfl (by simpa using hw) hne rfl]
  simp

theorem fitExpr2_lit (w : Nat) (v : LVec) :
    fitExpr2 env elems (some w) (.lit v) =
      if v.width = w then .lit v else .resize w (.lit v) := by
  by_cases h : v.width = w
  · rw [if_pos h, fitExpr2_of_rigid_eq rfl (by simp [h])]; simp
  · rw [if_neg h, fitExpr2_of_rigid_ne rfl (by simp) h rfl]; simp

/-- A constant-index select at its element width (the gate-level operand
shape): exactly the `slice`, no resize. -/
theorem fitExpr2_bitSel_ident {n : String} {idx : PExpr} {ew : Nat} {i : Int}
    (hel : elems.lookup n = some ew) (hi : evalInt env idx = .ok i) (h0 : 0 ≤ i) :
    fitExpr2 env elems (some ew) (.bitSel (.ident n) idx) =
      .slice (.ident n) (i.toNat * ew) ew := by
  rw [fitExpr2_of_rigid_eq rfl (by simpa using hel), instExpr2_bitSel_ident _ hel hi h0]

/-- A constant-index select in a different-width context is resized. -/
theorem fitExpr2_bitSel_ident_resize {n : String} {idx : PExpr} {ew w : Nat} {i : Int}
    (hel : elems.lookup n = some ew) (hi : evalInt env idx = .ok i) (h0 : 0 ≤ i)
    (hne : ew ≠ w) :
    fitExpr2 env elems (some w) (.bitSel (.ident n) idx) =
      .resize w (.slice (.ident n) (i.toNat * ew) ew) := by
  rw [fitExpr2_of_rigid_ne rfl (by simpa using hel) hne rfl, instExpr2_bitSel_ident _ hel hi h0]

/-- A constant part-select at its own width: exactly the `slice`. -/
theorem fitExpr2_partSel_ident {n : String} {msb lsb : PExpr} {ew : Nat} {m l : Int}
    (hel : elems.lookup n = some ew) (hm : evalInt env msb = .ok m)
    (hl : evalInt env lsb = .ok l) (h : 0 ≤ l ∧ l ≤ m)
    (h31 : msb.isInt env = true ∨ m < 2 ^ 31) :
    fitExpr2 env elems (some (((m - l).toNat + 1) * ew)) (.partSel (.ident n) msb lsb) =
      .slice (.ident n) (l.toNat * ew) (((m - l).toNat + 1) * ew) := by
  rw [fitExpr2_of_rigid_eq rfl (selfWidth2_partSel_of (by simpa using hel) hm hl h),
    instExpr2_partSel_ident _ hel hm hl h h31]

/-- A constant part-select in a different-width context is resized. -/
theorem fitExpr2_partSel_ident_resize {n : String} {msb lsb : PExpr} {ew w : Nat} {m l : Int}
    (hel : elems.lookup n = some ew) (hm : evalInt env msb = .ok m)
    (hl : evalInt env lsb = .ok l) (h : 0 ≤ l ∧ l ≤ m)
    (h31 : msb.isInt env = true ∨ m < 2 ^ 31) (hne : ((m - l).toNat + 1) * ew ≠ w) :
    fitExpr2 env elems (some w) (.partSel (.ident n) msb lsb) =
      .resize w (.slice (.ident n) (l.toNat * ew) (((m - l).toNat + 1) * ew)) := by
  rw [fitExpr2_of_rigid_ne rfl (selfWidth2_partSel_of (by simpa using hel) hm hl h) hne rfl,
    instExpr2_partSel_ident _ hel hm hl h h31]

/-- A concatenation: rigid, its width the sum of its parts'. -/
theorem fitExpr2_concat {ps : List PExpr} {w sw : Nat}
    (hw : selfWidthSum2 env elems ps = some sw) :
    fitExpr2 env elems (some w) (.concat ps) =
      if sw = w then .concat (instParts2 env elems ps).toArray
      else .resize w (.concat (instParts2 env elems ps).toArray) := by
  by_cases h : sw = w
  · subst h
    rw [if_pos rfl, fitExpr2_of_rigid_eq rfl (by simpa using hw)]; simp
  · rw [if_neg h, fitExpr2_of_rigid_ne rfl (by simpa using hw) h rfl]; simp

/-- Whole-signal target: the declared width is the RHS context. -/
theorem instLhs2_ident {n : String} {w : Nat} (hw : env.widths.lookup n = some w) :
    instLhs2 env elems (.ident n) = .ok (.ident n, w) := by
  simp [instLhs2, instLhsLeaf2, hw]

/-- Constant-index select target `n[idx]`: an `elemW`-wide slice write. -/
theorem instLhs2_bitSel {n : String} {idx : PExpr} {ew : Nat} {i : Int}
    (hel : elems.lookup n = some ew) (hi : evalInt env idx = .ok i) (h0 : 0 ≤ i) :
    instLhs2 env elems (.bitSel n idx) = .ok (.slice n (i.toNat * ew) ew, ew) := by
  simp [instLhs2, instLhsLeaf2, hel, hi, h0]

/-- Non-constant-index select target: a dynamic `index` write. -/
theorem instLhs2_bitSel_dyn {n : String} {idx : PExpr} {ew : Nat} {e : String}
    (hel : elems.lookup n = some ew) (hi : evalInt env idx = .error e) :
    instLhs2 env elems (.bitSel n idx) =
      .ok (.index n (instExpr2 env elems (selfWidth2 env elems idx) idx) ew, ew) := by
  simp [instLhs2, instLhsLeaf2, hel, hi]

/-- Constant part-select target `n[msb:lsb]`. -/
theorem instLhs2_partSel {n : String} {msb lsb : PExpr} {ew : Nat} {m l : Int}
    (hel : elems.lookup n = some ew) (hm : evalInt env msb = .ok m)
    (hl : evalInt env lsb = .ok l) (h : 0 ≤ l ∧ l ≤ m)
    (h31 : msb.isInt env = true ∨ m < 2 ^ 31) :
    instLhs2 env elems (.partSel n msb lsb) =
      .ok (.slice n (l.toNat * ew) (((m - l).toNat + 1) * ew), ((m - l).toNat + 1) * ew) := by
  rcases h31 with h31 | h31
  · simp [instLhs2, instLhsLeaf2, hel, hm, hl, h.1, h.2, h31]
  · have h31n : m < 2147483648 := by simpa using h31
    simp [instLhs2, instLhsLeaf2, hel, hm, hl, h.1, h.2, h31n]

/-- Whole-signal continuous assign. -/
theorem instProcess2_assign {t : String} {w : Nat} (v : PExpr)
    (hw : env.widths.lookup t = some w) :
    instProcess2 env elems (.assign t v) = .assign (.ident t) (fitExpr2 env elems (some w) v) := by
  simp [instProcess2, hw]

/-- Select-target continuous assign: the lowered target and its width as
the RHS context. -/
theorem instProcess2_assignL {lhs : PLhs} {l2 : Lhs2} {w : Nat} (v : PExpr)
    (h : instLhs2 env elems lhs = .ok (l2, w)) :
    instProcess2 env elems (.assignL lhs v) = .assign l2 (fitExpr2 env elems (some w) v) := by
  simp [instProcess2, h]

@[simp] theorem instProcess2_unsupported (k t : String) :
    instProcess2 env elems (.unsupported k t) = .unsupported k t := by
  simp [instProcess2]

end valueTier

/-! ## Packed-array select paths at symbolic parameters

`PExpr.arrayElem`/`arrayPart` (the envelope's `ArraySel`, nested selects
such as `pp[i][j]`, `s[i-1][j+1]`, `s[N-1][N:1]`) lower through ONE window
computation (`arrayElemWindow` / `arrayPartGeom`): the declaration's
dimensions are read from the declaration-scope geometry table
(`arrayDims_of`; an instantiated environment's entries by `dimTable_lookup_of`
and `evalDims_cons_of`), the labels walk down them
(`walkIndices_cons_of`), and an in-range window is a flat `slice`
(`arrayElemRead_of_inRange`, `arrayElemTarget_of_inRange`, the part
twins). The zero-based descending dimension `[m:0]` — the golf shape —
has label = offset (`labelOffset_desc0`) and `m + 1` elements
(`dimCount_desc0`), so `pp[i][j]` over `[N-1:0][N-1:0]` is the 1-bit window
at `i*N + j` for `i, j < N` (`walkIndices_desc0_cons`). -/

section arraySel

variable {env : IEnv} {elems : List (String × Nat)}

@[simp] theorem rigidExpr_arrayElem (n : String) (is : List PExpr) :
    rigidExpr (.arrayElem n is) = true := rfl

@[simp] theorem rigidExpr_arrayPart (n : String) (is : List PExpr) (m : PartMode) (a b : PExpr) :
    rigidExpr (.arrayPart n is m a b) = true := rfl

/-- A zero-based descending dimension `[m:0]`: the label IS the offset. -/
theorem labelOffset_desc0 {m : Int} (hm : 0 ≤ m) (k : Int) : labelOffset m 0 k = k := by
  simp [labelOffset, hm]

/-- A dimension `[m:0]` (`0 ≤ m`) has `m + 1` elements. -/
theorem dimCount_desc0 {m : Int} (hm : 0 ≤ m) : (dimCount m 0 : Int) = m + 1 := by
  unfold dimCount
  omega

@[simp] theorem dimsStride_nil : dimsStride [] = 1 := rfl

theorem dimsStride_cons (l r : Int) (ds : List (Int × Int)) :
    dimsStride ((l, r) :: ds) = dimCount l r * dimsStride ds := rfl

@[simp] theorem evalDims_nil : evalDims env [] = .ok [] := by
  simp [evalDims]

theorem evalDims_cons_of {d : PDim} {ds : List PDim} {m l : Int} {es : List (Int × Int)}
    (hm : evalInt env d.msb = .ok m) (hl : evalInt env d.lsb = .ok l)
    (hs : evalDims env ds = .ok es) :
    evalDims env (d :: ds) = .ok ((m, l) :: es) := by
  simp [evalDims, hm, hl, hs]

theorem arrayDims_of {n : String} {es : List (Int × Int)}
    (hd : env.dims.lookup n = some es) : arrayDims env n = .ok es := by
  simp [arrayDims, hd]

/-- `dimTable`'s step changes only the declared-width table. -/
theorem dimTableStep_widths (env : IEnv) (pd : PDecl) (ws : List (String × Nat)) :
    { dimTableStep env pd with widths := ws } = { env with widths := ws } := by
  unfold dimTableStep
  split <;> rfl

/-- **The geometry table's entry for a declared array** (`dimTable`, the
`IEnv.dims` that `instantiate2` builds once in the declaration scope): the
first explicit packed dimension list declared under `n`, evaluated. The
dimensions must evaluate to `es` at EVERY declared-width table (the table
threads `buildDecls`'s widths; dimensions built from parameters, localparams
and literals discharge it by the `evalInt` lemmas, whose facts read `vals`
only). -/
theorem dimTable_lookup_of {decls : List PDecl} {n : String} {ds : List PDim}
    {es : List (Int × Int)} (hl : (packedDimsOf decls).lookup n = some ds)
    (he : ∀ ws : List (String × Nat), evalDims { env with widths := ws } ds = .ok es) :
    (dimTable env decls).lookup n = some es := by
  induction decls generalizing env with
  | nil => simp [packedDimsOf] at hl
  | cons pd rest ih =>
      have he' : ∀ ws : List (String × Nat),
          evalDims { dimTableStep env pd with widths := ws } ds = .ok es := by
        intro ws
        rw [dimTableStep_widths]
        exact he ws
      by_cases hn : n = pd.name
      · subst hn
        cases hty : pd.type
        case packed ds' r =>
          have hds : ds' = ds := by simpa [packedDimsOf, hty, List.lookup] using hl
          subst hds
          have h0 : evalDims env ds' = .ok es := he env.widths
          simp [dimTable, hty, h0]
        all_goals
          simp [packedDimsOf, hty] at hl
          simpa [dimTable, hty] using ih hl he'
      · have hb : (n == pd.name) = false := beq_false_of_ne hn
        cases hty : pd.type
        case packed ds' r =>
          simp [packedDimsOf, hty, List.lookup, hb] at hl
          cases hev : evalDims env ds' <;>
            simpa [dimTable, hty, hev, List.lookup, hb] using ih hl he'
        all_goals
          simp [packedDimsOf, hty] at hl
          simpa [dimTable, hty] using ih hl he'

/-- `dimTable_lookup_of` for a design's declarations, the dimension list
pinned by `PDesign.packedDims` (typically by `rfl` against the envelope). -/
theorem PDesign.dimTable_lookup_of {d : PDesign} {n : String} {ds : List PDim}
    {es : List (Int × Int)} (hl : d.packedDims.lookup n = some ds)
    (he : ∀ ws : List (String × Nat), evalDims { env with widths := ws } ds = .ok es) :
    (dimTable env d.decls).lookup n = some es :=
  LeanModels.Sv.dimTable_lookup_of hl he

@[simp] theorem walkIndices_nil (ds : List (Int × Int)) :
    walkIndices env ds [] = .ok (0, true, ds) := by
  simp [walkIndices]

/-- One element select: the label's offset scaled by the stride of the
remaining dimensions, and its own range check conjoined. -/
theorem walkIndices_cons_of {l r : Int} {ds : List (Int × Int)} {i : PExpr} {is : List PExpr}
    {k b : Int} {ok : Bool} {rest : List (Int × Int)}
    (hk : evalInt env i = .ok k) (hw : walkIndices env ds is = .ok (b, ok, rest)) :
    walkIndices env ((l, r) :: ds) (i :: is) =
      .ok (labelOffset l r k * (dimsStride ds : Int) + b,
        ok && decide (0 ≤ labelOffset l r k) && decide (labelOffset l r k < (dimCount l r : Int)),
        rest) := by
  simp [walkIndices, hk, hw]

/-- `walkIndices_cons_of` on a zero-based descending dimension `[m:0]`
with an in-range label `0 ≤ k ≤ m`: offset `k`, range check passes. -/
theorem walkIndices_desc0_cons {m : Int} {ds : List (Int × Int)} {i : PExpr} {is : List PExpr}
    {k b : Int} {ok : Bool} {rest : List (Int × Int)}
    (hm : 0 ≤ m) (hk : evalInt env i = .ok k) (hk0 : 0 ≤ k) (hkm : k ≤ m)
    (hw : walkIndices env ds is = .ok (b, ok, rest)) :
    walkIndices env ((m, 0) :: ds) (i :: is) = .ok (k * (dimsStride ds : Int) + b, ok, rest) := by
  rw [walkIndices_cons_of hk hw, labelOffset_desc0 hm]
  have hc := dimCount_desc0 hm
  have hlt : k < (dimCount m 0 : Int) := by omega
  simp [hk0, hlt]

theorem arrayElemWindow_of {n : String} {is : List PExpr} {es : List (Int × Int)} {b : Int}
    {ok : Bool} {rest : List (Int × Int)}
    (hd : arrayDims env n = .ok es) (hw : walkIndices env es is = .ok (b, ok, rest)) :
    arrayElemWindow env n is = .ok (b, dimsStride rest, ok) := by
  simp [arrayElemWindow, hd, hw]

/-- **A 2-D zero-based descending path `x[i][j]`** (dimensions evaluating to
`[am:0][bm:0]`) with in-range labels: the 1-bit window at `i*(bm+1) + j`. -/
theorem arrayElemWindow_desc0_2 {n : String} {am bm : Int} {ie je : PExpr}
    {i j : Int} (hd : env.dims.lookup n = some [(am, 0), (bm, 0)]) (ham : 0 ≤ am) (hbm : 0 ≤ bm)
    (hi : evalInt env ie = .ok i) (hi0 : 0 ≤ i) (hia : i ≤ am)
    (hj : evalInt env je = .ok j) (hj0 : 0 ≤ j) (hjb : j ≤ bm) :
    arrayElemWindow env n [ie, je] = .ok (i * (bm + 1) + j, 1, true) := by
  rw [arrayElemWindow_of (arrayDims_of hd)
    (walkIndices_desc0_cons ham hi hi0 hia
      (walkIndices_desc0_cons hbm hj hj0 hjb (walkIndices_nil (env := env) [])))]
  have hc := dimCount_desc0 hbm
  simp [dimsStride, hc]

/-- **In-range element select read**: the flat window of the declared
vector. -/
theorem arrayElemRead_of_inRange {n : String} {is : List PExpr} {lo : Int} {w : Nat}
    (h : arrayElemWindow env n is = .ok (lo, w, true)) :
    arrayElemRead env n is = .slice (.ident n) lo.toNat w := by
  simp [arrayElemRead, h]

/-- Out-of-range element select read: all-x (§7.4.6, per dimension). -/
theorem arrayElemRead_of_oob {n : String} {is : List PExpr} {lo : Int} {w : Nat}
    (h : arrayElemWindow env n is = .ok (lo, w, false)) :
    arrayElemRead env n is = .lit (LVec.xVec w) := by
  simp [arrayElemRead, h]

/-- **In-range element select target**: the flat window, the element width
as the RHS context. -/
theorem arrayElemTarget_of_inRange {n : String} {is : List PExpr} {lo : Int} {w : Nat}
    (h : arrayElemWindow env n is = .ok (lo, w, true)) :
    arrayElemTarget env n is = .ok (.slice n lo.toNat w, w) := by
  simp [arrayElemTarget, h]

/-- Out-of-range element select target: the zero-width (no-op) window. -/
theorem arrayElemTarget_of_oob {n : String} {is : List PExpr} {lo : Int} {w : Nat}
    (h : arrayElemWindow env n is = .ok (lo, w, false)) :
    arrayElemTarget env n is = .ok (.slice n 0 0, w) := by
  simp [arrayElemTarget, h]

@[simp] theorem instExpr2_arrayElem (ctx : Option Nat) (n : String) (is : List PExpr) :
    instExpr2 env elems ctx (.arrayElem n is) = arrayElemRead env n is := by
  simp [instExpr2]

/-- A constant part-select base is not a run-time one (`dynPartPlan`). -/
theorem dynPartPlan_of_evalInt {n : String} {is : List PExpr} {m : PartMode} {a b : PExpr}
    {k : Int} (ha : evalInt env a = .ok k) : dynPartPlan env n is m a b = none := by
  simp [dynPartPlan, ha]

/-- A part-select path whose static geometry computes is not a run-time one. -/
theorem dynPartPlan_of_geom {n : String} {is : List PExpr} {m : PartMode} {a b : PExpr}
    {g : Int × Bool × Nat × Nat × Int × Int} (h : arrayPartGeom env n is m a b = .ok g) :
    dynPartPlan env n is m a b = none := by
  cases ha : evalInt env a with
  | ok k => exact dynPartPlan_of_evalInt ha
  | error e =>
    exfalso
    have hp : partLabels env m a b = .error e := by simp [partLabels, ha]
    unfold arrayPartGeom at h
    cases hd : arrayDims env n with
    | error e' => simp [hd] at h
    | ok ds =>
      cases hw : walkIndices env ds is with
      | error e' => simp [hd, hw] at h
      | ok res =>
        obtain ⟨base, ok, rest⟩ := res
        cases rest with
        | nil => simp [hd, hw] at h
        | cons lr inner =>
          obtain ⟨l, r⟩ := lr
          simp [hd, hw, hp] at h

/-- A part-select path with a STATIC base reads through `arrayPartRead`
(`dynPartPlan_of_evalInt` / `dynPartPlan_of_geom` discharge `h`). -/
theorem instExpr2_arrayPart (ctx : Option Nat) {n : String} {is : List PExpr}
    {m : PartMode} {a b : PExpr} (h : dynPartPlan env n is m a b = none) :
    instExpr2 env elems ctx (.arrayPart n is m a b) = arrayPartRead env n is m a b := by
  simp [instExpr2, h]

/-- A part select with a RUN-TIME base (`v[sel +: 4]`) reads through
`dynBaseRead`, its base instantiated at its own self-determined width `bw`
(`dynPartRead` below 32 bits, `dynPartRead32` at 32, loud above). -/
theorem instExpr2_arrayPart_dyn (ctx : Option Nat) {n : String} {is : List PExpr}
    {m : PartMode} {a b : PExpr} {w q c bw : Nat}
    (h : dynPartPlan env n is m a b = some (.ok (w, q, c)))
    (hbw : selfWidth2 env elems a = some bw) :
    instExpr2 env elems ctx (.arrayPart n is m a b) =
      dynBaseRead n w q c bw (instExpr2 env elems (some bw) a) := by
  simp [instExpr2, h, hbw]

/-- A run-time base narrower than 32 bits is read unsigned (`dynPartRead`). -/
theorem dynBaseRead_lt32 {n : String} {w q c bw : Nat} {e : Expr2} (h : bw < 32) :
    dynBaseRead n w q c bw e = dynPartRead n w q c e := by
  simp [dynBaseRead, h]

/-- A run-time base of exactly 32 bits is read as a two's-complement `int`
(`dynPartRead32`). -/
@[simp] theorem dynBaseRead_32 {n : String} {w q c : Nat} {e : Expr2} :
    dynBaseRead n w q c 32 e = dynPartRead32 n w q c e := by
  simp [dynBaseRead]

@[simp] theorem instLhs2_arrayElem (n : String) (is : List PExpr) :
    instLhs2 env elems (.arrayElem n is) = arrayElemTarget env n is := by
  simp [instLhs2, instLhsLeaf2]

@[simp] theorem instLhs2_arrayPart (n : String) (is : List PExpr) (m : PartMode) (a b : PExpr) :
    instLhs2 env elems (.arrayPart n is m a b) = arrayPartTarget env n is m a b := by
  simp [instLhs2, instLhsLeaf2]

theorem selfWidth2_arrayElem_of {n : String} {is : List PExpr} {lo : Int} {w : Nat} {ok : Bool}
    (h : arrayElemWindow env n is = .ok (lo, w, ok)) :
    selfWidth2 env elems (.arrayElem n is) = some w := by
  simp [selfWidth2, arraySelWidth, h]

/-- An element-select path read at its own width: no resize. -/
theorem fitExpr2_arrayElem_of {n : String} {is : List PExpr} {lo : Int} {w : Nat} {ok : Bool}
    (h : arrayElemWindow env n is = .ok (lo, w, ok)) :
    fitExpr2 env elems (some w) (.arrayElem n is) = arrayElemRead env n is := by
  rw [fitExpr2_of_rigid_eq rfl (selfWidth2_arrayElem_of h), instExpr2_arrayElem]

/-- An element-select path read in a different-width context is resized. -/
theorem fitExpr2_arrayElem_resize {n : String} {is : List PExpr} {lo : Int} {w w' : Nat}
    {ok : Bool} (h : arrayElemWindow env n is = .ok (lo, w, ok)) (hne : w ≠ w') :
    fitExpr2 env elems (some w') (.arrayElem n is) = .resize w' (arrayElemRead env n is) := by
  rw [fitExpr2_of_rigid_ne rfl (selfWidth2_arrayElem_of h) hne rfl, instExpr2_arrayElem]

/-- A `[a:b]` part on the dimension after an element path whose msb label's
offset is at least its lsb label's. -/
theorem arrayPartGeom_range_of {n : String} {is : List PExpr} {a b : PExpr}
    {es : List (Int × Int)} {pb : Int} {ok : Bool} {l r : Int} {inner : List (Int × Int)}
    {k₁ k₂ : Int}
    (hd : arrayDims env n = .ok es) (hw : walkIndices env es is = .ok (pb, ok, (l, r) :: inner))
    (ha : evalInt env a = .ok k₁) (hb : evalInt env b = .ok k₂)
    (hdir : labelOffset l r k₂ ≤ labelOffset l r k₁) :
    arrayPartGeom env n is .range a b =
      .ok (pb, ok, dimsStride inner, dimCount l r, labelOffset l r k₂, labelOffset l r k₁) := by
  have hn : ¬ labelOffset l r k₁ < labelOffset l r k₂ := Int.not_lt.mpr hdir
  simp [arrayPartGeom, hd, hw, partLabels, ha, hb, hn, Int.min_def, Int.max_def]
  exact ⟨fun _ => by omega, fun _ => by omega⟩

/-- **In-range part-select read**: the flat window. -/
theorem arrayPartRead_of_inRange {n : String} {is : List PExpr} {m : PartMode} {a b : PExpr}
    {pb : Int} {s c : Nat} {lo hi : Int}
    (h : arrayPartGeom env n is m a b = .ok (pb, true, s, c, lo, hi))
    (hlo : 0 ≤ lo) (hhi : hi < (c : Int)) :
    arrayPartRead env n is m a b = .slice (.ident n) (pb + lo * s).toNat ((hi - lo + 1).toNat * s) := by
  simp [arrayPartRead, h, hlo, hhi]

/-- **In-range part-select target**: the flat window, its width the RHS
context. -/
theorem arrayPartTarget_of_inRange {n : String} {is : List PExpr} {m : PartMode} {a b : PExpr}
    {pb : Int} {s c : Nat} {lo hi : Int}
    (h : arrayPartGeom env n is m a b = .ok (pb, true, s, c, lo, hi))
    (hlo : 0 ≤ lo) (hhi : hi < (c : Int)) :
    arrayPartTarget env n is m a b =
      .ok (.slice n (pb + lo * s).toNat ((hi - lo + 1).toNat * s), (hi - lo + 1).toNat * s) := by
  simp [arrayPartTarget, h, hlo, hhi]

theorem selfWidth2_arrayPart_of {n : String} {is : List PExpr} {m : PartMode} {a b : PExpr}
    {pb : Int} {ok : Bool} {s c : Nat} {lo hi : Int}
    (h : arrayPartGeom env n is m a b = .ok (pb, ok, s, c, lo, hi)) :
    selfWidth2 env elems (.arrayPart n is m a b) = some ((hi - lo + 1).toNat * s) := by
  simp [selfWidth2, arraySelWidth, h]

/-- A part-select path read at its own width: no resize. -/
theorem fitExpr2_arrayPart_of {n : String} {is : List PExpr} {m : PartMode} {a b : PExpr}
    {pb : Int} {ok : Bool} {s c : Nat} {lo hi : Int}
    (h : arrayPartGeom env n is m a b = .ok (pb, ok, s, c, lo, hi)) :
    fitExpr2 env elems (some ((hi - lo + 1).toNat * s)) (.arrayPart n is m a b) =
      arrayPartRead env n is m a b := by
  rw [fitExpr2_of_rigid_eq rfl (selfWidth2_arrayPart_of h),
    instExpr2_arrayPart _ (dynPartPlan_of_geom h)]

/-! ### Indexed part-selects over a vector `[m:0]` at symbolic parameters

`x[b +: w]` and `x[b -: w]` (§11.5.1) on a 1-D zero-based descending
vector — the golf shape of a lane array, `y[i*W +: W]` over `[N*W-1:0]` —
for symbolic base `b` and width `w` (any `evalInt` facts: parameters,
genvars, their arithmetic). In range, a target is the flat `w`-bit window
at the select's lsb, and a read in a `w`-bit context is that window with no
resize (`fitExpr2_arrayPart_up_desc0`/`…_down_desc0`). -/

theorem arrayPartGeom_up_desc0 {n : String} {a b : PExpr} {mm k w : Int}
    (hd : arrayDims env n = .ok [(mm, 0)]) (hm : 0 ≤ mm)
    (ha : evalInt env a = .ok k) (hb : evalInt env b = .ok w) (hw : 0 < w) :
    arrayPartGeom env n [] .up a b = .ok (0, true, 1, dimCount mm 0, k, k + w - 1) := by
  have hmin : min (k + w - 1) k = k := Int.min_eq_right (by omega)
  have hmax : max (k + w - 1) k = k + w - 1 := Int.max_eq_left (by omega)
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  simp [arrayPartGeom, hd, partLabels, ha, hb, hw, labelOffset, hm, hmin, hmax,
    hmode]

theorem arrayPartGeom_down_desc0 {n : String} {a b : PExpr} {mm k w : Int}
    (hd : arrayDims env n = .ok [(mm, 0)]) (hm : 0 ≤ mm)
    (ha : evalInt env a = .ok k) (hb : evalInt env b = .ok w) (hw : 0 < w) :
    arrayPartGeom env n [] .down a b = .ok (0, true, 1, dimCount mm 0, k - w + 1, k) := by
  have hmin : min k (k - w + 1) = k - w + 1 := Int.min_eq_right (by omega)
  have hmax : max k (k - w + 1) = k := Int.max_eq_left (by omega)
  have hmode : (PartMode.down == PartMode.range) = false := rfl
  simp [arrayPartGeom, hd, partLabels, ha, hb, hw, labelOffset, hm, hmin, hmax,
    hmode]

/-- The in-range window of a 1-D part with geometry `(0, true, 1, c, lo, hi)`:
target. -/
private theorem arrayPartTarget_desc0_window {n : String} {m : PartMode} {a b : PExpr}
    {mm lo hi : Int} (hg : arrayPartGeom env n [] m a b = .ok (0, true, 1, dimCount mm 0, lo, hi))
    (hm : 0 ≤ mm) (hlo : 0 ≤ lo) (hhi : hi ≤ mm) :
    arrayPartTarget env n [] m a b = .ok (.slice n lo.toNat (hi - lo + 1).toNat,
      (hi - lo + 1).toNat) := by
  have hc : (dimCount mm 0 : Int) = mm + 1 := dimCount_desc0 hm
  have h0 : (0 : Int) + lo * ((1 : Nat) : Int) = lo := by omega
  simp only [arrayPartTarget, hg]
  rw [if_pos (by simp; omega), h0, Nat.mul_one]

/-- The in-range window of a 1-D part with geometry `(0, true, 1, c, lo, hi)`:
read. -/
private theorem arrayPartRead_desc0_window {n : String} {m : PartMode} {a b : PExpr}
    {mm lo hi : Int} (hg : arrayPartGeom env n [] m a b = .ok (0, true, 1, dimCount mm 0, lo, hi))
    (hm : 0 ≤ mm) (hlo : 0 ≤ lo) (hhi : hi ≤ mm) :
    arrayPartRead env n [] m a b = .slice (.ident n) lo.toNat (hi - lo + 1).toNat := by
  have hc : (dimCount mm 0 : Int) = mm + 1 := dimCount_desc0 hm
  have h0 : (0 : Int) + lo * ((1 : Nat) : Int) = lo := by omega
  simp only [arrayPartRead, hg]
  rw [if_pos (by simp; omega), h0, Nat.mul_one]

/-- **`x[b +: w]` target over `[m:0]`, in range** (`0 ≤ b`, `b + w ≤ m + 1`):
the `w`-bit window at `b`. -/
theorem arrayPartTarget_up_desc0 {n : String} {a b : PExpr} {mm k w : Int}
    (hd : arrayDims env n = .ok [(mm, 0)]) (hm : 0 ≤ mm)
    (ha : evalInt env a = .ok k) (hb : evalInt env b = .ok w) (hw : 0 < w)
    (hk : 0 ≤ k) (hkw : k + w ≤ mm + 1) :
    arrayPartTarget env n [] .up a b = .ok (.slice n k.toNat w.toNat, w.toNat) := by
  rw [arrayPartTarget_desc0_window (arrayPartGeom_up_desc0 hd hm ha hb hw) hm hk (by omega)]
  have hwid : k + w - 1 - k + 1 = w := by omega
  rw [hwid]

/-- **`x[b -: w]` target over `[m:0]`, in range** (`w - 1 ≤ b ≤ m`): the
`w`-bit window at `b - w + 1`. -/
theorem arrayPartTarget_down_desc0 {n : String} {a b : PExpr} {mm k w : Int}
    (hd : arrayDims env n = .ok [(mm, 0)]) (hm : 0 ≤ mm)
    (ha : evalInt env a = .ok k) (hb : evalInt env b = .ok w) (hw : 0 < w)
    (hk : w - 1 ≤ k) (hkm : k ≤ mm) :
    arrayPartTarget env n [] .down a b = .ok (.slice n (k - w + 1).toNat w.toNat, w.toNat) := by
  rw [arrayPartTarget_desc0_window (arrayPartGeom_down_desc0 hd hm ha hb hw) hm (by omega) hkm]
  have hwid : k - (k - w + 1) + 1 = w := by omega
  rw [hwid]

/-- **`x[b +: w]` read over `[m:0]`, in range**: the `w`-bit window at `b`. -/
theorem arrayPartRead_up_desc0 {n : String} {a b : PExpr} {mm k w : Int}
    (hd : arrayDims env n = .ok [(mm, 0)]) (hm : 0 ≤ mm)
    (ha : evalInt env a = .ok k) (hb : evalInt env b = .ok w) (hw : 0 < w)
    (hk : 0 ≤ k) (hkw : k + w ≤ mm + 1) :
    arrayPartRead env n [] .up a b = .slice (.ident n) k.toNat w.toNat := by
  rw [arrayPartRead_desc0_window (arrayPartGeom_up_desc0 hd hm ha hb hw) hm hk (by omega)]
  have hwid : k + w - 1 - k + 1 = w := by omega
  rw [hwid]

/-- **`x[b -: w]` read over `[m:0]`, in range**: the window at `b - w + 1`. -/
theorem arrayPartRead_down_desc0 {n : String} {a b : PExpr} {mm k w : Int}
    (hd : arrayDims env n = .ok [(mm, 0)]) (hm : 0 ≤ mm)
    (ha : evalInt env a = .ok k) (hb : evalInt env b = .ok w) (hw : 0 < w)
    (hk : w - 1 ≤ k) (hkm : k ≤ mm) :
    arrayPartRead env n [] .down a b = .slice (.ident n) (k - w + 1).toNat w.toNat := by
  rw [arrayPartRead_desc0_window (arrayPartGeom_down_desc0 hd hm ha hb hw) hm (by omega) hkm]
  have hwid : k - (k - w + 1) + 1 = w := by omega
  rw [hwid]

/-- `x[b +: w]` read in a `w`-bit context (an RHS feeding a `w`-bit
target): exactly the window, no resize. -/
theorem fitExpr2_arrayPart_up_desc0 {n : String} {a b : PExpr} {mm k w : Int}
    (hd : arrayDims env n = .ok [(mm, 0)]) (hm : 0 ≤ mm)
    (ha : evalInt env a = .ok k) (hb : evalInt env b = .ok w) (hw : 0 < w)
    (hk : 0 ≤ k) (hkw : k + w ≤ mm + 1) :
    fitExpr2 env elems (some w.toNat) (.arrayPart n [] .up a b) =
      .slice (.ident n) k.toNat w.toNat := by
  have hg := arrayPartGeom_up_desc0 hd hm ha hb hw
  have hwid : (k + w - 1 - k + 1).toNat * 1 = w.toNat := by omega
  have hs := selfWidth2_arrayPart_of (elems := elems) hg
  rw [hwid] at hs
  rw [fitExpr2_of_rigid_eq rfl hs, instExpr2_arrayPart _ (dynPartPlan_of_geom hg),
    arrayPartRead_up_desc0 hd hm ha hb hw hk hkw]

/-- `x[b -: w]` read in a `w`-bit context: the window, no resize. -/
theorem fitExpr2_arrayPart_down_desc0 {n : String} {a b : PExpr} {mm k w : Int}
    (hd : arrayDims env n = .ok [(mm, 0)]) (hm : 0 ≤ mm)
    (ha : evalInt env a = .ok k) (hb : evalInt env b = .ok w) (hw : 0 < w)
    (hk : w - 1 ≤ k) (hkm : k ≤ mm) :
    fitExpr2 env elems (some w.toNat) (.arrayPart n [] .down a b) =
      .slice (.ident n) (k - w + 1).toNat w.toNat := by
  have hg := arrayPartGeom_down_desc0 hd hm ha hb hw
  have hwid : (k - (k - w + 1) + 1).toNat * 1 = w.toNat := by omega
  have hs := selfWidth2_arrayPart_of (elems := elems) hg
  rw [hwid] at hs
  rw [fitExpr2_of_rigid_eq rfl hs, instExpr2_arrayPart _ (dynPartPlan_of_geom hg),
    arrayPartRead_down_desc0 hd hm ha hb hw hk hkm]

end arraySel

/-! ## `sv2_inst_simp` — the documented symbolic-instantiation recipe -/

open Lean Lean.Parser.Tactic in
/-- `sv2_inst_simp [facts] (at h)?` — compute `instProcess2` / `instLhs2` /
`fitExpr2` / `instExpr2` / `evalInt` on concrete process TEMPLATES whose
parameter and genvar values are SYMBOLIC integers: simp with the
instantiation equations, `List.lookup` by string key, `IEnv.bindVal`, and
`Except` stepping. Select sign checks over `Nat`-cast genvars (`0 ≤ ↑i + 1`,
`0 ≤ ↑i * ↑N + ↑j`) are discharged by `Gen2.int_add_nonneg`/`int_mul_nonneg`;
for `Int` genvars pass the nonnegativity fact (`0 ≤ v`) as an extra, and
pass arithmetic normalizers (`(↑i * 4).toNat = i * 4`, …) the same way.
Leaves `Int.toNat` of evaluated indices that simp's `Int.toNat_natCast`
family cannot fold. -/
macro (name := sv2InstSimpTactic) "sv2_inst_simp" "["
    args:(simpStar <|> simpErase <|> simpLemma),* "]" loc:(location)? : tactic => do
  let extra : Syntax.TSepArray
      [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
       `Lean.Parser.Tactic.simpLemma] "," := ⟨args.elemsAndSeps⟩
  `(tactic| set_option linter.unusedSimpArgs false in
      simp [instProcess2, instLhs2, instLhsLeaf2, fitExpr2, instExpr2, rigidExpr,
            selfWidth2, selfWidthSum2, elemOf, instParts2, evalInt, IEnv.bindVal,
            PExpr.isInt, SymBinOp.intArith,
            arraySelWidth, arrayElemRead, arrayPartRead, arrayElemTarget,
            arrayPartTarget, arrayElemWindow, arrayPartGeom, arrayDims, evalDims,
            dynPartPlan, dynBaseRead, arrayFlatWidth, partOffsetsWild, concatLeafExact,
            walkIndices, partLabels, labelOffset, dimCount, dimsStride,
            List.lookup, Gen2.except_ok_bind, Gen2.except_error_bind,
            Gen2.int_add_nonneg, Gen2.int_mul_nonneg, $extra,*] $(loc)?)

@[inherit_doc sv2InstSimpTactic]
macro "sv2_inst_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| sv2_inst_simp [] $(loc)?)

/-! ## Smoke: the probe shapes with a symbolic parameter and genvars

Environments are written the way `instantiate2` builds them: parameter
values in `vals` (genvars prepended by `IEnv.bindVal`), declared widths in
`widths`, element widths in `elems`. -/

section smoke

/-- A symbolic-width environment: `x` is `N*N` bits, `y` is `N` bits. -/
private def smokeEnv (N : Int) : IEnv :=
  { vals := [("N", N), ("W", 4)], widths := [("x", (N * N).toNat), ("y", N.toNat), ("o", 1)] }

private def smokeElems : List (String × Nat) := [("x", 1), ("y", 1), ("o", 1)]

/-- `x[i*N+j]` with symbolic `N` and genvars `i j`. -/
example (N i j : Int) (h : 0 ≤ i * N + j) :
    instExpr2 (((smokeEnv N).bindVal "i" i).bindVal "j" j) smokeElems (some 1)
      (.bitSel (.ident "x") (.binary (.m0 .add) (.binary .mul (.genvarRef "i")
        (.paramRef "N" none)) (.genvarRef "j"))) =
      .slice (.ident "x") (i * N + j).toNat 1 := by
  sv2_inst_simp [smokeEnv, smokeElems, h]

/-- `x[(i-1)*W+j+1]` (an affine genvar index with a parameter). -/
example (N i j : Int) (h : 0 ≤ (i - 1) * 4 + j + 1) :
    fitExpr2 (((smokeEnv N).bindVal "i" i).bindVal "j" j) smokeElems (some 1)
      (.bitSel (.ident "x") (.binary (.m0 .add) (.binary (.m0 .add)
        (.binary .mul (.binary (.m0 .sub) (.genvarRef "i") (.int 1)) (.paramRef "W" none))
        (.genvarRef "j")) (.int 1))) =
      .slice (.ident "x") ((i - 1) * 4 + j + 1).toNat 1 := by
  sv2_inst_simp [smokeEnv, smokeElems, h]

/-- A gate: `assign o = x[i] & y[j] | x[j] ^ y[i]` — no resize nodes. -/
example (N : Int) (i j : Nat) :
    instProcess2 (((smokeEnv N).bindVal "i" i).bindVal "j" j) smokeElems
      (.assign "o" (.binary (.m0 .or)
        (.binary (.m0 .and) (.bitSel (.ident "x") (.genvarRef "i"))
          (.bitSel (.ident "y") (.genvarRef "j")))
        (.binary (.m0 .xor) (.bitSel (.ident "x") (.genvarRef "j"))
          (.bitSel (.ident "y") (.genvarRef "i"))))) =
      .assign (.ident "o") (.binary .or
        (.binary .and (.slice (.ident "x") i 1) (.slice (.ident "y") j 1))
        (.binary .xor (.slice (.ident "x") j 1) (.slice (.ident "y") i 1))) := by
  sv2_inst_simp [smokeEnv, smokeElems]

/-- A constant part-select, a concat, and a literal into an `N`-bit
select target: the concat `{x[3:2], 2'b01}` is 4 bits wide, so in the
4-bit context of `y[i*4+3 : i*4]` it is NOT resized. -/
example (N : Int) (i : Nat) :
    instProcess2 ((smokeEnv N).bindVal "i" i) smokeElems
      (.assignL (.partSel "y" (.binary (.m0 .add) (.binary .mul (.genvarRef "i") (.int 4))
          (.int 3)) (.binary .mul (.genvarRef "i") (.int 4)))
        (.concat [.partSel (.ident "x") (.int 3) (.int 2), .lit (LVec.ofNat 2 1)])) =
      .assign (.slice "y" (i * 4) 4)
        (.concat #[.slice (.ident "x") 2 2, .lit (LVec.ofNat 2 1)]) := by
  have h3 : ((i : Int) * 4 + 3 - (i : Int) * 4) = 3 := by omega
  have h0 : (0 : Int) ≤ (i : Int) * 4 := by omega
  have hi : ((i : Int) * 4).toNat = i * 4 := by omega
  have hle : (i : Int) * 4 ≤ (i : Int) * 4 + 3 := by omega
  sv2_inst_simp [smokeEnv, smokeElems, LVec.width_ofNat, h3, h0, hi, hle]

/-- A 1-bit select in a wider context IS resized (the one inserted node). -/
example (N : Int) (i : Nat) :
    instProcess2 ((smokeEnv N).bindVal "i" i) smokeElems
      (.assignL (.partSel "y" (.int 3) (.int 0)) (.bitSel (.ident "x") (.genvarRef "i"))) =
      .assign (.slice "y" 0 4) (.resize 4 (.slice (.ident "x") i 1)) := by
  sv2_inst_simp [smokeEnv, smokeElems]

/-! Nested generate loops — the `N×N` partial-product array of a
gate-level multiplier, `for i < N: for j < N: p[i*N+j] = a[i] & b[j]` —
expand, for EVERY `N`, to the `i`-major family of 1-bit cells. -/

/-- The inner-loop template `assign p[i*N+j] = a[i] & b[j];`. -/
private def ppTmpl : PProcess :=
  .assignL (.bitSel "p" (.binary (.m0 .add) (.binary .mul (.genvarRef "i") (.paramRef "N" none))
      (.genvarRef "j")))
    (.binary (.m0 .and) (.bitSel (.ident "a") (.genvarRef "i"))
      (.bitSel (.ident "b") (.genvarRef "j")))

/-- `for (i = 0; i s< N; i++) for (j = 0; j s< N; j++) <ppTmpl>`. -/
private def ppGen : GenItem :=
  .genFor (some "gi") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
    (.unary .inc (.genvarRef "i")) none
    [.genFor (some "gj") "j" (.int 0) (.binary .slt (.genvarRef "j") (.paramRef "N" none))
      (.unary .inc (.genvarRef "j")) none ([ppTmpl].map GenItem.process)]

private def ppElems : List (String × Nat) := [("a", 1), ("b", 1), ("p", 1)]

/-- Cell `(i, j)`: `p[i*N+j] = a[i] & b[j]`. -/
private def ppProc (N i j : Nat) : Process2 :=
  .assign (.slice "p" (i * N + j) 1)
    (.binary .and (.slice (.ident "a") i 1) (.slice (.ident "b") j 1))

/-- The template at `Nat`-cast genvars, `N` read through the environment. -/
private theorem pp_inst (env : IEnv) (N i j : Nat) (hN : env.vals.lookup "N" = some (N : Int)) :
    instProcess2 ((env.bindVal "i" i).bindVal "j" j) ppElems ppTmpl = ppProc N i j := by
  have hidx : ((i : Int) * (N : Int) + (j : Int)).toNat = i * N + j := by
    rw [← Int.natCast_mul, ← Int.natCast_add, Int.toNat_natCast]
  sv2_inst_simp [ppElems, ppTmpl, ppProc, hN, hidx]

/-- The `N` lookup survives genvar bindings (genvars never shadow `N`). -/
private theorem pp_bound (env' : IEnv) (N : Nat) (h' : env'.vals.lookup "N" = some (N : Int))
    (g : String) (hg : g ≠ "N") (i : Int) :
    evalInt (env'.bindVal g i) (.paramRef "N" none) = .ok (N : Int) := by
  apply evalInt_paramRef_of
  simp [List.lookup, h', beq_false_of_ne (Ne.symm hg)]

/-- … and `N` stays in the INT class under them. -/
private theorem pp_bound_int (env' : IEnv) (N : Nat) (h' : env'.vals.lookup "N" = some (N : Int))
    (g : String) (hg : g ≠ "N") (i : Int) :
    (PExpr.paramRef "N" none).isInt (env'.bindVal g i) = true := by
  simp [PExpr.isInt, IEnv.bindVal, List.lookup, h', beq_false_of_ne (Ne.symm hg)]

example (env : IEnv) (N F : Nat) (hN : env.vals.lookup "N" = some (N : Int)) (hF : N < F) :
    ppGen.expand2 env ppElems F =
      .ok ((List.range N).flatMap fun i => (List.range N).map fun j => ppProc N i j) := by
  rw [ppGen, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => (intRange 0 N).flatMap fun w =>
        [ppTmpl].map (instProcess2 ((env.bindVal "i" v).bindVal "j" w) ppElems))
      (evalInt_int 0) (pp_bound_int env N hN "i" (by decide)) (pp_bound env N hN "i" (by decide))
      (by simpa using hF)]
  · simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast, List.map_cons,
      List.map_nil, pp_inst env N _ _ hN, Gen2.flatMap_singleton_map]
  · intro v _ _
    apply expandList2_singleton_ok
    rw [GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
      (pp_bound_int _ N (by simp [List.lookup, hN]) "j" (by decide))
      (pp_bound _ N (by simp [List.lookup, hN]) "j" (by decide)) (by simpa using hF)]
    simp

end smoke

end LeanModels.Sv
