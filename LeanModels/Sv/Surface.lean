import LeanModels.Sv.Obs

/-!
# The SV typed spec surface (`LeanModels.Sv`)

Theorems about SV designs should mention neither the AST, nor fuel, nor the
interpreter plumbing (`docs/sv-spec-surface.md`, the Python lane's
`docs/spec-surface.md` discipline). This file provides the M0 cycle-level
rendering of the gallery's judgment family:

* **`d ⊨ P`** — the all-schedule trace judgment: for every legal schedule σ,
  every stimulus, and every completed run, the property holds. The spine is
  **fuel-free**: it is built on `Runs` (`∃ fuel`, Obs.lean), and fuel
  monotonicity (`run_mono`) makes any single deciding fuel equivalent to all
  larger ones — `Models.of_run` consumes a ∀-fuel hypothesis-form fact, so
  every raw M0 theorem (`run … = .ok tr → …`) lifts in one step. `P` sees
  the design too (`TraceProp = Design → stimulus → trace → Prop`), which is
  what lets gallery-style property builders (`Sv.onPosedge`, which needs
  `initState d`) live inside `⊨` exactly as the gallery writes them;
  design-agnostic properties use the `Sv.spec` lift (`P stim tr`, the
  contract's plain form).
* **`d / stim ⇓[σ] tr`** — the gallery's run judgment at cycle level:
  notation for `Runs d σ stim tr`. `run_functional` (theorem 1 in surface
  form) and `Deterministic_iff` pin its determinism readings.
* **`Sv.Deterministic d`** — already fuel-free in Obs.lean; `Deterministic_iff`
  restates it in `⇓[σ]` notation (definitional).
* **`d ⊑@clk[from rst] model`** — cycle refinement against a Lean transition
  function, from the first sampled reset: from ANY trace snapshot that
  sampled `rst` true, the observed output column follows `model` iterated
  over the subsequently sampled resets, **whatever abstract state `s₀` is
  posited before the reset** (the ∀`s₀` inside `RefinesFromReset` is exactly
  "reset establishes the abstraction"; before the first reset the trace is
  all-x and no `BitVec` state corresponds — gallery example 2's point). The
  M0 form observes the design's (single) output port and takes `Bool` reset
  input per cycle; `clk` is recorded for notation fidelity only (M0's clock
  is implicit — every cycle IS a posedge).
* **`sv_prove [raw, bridges…]`** — first-cut tactic: closes surface-form
  goals from their raw (Proofs.lean-style) theorems — the Python lane's
  corollary pattern. See its docstring for the four goal shapes it handles
  and what it cannot do yet.
* **`#sv_check`** — concrete-run guards in surface syntax:
  `#sv_check counterD [[clk := 1, rst := 1], [rst := 0]] shows count = [0, 1]`.

**File-layout note (load-bearing):** this file deliberately imports only
`Obs.lean`, NOT `Proofs.lean`. `Tests.lean` must be able to import the
surface (for `#sv_check`), and importing `Proofs.lean` there would collide
with `Tests.lean`'s own private copies of the example designs/stimuli
(a same-file `private def` cannot coexist with an imported public name —
e.g. `raceStim`). The surface restatements of the four M0 theorems
(`swap_nba_swaps`, `counter_refines`, `race_blk_race`, …) therefore live in
`Delab.lean`, which imports both this file and `Proofs.lean` and also pins
how they print.
-/

namespace LeanModels.Sv

/-! ## Sampling and design helpers -/

/-- The value a snapshot *sampled* for `name`, as the `if`-condition boolean
the edge process saw that cycle (`condTrue`: has an `l1` bit). Signals are
only written by `applyInputs`/the edge phase before the snapshot, so the
trace carries exactly what the cycle's edge sampled — a stimulus entry that
omits `name` HOLDS the previous value, and the trace records that (which is
why refinement reads the trace, never the raw stimulus). `sampledRst`
(Proofs.lean) is definitionally `(sampled · "rst")`. -/
def sampled (s : SvState) (name : String) : Bool :=
  ((SvState.lookup s name).getD (LVec.xVec 1)).condTrue

/-- Declared width of a signal (0 if `name` is not declared — a `#sv_check`
on an undeclared name then fails loudly on the rendered-width mismatch). -/
def Design.widthOf (d : Design) (name : String) : Nat :=
  match d.decls.find? (fun dc => dc.name == name) with
  | some dc => dc.width
  | none => 0

/-- The design's first (in M0: only) output port name — what
`⊑@clk[from rst]` observes. `pp_nodot` keeps the delaborated form
`Design.firstOutput d`, which the `⊑@` unexpander (Delab.lean) recognizes. -/
@[pp_nodot] def Design.firstOutput (d : Design) : String :=
  (d.outputNames)[0]?.getD ""

/-! ## The all-schedule trace judgment `d ⊨ P` -/

/-- A cycle-level trace property: sees the design (so property builders can
mention `initState d`), the stimulus, and the trace (one snapshot per
stimulus entry). Design-agnostic properties are lifted with `spec`. -/
abbrev TraceProp := Design → List SvState → List SvState → Prop

/-- `d ⊨ P` — for **every** legal schedule, every stimulus, and every
completed run, the trace satisfies `P`. Fuel-free by construction: the run
hypothesis is `Runs` (`∃ fuel`, with fuel monotonicity making the witness
irrelevant). Introduce from a raw ∀-fuel fact with `Models.of_run`;
eliminate against a concrete run with `Models.run`. -/
def Models (d : Design) (P : TraceProp) : Prop :=
  ∀ (σ : ScheduleOracle) (stim tr : List SvState), Runs d σ stim tr → P d stim tr

@[inherit_doc] scoped infix:50 " ⊨ " => Models

/-- Introduction rule — exactly the shape of the raw M0 theorems
(`run d σ fuel stim = .ok tr → …`), so every hypothesis-form Proofs.lean
theorem lifts to `⊨` in one step. -/
theorem Models.of_run {d : Design} {P : TraceProp}
    (h : ∀ (σ : ScheduleOracle) (fuel : Nat) (stim tr : List SvState),
      run d σ fuel stim = .ok tr → P d stim tr) : d ⊨ P :=
  fun σ stim tr hr => hr.elim fun fuel hrun => h σ fuel stim tr hrun

/-- Elimination against a concrete interpreter run (any fuel). -/
theorem Models.run {d : Design} {P : TraceProp} (h : d ⊨ P)
    {σ : ScheduleOracle} {fuel : Nat} {stim tr : List SvState}
    (hrun : run d σ fuel stim = .ok tr) : P d stim tr :=
  h σ stim tr ⟨fuel, hrun⟩

/-- Monotonicity: weaken the property pointwise. -/
theorem Models.imp {d : Design} {P Q : TraceProp}
    (hPQ : ∀ stim tr, P d stim tr → Q d stim tr) (h : d ⊨ P) : d ⊨ Q :=
  fun σ stim tr hr => hPQ stim tr (h σ stim tr hr)

/-- Lift a design-agnostic stimulus/trace predicate into `⊨` — the
contract's plain `P stim tr` form (`d ⊨ spec fun stim tr => …`). -/
def spec (P : List SvState → List SvState → Prop) : TraceProp :=
  fun _d stim tr => P stim tr

/-- Every adjacent snapshot pair of `states` satisfies `R` (indexed form —
the shape the raw theorems already use, so no list-recursion bridging is
needed). -/
def Stepwise (R : SvState → SvState → Prop) (states : List SvState) : Prop :=
  ∀ (i : Nat) (s s' : SvState), states[i]? = some s → states[i + 1]? = some s' → R s s'

/-- Gallery `Sv.onPosedge` at M0 cycle level: every posedge step — from each
state to the next cycle's snapshot, the pre-edge startup state `initState d`
included — satisfies the two-state relation `R`. (`s` = state the edge read,
`s'` = snapshot after that edge's NBA commit.) -/
def onPosedge (R : SvState → SvState → Prop) : TraceProp :=
  fun d _stim tr => Stepwise R (initState d :: tr)

/-! ## The run judgment `d / stim ⇓[σ] tr` -/

/-- `d / stim ⇓[σ] tr` — design `d` under stimulus `stim` and schedule `σ`
yields trace `tr` (`docs/sv-spec-surface.md`'s `m / stim ⇓[σ] tr` at cycle
level): notation for `Runs d σ stim tr`, i.e. some fuel completes the run —
and then, by fuel monotonicity, every larger fuel agrees. -/
syntax:50 term:max " / " term:max " ⇓[" term "] " term:51 : term

macro_rules
  | `($d / $stim ⇓[$σ] $tr) => `(Runs $d $σ $stim $tr)

/-- **M0 theorem 1 in surface form**: at fixed schedule the run judgment is
functional — fuel does not exist on the surface, so this is the honest
"`run` is deterministic" statement (`Runs.functional`/`run_det` underneath;
the contract's pinned `run_deterministic : run … = run …` stays in
Proofs.lean). -/
theorem run_functional {d : Design} {σ : ScheduleOracle} {stim tr₁ tr₂ : List SvState}
    (h₁ : d / stim ⇓[σ] tr₁) (h₂ : d / stim ⇓[σ] tr₂) : tr₁ = tr₂ :=
  Runs.functional h₁ h₂

/-- `Sv.Deterministic` (Obs.lean) in `⇓[σ]` notation — definitional, pinned
so the surface reading is on record: all legal schedules agree on the trace. -/
theorem Deterministic_iff {d : Design} :
    Deterministic d ↔
      ∀ (σ₁ σ₂ : ScheduleOracle) (stim tr₁ tr₂ : List SvState),
        (d / stim ⇓[σ₁] tr₁) → (d / stim ⇓[σ₂] tr₂) → tr₁ = tr₂ :=
  Iff.rfl

/-! ## Cycle refinement from reset: `d ⊑@clk[from rst] model` -/

/-- Iterate a golden-model transition function over a list of sampled reset
inputs, emitting one state per cycle (`counterModelRun` in Proofs.lean is
`modelRun counterModel` — bridged in Delab.lean). -/
def modelRun {w : Nat} (model : BitVec w → Bool → BitVec w) :
    BitVec w → List Bool → List (BitVec w)
  | _, [] => []
  | s, r :: rs => model s r :: modelRun model (model s r) rs

set_option linter.unusedVariables false in
/-- The cycle-refinement-from-reset judgment (gallery `⊑@clk[from rst]`, M0
form): on every completed run, from ANY snapshot `i` that sampled `rst`
true, the `out` column equals `model` iterated over the sampled resets of
cycles `i, i+1, …` — starting from **every** abstract state `s₀`. The ∀`s₀`
is the `[from rst]` content: since cycle `i` sampled reset, the iteration's
head is `model s₀ true`, so the statement forces the reset to erase the
abstract state (and before the first reset nothing is claimed — the trace is
all-x there and no `BitVec w` state corresponds, gallery example 2). `clk`
is recorded for notation fidelity only: M0's clock is implicit (every cycle
is a posedge of the single clock). Prove it with
`RefinesFromReset.of_reset_column` (or `sv_prove`) from a raw
`counter_from_reset`-shaped column theorem. -/
def RefinesFromReset (d : Design) (clk rst out : String) {w : Nat}
    (model : BitVec w → Bool → BitVec w) : Prop :=
  ∀ (σ : ScheduleOracle) (stim tr : List SvState), Runs d σ stim tr →
    ∀ (i : Nat) (s : SvState), tr[i]? = some s → sampled s rst = true →
      ∀ s₀ : BitVec w,
        (tr.drop i).map (fun s' => SvState.lookup s' out) =
          (modelRun model s₀ ((tr.drop i).map (fun s' => sampled s' rst))).map
            (fun b => some (LVec.ofBitVec b))

/-- `d ⊑@clk[from rst] model` — gallery notation for `RefinesFromReset`,
observing the design's (single, in M0) output port: expands to
`RefinesFromReset d "clk" "rst" (Design.firstOutput d) model`. The clock and
reset appear as bare identifiers, exactly as in
`counter ⊑@clk[from rst] counterModel`. -/
syntax:50 term:max " ⊑@" ident "[" "from" ident "] " term:51 : term

open Lean in
macro_rules
  | `($d ⊑@$clk:ident[from $rst:ident] $model) => do
      let clkS := Syntax.mkStrLit clk.getId.eraseMacroScopes.toString
      let rstS := Syntax.mkStrLit rst.getId.eraseMacroScopes.toString
      `(RefinesFromReset $d $clkS $rstS (Design.firstOutput $d) $model)

/-- **The refinement introduction rule**: a raw reset-column theorem (the
exact `counter_from_reset` shape — `run` hypothesis, snapshot `i` sampling
reset, column = `r0 ::` model iterates from `r0`) yields the judgment,
provided the model's reset is state-independent (`hreset` — `r0` is "the"
reset state; for `counterModel` it is `0` and `hreset` is `fun _ => rfl`).
The ∀`s₀` of the judgment is discharged here once and for all: snapshot `i`
sampled reset, so the iteration's head collapses to `r0` by `hreset`. -/
theorem RefinesFromReset.of_reset_column {d : Design} {clk rst out : String}
    {w : Nat} {model : BitVec w → Bool → BitVec w} (r0 : BitVec w)
    (hreset : ∀ s, model s true = r0)
    (h : ∀ (σ : ScheduleOracle) (fuel : Nat) (stim tr : List SvState),
        run d σ fuel stim = .ok tr →
        ∀ (i : Nat) (s : SvState), tr[i]? = some s → sampled s rst = true →
          (tr.drop i).map (fun s' => SvState.lookup s' out) =
            (r0 :: modelRun model r0 ((tr.drop (i + 1)).map (fun s' => sampled s' rst))).map
              (fun b => some (LVec.ofBitVec b))) :
    RefinesFromReset d clk rst out model := by
  intro σ stim tr hruns i s hi hr s₀
  obtain ⟨fuel, hrun⟩ := hruns
  have hcol := h σ fuel stim tr hrun i s hi hr
  obtain ⟨hlt, hs⟩ := List.getElem?_eq_some_iff.mp hi
  have hdrop : tr.drop i = s :: tr.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hlt, hs]
  rw [hdrop] at hcol ⊢
  simp only [List.map_cons, hr, modelRun, hreset s₀]
  simpa using hcol

/-! ## `sv_prove` — the surface front door (first cut) -/

open Lean Lean.Parser.Tactic in
/-- `sv_prove [raw, bridges…]` — close a surface-form goal from its raw
(Proofs.lean-style) theorem `raw`, the Python lane's `py_corollary` pattern.
Handles four goal shapes, in attempt order:

1. **plain restatements** (`⇓[σ]`/∃-witness/¬`Deterministic` forms that are
   the raw proposition verbatim or an instance of it) — `exact raw` /
   `apply raw <;> assumption`;
2. **`Deterministic d`** from a canonical-totality lemma
   `raw : ∀ σ stim, Runs d σ stim (canonicalTrace …)`
   (e.g. `sv_prove [swap_nba_total]`) — both runs are rewritten to the
   canonical trace by `Runs.functional`;
3. **`d ⊨ P`** from a hypothesis-form raw theorem
   `raw : (σ) → run d σ fuel stim = .ok tr → …` (e.g.
   `sv_prove [swap_nba_spec]`): opens the run with `Models.of_run`, intros
   through the property builders (`spec`/`onPosedge`/`Stepwise` unfold by
   whnf), then instantiates `raw`; a `simpa [bridges…]` fallback normalizes
   value-form mismatches;
4. **`d ⊑@clk[from rst] model`** from a raw reset-column theorem (the
   `counter_from_reset` shape) via `RefinesFromReset.of_reset_column`, with
   the model's reset-state independence discharged by `rfl` and the
   `bridges` simp set aligning the raw statement with the judgment (e.g.
   `sv_prove [counter_from_reset, sampledRst_eq, counterModelRun_eq,
   counter_firstOutput]` — the bridges live in Delab.lean).

Not yet handled (documented gaps): direct symbolic execution of a new
design (the per-design cycle lemmas still use the Proofs.lean script —
threshold intro + `combSettle_nil` + `sv_simp` + `choose_singleton`/
`choose_pair`); `Sv.comb`-style combinational judgments (no M0 theorems need
them yet); models whose reset state is not definitionally state-independent
(use `RefinesFromReset.of_reset_column` directly with a proved `hreset`). -/
macro (name := svProveTactic) "sv_prove" "[" tot:term ","
    args:(simpStar <|> simpErase <|> simpLemma),* "]" : tactic => do
  let extra : Syntax.TSepArray
      [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
       `Lean.Parser.Tactic.simpLemma] "," := ⟨args.elemsAndSeps⟩
  `(tactic|
    (intros
     first
       | exact $tot
       | (apply $tot <;> assumption)
       | (intro σ₁ σ₂ stim tr₁ tr₂ h₁ h₂
          rw [Runs.functional h₁ ($tot σ₁ stim), Runs.functional h₂ ($tot σ₂ stim)])
       | (refine Models.of_run fun σ fuel stim tr hrun => ?_
          intros
          first
            | (apply $tot <;> assumption)
            | (set_option linter.unusedSimpArgs false in
               simpa [$extra,*] using $tot σ hrun ‹_› ‹_›))
       | (refine RefinesFromReset.of_reset_column _ (fun _ => rfl) ?_
          intro σ fuel stim tr hrun i s hi hr
          set_option linter.unusedSimpArgs false in
          simpa [$extra,*] using $tot σ hrun hi hr)))

@[inherit_doc svProveTactic]
macro "sv_prove" "[" tot:term "]" : tactic => `(tactic| sv_prove [$tot,])

/-! ## `#sv_check` — concrete-run guards in surface syntax

```
#sv_check <design> [<cycle>, <cycle>, …] (under <σ>)? shows <sig> = [<val>, …], …
```

* `<design>` — a `Design` constant (identifier).
* `<cycle>` — one stimulus entry: `[name := val, …]` drives the listed
  **input ports** for that cycle (non-inputs are ignored by `applyInputs`,
  and an input absent from the entry holds its previous value); `[]` is a
  hold cycle.
* `<val>` — a `Nat` literal (rendered at the signal's declared width), a
  `%b` string literal with `x`/`z` digits (MSB first, e.g. `"0000z01x"`),
  bare `x` (all-x at declared width), or bare `z` (all-z).
* `under σ` — optional schedule (default `σ_src`, the Xcelium order).
* `shows` — one or more expected signal columns, one value per cycle,
  compared against the run's `%b` snapshots (`SvState.showSignal`).

The command expands to one `#guard svCheck …` at fixed generous fuel 4096
(the Python `#py_check` convention: fuel is existential in every judgment,
so a minimal fuel documents nothing — and concrete runs cost time
proportional to actual work, not to fuel). A run that does not complete
(`.timeout`/`.unsupported`), a wrong column, or an undeclared signal name
all fail the guard (and hence the file). -/

/-- A surface-syntax stimulus/expectation value (see the section comment). -/
inductive SvVal where
  /-- A `Nat`, read/rendered at the signal's declared width (mod 2^w). -/
  | nat (n : Nat)
  /-- A `%b` string with `0`/`1`/`x`/`z` digits, MSB first (width = length). -/
  | bits (s : String)
  /-- All-x at the signal's declared width. -/
  | allx
  /-- All-z at the signal's declared width. -/
  | allz
deriving Repr, BEq, Inhabited

/-- The `LVec` a stimulus value drives onto `name` (widths from `d`). -/
def SvVal.toLVec (d : Design) (name : String) : SvVal → LVec
  | .nat n => .ofNat (d.widthOf name) n
  | .bits s => .lit s
  | .allx => .xVec (d.widthOf name)
  | .allz => .replicate (d.widthOf name) .lz

/-- The `%b` string an expected value renders to (what the trace column is
compared against). -/
def SvVal.render (d : Design) (name : String) : SvVal → String
  | .nat n => (LVec.ofNat (d.widthOf name) n).toBinString
  | .bits s => (LVec.lit s).toBinString
  | .allx => (LVec.xVec (d.widthOf name)).toBinString
  | .allz => (LVec.replicate (d.widthOf name) .lz).toBinString

/-- Build the stimulus (one `SvState` per cycle) from surface values. -/
def svStim (d : Design) (cycles : List (List (String × SvVal))) : List SvState :=
  cycles.map fun c => c.map fun (n, v) => (n, v.toLVec d n)

/-- The `#sv_check` runtime: run at fuel 4096 under `σ` and compare every
requested `%b` column. `false` unless the run is `.ok` and all columns
match. -/
def svCheck (d : Design) (σ : ScheduleOracle) (cycles : List (List (String × SvVal)))
    (cols : List (String × List SvVal)) : Bool :=
  match run d σ 4096 (svStim d cycles) with
  | .ok tr => cols.all fun (name, expected) =>
      tr.map (fun st => SvState.showSignal st name) == expected.map (SvVal.render d name)
  | _ => false

declare_syntax_cat sv_val
/-- `Nat` stimulus/expectation value (declared-width binary). -/
syntax num : sv_val
/-- `%b` string stimulus/expectation value (may contain `x`/`z`). -/
syntax str : sv_val
/-- `x` (all-x) / `z` (all-z) stimulus/expectation value. -/
syntax ident : sv_val

declare_syntax_cat sv_bind
/-- One driven input: `name := val`. -/
syntax ident " := " sv_val : sv_bind

declare_syntax_cat sv_cycle
/-- One stimulus cycle: `[name := val, …]` (empty = hold). -/
syntax "[" sv_bind,* "]" : sv_cycle

declare_syntax_cat sv_col
/-- One expected column: `sig = [val, …]`. -/
syntax ident " = " "[" sv_val,* "]" : sv_col

@[inherit_doc svCheck]
syntax (name := svCheckCmd) "#sv_check " ident " [" sv_cycle,* "]"
  (&"under" term:max)? &"shows" sv_col,+ : command

open Lean in
private def svValTerm : TSyntax `sv_val → MacroM Term
  | `(sv_val| $n:num) => `(SvVal.nat $n)
  | `(sv_val| $s:str) => `(SvVal.bits $s)
  | `(sv_val| $i:ident) =>
      match i.getId.eraseMacroScopes with
      | .str .anonymous "x" => `(SvVal.allx)
      | .str .anonymous "z" => `(SvVal.allz)
      | _ => Macro.throwErrorAt i "expected a numeral, a %b string literal, `x`, or `z`"
  | _ => Macro.throwUnsupported

open Lean in
private def svBindTerm : TSyntax `sv_bind → MacroM Term
  | `(sv_bind| $name:ident := $v:sv_val) => do
      let nS := Syntax.mkStrLit name.getId.eraseMacroScopes.toString
      let vT ← svValTerm v
      `(($nS, $vT))
  | _ => Macro.throwUnsupported

open Lean in
private def svCycleTerm : TSyntax `sv_cycle → MacroM Term
  | `(sv_cycle| [$bs,*]) => do
      let ts ← bs.getElems.mapM svBindTerm
      `([$ts,*])
  | _ => Macro.throwUnsupported

open Lean in
private def svColTerm : TSyntax `sv_col → MacroM Term
  | `(sv_col| $name:ident = [$vs,*]) => do
      let nS := Syntax.mkStrLit name.getId.eraseMacroScopes.toString
      let ts ← vs.getElems.mapM svValTerm
      `(($nS, [$ts,*]))
  | _ => Macro.throwUnsupported

macro_rules
  | `(#sv_check $d:ident [$cs,*] shows $cols,*) => do
      let cyc ← cs.getElems.mapM svCycleTerm
      let colTs ← cols.getElems.mapM svColTerm
      `(#guard svCheck $d σ_src [$cyc,*] [$colTs,*])
  | `(#sv_check $d:ident [$cs,*] under $σ:term shows $cols,*) => do
      let cyc ← cs.getElems.mapM svCycleTerm
      let colTs ← cols.getElems.mapM svColTerm
      `(#guard svCheck $d $σ [$cyc,*] [$colTs,*])

/-! ### `#sv_check` smoke tests (Proofs-independent; the gallery-design
demos live in `Tests.lean`) -/

/-- A pass-through wire, for in-file `#sv_check` regressions. -/
private def svPassD : Design :=
  { name := "pass"
    decls := #[
      { name := "a", width := 8, isInput := true },
      { name := "y", width := 8, isOutput := true }]
    processes := #[.assign "y" (.ident "a")] }

#sv_check svPassD [[a := 5], [a := 0xAA], []] shows y = [5, "10101010", "10101010"]
#sv_check svPassD [[]] shows y = [x]
#sv_check svPassD [[a := "0000z01x"]] under σ_rev shows y = ["0000z01x"], a = ["0000z01x"]

-- The judgment layer is exercised end-to-end in Delab.lean (surface forms of
-- the four M0 theorems); a design-generic smoke here:
example (d : Design) : d ⊨ spec fun _ _ => True := by
  sv_prove [trivial]

end LeanModels.Sv
