import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2
import LeanModels.Sv.Comb2Base

/-!
# Proof handles for the hierarchical instantiation (`Hier2.lean`)

The `Gen2.lean` discipline, extended to `PDesign.instantiateH`: the walk
`GenItem.expandH` / `expandListH` / `expandItersH` is well-founded and is
never unfolded by hand — its interface is the per-constructor equations
below (`expandListH_cons_ok`, `GenItem.expandH_inst`,
`GenItem.expandH_genFor_of`, `expandItersH_eq_flatMap`, and the canonical
ascending loop `GenItem.expandH_genFor_ascending_flatMap`), the instance
step `instExpandH_of` (prefix + child design ↦ `flattenInst`), and the
decomposition `PDesign.instantiateRec_of_ok` (the `instantiate2_of_ok`
twin: parameter environment, declarations, element widths, the walk, the
assembled design `PDesign.assembleH`).

**Conservative extension.** On a design with no module instance the
hierarchical instantiation IS the flat one: `PDesign.instantiateRec_flat`,
`PDesign.instantiateH_flat`, `PDesign.instantiateHD2_flat`.

**The one-driver rule** (`Hier2.lean`, "Drivers"): `PDesign.instantiateH_of_rec`
peels the top's guard given `driversOk` on the result;
`driversOk_of_continuous` reduces `driversOk` of a continuous-only process
list to pairwise disjointness of its windows (`drvWinsDisjoint_iff`) and
their avoiding the input ports — the procedural clauses (the §6.5 mixture,
the §9.2.2.2/§9.2.2.4 `always_comb`/`always_ff` exclusivity) hold
vacuously there (`procWins_nil_of_procWrites`,
`procExclusiveOk_of_procWins_nil`) — and `driverWins_cons`/`_append`/
`_flatMap` compute the windows of a symbolic family. For a list WITH
procedural processes, `driversOk_iff` states the rule clause by clause
(`procExclusiveOk_iff`: pairwise over the processes; a process without
procedural windows clashes with nothing,
`Process2.exclClash_of_procWins_nil_left`/`_right`).

**The flat top's one-driver rule** (2026-10-28, WP2): `name.sem` of a
single-module envelope is `PDesign.instantiateGD2` — `instantiateD2` under
`PDesign.driverGuard` at every parameter point. A proof about `name.sem`
removes the guard with ONE of two recipes, both ending in
`PDesign.instantiateGD2_of_ok` (`name.sem args = m` for the instantiated
design `m`):

* **from the comb profile** — `PDesign.instantiateGD2_of_combDesign`: the
  instantiation `d.instantiate2 args (PDesign.surfaceFuel args) = .ok m`
  (the `Gen2.lean` recipe, `PDesign.instantiate2_of_ok`), `CombDesign m`
  (the settle theorem's own hypothesis — prove it about `m`, then transport
  it to `name.sem` along the equation), and positive write windows. The
  bridge is `driversOk_of_combDesign`: `CombDesign`'s `disjoint`,
  `selfDisjoint` and `notInput` fields ARE the one-driver rule on its
  windows (`DrvWin.MatchList`: a `Lhs2.drvWins` window is the comb
  window of the same leaf, a whole-signal one its full declared width).
* **from the process list** — `driversOk_of_continuous` over the list the
  instantiation theorem computes: `driverWins_cons`/`_append`/`_map`/
  `_flatMap` compute its windows for symbolic parameters,
  `pairwise_flatMap_range` splits a generate family's windows into one
  cell's and two cells' (`j < k`), and `DrvWin.overlaps_some_eq_false`
  turns each pair into bit arithmetic for `omega` (row-major offsets
  `i * K + c`: `rowMajor_le`). `ripple_add/gen.lean` and `mul2d/gen.lean`
  use this route; `ripple_fa/gen.lean` uses it for a hierarchical top.

The structural acceptance (`ripple_fa`, a ripple-carry adder of
`full_adder` instances in a generate loop, flattened at symbolic `N`) lives
in `Examples/system-verilog/ripple_fa/gen.lean`.
-/

namespace LeanModels.Sv

attribute [local simp] Gen2.except_ok_bind Gen2.except_error_bind

section walk

variable {cb : ChildInst} {env : IEnv} {elems : List (String × Nat)} {F : Nat}

@[simp] theorem expandListH_nil : expandListH cb env elems F [] = .ok ([], []) := by
  rw [expandListH]

/-- An instance-free item list expands exactly as the flat walk, with no
hoisted declarations. -/
theorem expandListH_of_instFree {l : List GenItem} (h : GenItem.listInstFree l = true) :
    expandListH cb env elems F l = (expandList2 env elems F l >>= fun ps => .ok ([], ps)) := by
  cases l with
  | nil => simp
  | cons it rest => rw [expandListH, if_pos h]

/-- A list holding an instance: item by item. -/
theorem expandListH_cons_ok {it : GenItem} {rest : List GenItem}
    {ds ds' : List Decl} {ps qs : List Process2}
    (h : GenItem.listInstFree (it :: rest) = false)
    (h1 : it.expandH cb env elems F = .ok (ds, ps))
    (h2 : expandListH cb env elems F rest = .ok (ds', qs)) :
    expandListH cb env elems F (it :: rest) = .ok (ds ++ ds', ps ++ qs) := by
  rw [expandListH, if_neg (by simp [h]), h1]
  simp only [Res.ok_bind, h2]

/-- A one-item list holding an instance is that item's expansion. -/
theorem expandListH_singleton_ok {it : GenItem} {ds : List Decl} {ps : List Process2}
    (h : it.instFree = false) (h1 : it.expandH cb env elems F = .ok (ds, ps)) :
    expandListH cb env elems F [it] = .ok (ds, ps) := by
  have := expandListH_cons_ok (rest := []) (by simp [GenItem.listInstFree, h]) h1 expandListH_nil
  simpa using this

@[simp] theorem GenItem.expandH_inst (i : PInst) :
    (GenItem.inst i).expandH cb env elems F = instExpandH cb env elems i := by
  rw [GenItem.expandH]

@[simp] theorem GenItem.expandH_process (p : PProcess) :
    (GenItem.process p).expandH cb env elems F = .ok ([], [instProcess2 env elems p]) := by
  rw [GenItem.expandH]

/-- A decided generate-for header: the body iterated over the genvar
sequence. -/
theorem GenItem.expandH_genFor_of {label : Option String} {g : String}
    {initE bound step : PExpr} {rc : Option Nat} {body : List GenItem}
    {i0 δ : Int} {vs : List Int}
    (hi : evalInt env initE = .ok i0) (hs : stepDelta g step = .ok δ)
    (hv : genvarSeq env g bound δ F i0 = .ok vs) :
    (GenItem.genFor label g initE bound step rc body).expandH cb env elems F =
      expandItersH cb env elems F g vs body := by
  rw [GenItem.expandH, hi, hs]
  simp [hv]

@[simp] theorem expandItersH_nil (g : String) (body : List GenItem) :
    expandItersH cb env elems F g [] body = .ok ([], []) := by
  rw [expandItersH]

/-- **The family lemma**: a generate-for body whose expansion at every
genvar value is known expands to the concatenations over the sequence. -/
theorem expandItersH_eq_flatMap {g : String} {body : List GenItem}
    {f : Int → List Decl × List Process2} :
    ∀ {vs : List Int},
      (∀ v ∈ vs, expandListH cb (env.bindVal g v) elems F body = .ok (f v)) →
      expandItersH cb env elems F g vs body =
        .ok (vs.flatMap fun v => (f v).1, vs.flatMap fun v => (f v).2)
  | [], _ => by simp
  | v :: vs, hf => by
      rw [expandItersH, hf v (by simp)]
      simp only [Res.ok_bind]
      rw [expandItersH_eq_flatMap (vs := vs) (fun w hw => hf w (by simp [hw]))]
      simp

/-- **The canonical ascending generate-for over a body with instances**
(`for (g = i0; g s< e; g++)`, loop-invariant `e ⇓ N`, enough fuel): the
per-value expansions concatenated over `intRange i0 (N - i0).toNat`. -/
theorem GenItem.expandH_genFor_ascending_flatMap {label : Option String} {g : String}
    {initE e : PExpr} {rc : Option Nat} {body : List GenItem} {i0 N : Int}
    {f : Int → List Decl × List Process2}
    (hi : evalInt env initE = .ok i0)
    (hei : ∀ i : Int, e.isInt (env.bindVal g i) = true)
    (he : ∀ i : Int, evalInt (env.bindVal g i) e = .ok N)
    (hF : (N - i0).toNat < F)
    (hf : ∀ v : Int, i0 ≤ v → v < N →
      expandListH cb (env.bindVal g v) elems F body = .ok (f v)) :
    (GenItem.genFor label g initE (.binary .slt (.genvarRef g) e)
        (.unary .inc (.genvarRef g)) rc body).expandH cb env elems F =
      .ok ((intRange i0 (N - i0).toNat).flatMap fun v => (f v).1,
           (intRange i0 (N - i0).toNat).flatMap fun v => (f v).2) := by
  rw [GenItem.expandH_genFor_of hi (stepDelta_inc g) (genvarSeq_ascending hei he i0 hF)]
  apply expandItersH_eq_flatMap
  intro v hv
  rw [mem_intRange] at hv
  exact hf v hv.1 (by omega)

/-- **One instance**: at a decided prefix, with the child's flattened
design `c`, the instance expands to `flattenInst`. -/
theorem instExpandH_of {i : PInst} {pfx : String} {c : Design2}
    (hp : i.prefix env = .ok pfx) (hc : cb env i = .ok c) :
    instExpandH cb env elems i = .ok (flattenInst env elems pfx i c) := by
  simp [instExpandH, hp, hc]

end walk

/-! ## The `instantiateRec` decomposition -/

/-- The `Design2` assembled by `instantiateRec`: the parent's declarations,
then the hoisted ones; the instantiated static processes, then the walk's,
then the out-of-tier members as loud processes. -/
def PDesign.assembleH (d : PDesign) (env : IEnv) (decls idecls : List Decl)
    (elems : List (String × Nat)) (gens : List Process2) : Design2 :=
  { name := d.name
    decls := (decls ++ idecls).toArray
    processes :=
      ((d.processes.map (instProcess2 (env.withDecls decls) elems)) ++ gens
        ++ d.others.map fun kt => Process2.unsupported kt.1 kt.2).toArray }

@[simp] theorem PDesign.assembleH_processes (d : PDesign) (env : IEnv)
    (decls idecls : List Decl) (elems : List (String × Nat)) (gens : List Process2) :
    (d.assembleH env decls idecls elems gens).processes.toList =
      d.processes.map (instProcess2 (env.withDecls decls) elems) ++ gens
        ++ d.others.map fun kt => Process2.unsupported kt.1 kt.2 := by
  simp [PDesign.assembleH]

@[simp] theorem PDesign.assembleH_decls (d : PDesign) (env : IEnv)
    (decls idecls : List Decl) (elems : List (String × Nat)) (gens : List Process2) :
    (d.assembleH env decls idecls elems gens).decls.toList = decls ++ idecls := by
  simp [PDesign.assembleH]

/-- The child instantiator `instantiateRec (depth + 1)` walks with, under
the clock-source rule for the instantiating module's input ports `clocks`
(`Decl.inputNames` of its declarations). -/
abbrev PDesign.childRec (depth : Nat) (lib : List PDesign) (envI : IEnv) (F : Nat)
    (clocks : List String) : ChildInst :=
  childInstOf (fun c cargs => PDesign.instantiateRec depth lib envI c cargs F) lib clocks

/-- **`instantiateRec` decomposed** (the `instantiate2_of_ok` twin):
decided stages assemble the flattened design. -/
theorem PDesign.instantiateRec_of_ok {depth : Nat} {lib : List PDesign} {envI : IEnv}
    {d : PDesign} {args : List Int} {F : Nat} {env : IEnv} {decls idecls : List Decl}
    {elems : List (String × Nat)} {gens : List Process2}
    (harity : args.length = d.params.length)
    (h1 : d.paramEnvH envI args = .ok env)
    (h2 : buildDecls env d.decls = .ok decls)
    (h3 : buildElems env d.decls = .ok elems)
    (h4 : expandListH (PDesign.childRec depth lib envI F (Decl.inputNames decls))
            (env.withDecls decls) elems F d.generates = .ok (idecls, gens)) :
    PDesign.instantiateRec (depth + 1) lib envI d args F =
      .ok (d.assembleH env decls idecls elems gens) := by
  have hne : (args.length != d.params.length) = false := by simp [harity]
  rw [PDesign.instantiateRec]
  simp only [hne, Bool.false_eq_true, if_false, h1, Res.ok_bind, h2, h3]
  rw [h4]
  rfl

/-- **Conservative extension**: on a design whose generate items hold no
instance, the hierarchical instantiation is `instantiate2From` — for any
library, depth and initial environment. -/
theorem PDesign.instantiateRec_flat (depth : Nat) (lib : List PDesign) (envI : IEnv)
    (d : PDesign) (args : List Int) (F : Nat) (h : GenItem.listInstFree d.generates = true) :
    PDesign.instantiateRec (depth + 1) lib envI d args F = d.instantiate2From envI args F := by
  rw [PDesign.instantiateRec, PDesign.instantiate2From]
  split
  · rfl
  · simp only [PDesign.paramEnvH, Gen2.res_bind_assoc, Res.ok_bind, expandListH_of_instFree h,
      List.append_nil]
    rfl

/-- `instantiateH` on an instance-free design is `instantiate2` (the top's
one-driver rule, `PDesign.topGuard`, is the identity there). -/
theorem PDesign.instantiateH_flat (d : PDesign) (lib : List PDesign) (args : List Int) (F : Nat)
    (h : GenItem.listInstFree d.generates = true) :
    d.instantiateH lib args F = d.instantiate2 args F := by
  have hrec := PDesign.instantiateRec_flat lib.length lib {} d args F h
  simp only [PDesign.instantiateH, PDesign.instantiateHFrom, PDesign.topGuard, h, if_true, hrec]
  show (d.instantiate2From {} args F >>= fun m => Res.ok m) = d.instantiate2From {} args F
  cases d.instantiate2From {} args F <;> rfl

/-! ## The one-driver rule (`driversOk`) -/

/-- `drvWinsDisjoint` is pairwise non-overlap. -/
theorem drvWinsDisjoint_iff {l : List DrvWin} :
    drvWinsDisjoint l = true ↔ l.Pairwise (fun a b => a.overlaps b = false) := by
  induction l with
  | nil => simp [drvWinsDisjoint]
  | cons w ws ih => simp [drvWinsDisjoint, List.pairwise_cons, ih, List.all_eq_true]

@[simp] theorem driverWins_nil (names : List String) : driverWins names [] = [] := rfl

@[simp] theorem driverWins_cons (names : List String) (p : Process2) (ps : List Process2) :
    driverWins names (p :: ps) =
      p.drvWins.filter (fun w => names.contains w.1) ++ driverWins names ps := by
  simp [driverWins]

@[simp] theorem driverWins_append (names : List String) (ps qs : List Process2) :
    driverWins names (ps ++ qs) = driverWins names ps ++ driverWins names qs := by
  simp [driverWins, List.flatMap_append]

theorem driverWins_flatMap {α : Type} (names : List String) (l : List α)
    (f : α → List Process2) :
    driverWins names (l.flatMap f) = l.flatMap fun a => driverWins names (f a) := by
  simp [driverWins, List.flatMap_assoc]

/-- `procExclusiveOk` is pairwise: no two processes of the list
(`p` before `q`) clash (`Process2.exclClash`). -/
theorem procExclusiveOk_iff {names : List String} {ps : List Process2} :
    procExclusiveOk names ps = true ↔ ps.Pairwise (fun p q => p.exclClash names q = false) := by
  induction ps with
  | nil => simp [procExclusiveOk]
  | cons p ps ih => simp [procExclusiveOk, List.pairwise_cons, ih, List.all_eq_true]

/-- A process with no procedural windows — a continuous `assign`, a loud
process, a procedure writing nothing — clashes with nothing … -/
@[simp] theorem Process2.exclClash_of_procWins_nil_left {names : List String}
    {p : Process2} (h : p.procWins = []) (q : Process2) : p.exclClash names q = false := by
  simp [Process2.exclClash, Process2.procWinsOn, h]

/-- … from either side. -/
@[simp] theorem Process2.exclClash_of_procWins_nil_right {names : List String}
    (p : Process2) {q : Process2} (h : q.procWins = []) : p.exclClash names q = false := by
  simp [Process2.exclClash, Process2.procWinsOn, h]

/-- A continuous assignment has no procedural windows. -/
@[simp] theorem Process2.procWins_assign (t : Lhs2) (e : Expr2) :
    (Process2.assign t e).procWins = [] := rfl

/-- `procWrites` are the signals of `procWins`. -/
theorem Process2.procWrites_eq (p : Process2) : p.procWrites = p.procWins.map (·.1) := rfl

/-- No procedural write means no procedural window, process by process. -/
theorem procWins_nil_of_procWrites {ps : List Process2}
    (hpw : ps.flatMap Process2.procWrites = []) : ∀ p ∈ ps, p.procWins = [] := by
  intro p hp
  have h := List.flatMap_eq_nil_iff.mp hpw p hp
  rwa [Process2.procWrites_eq, List.map_eq_nil_iff] at h

/-- **The one-driver rule, clause by clause** (`driversOk`'s docstring):
the continuous windows are pairwise disjoint; each avoids the input ports
and every procedural window (§6.5); no procedural process writes an input
port; and no two processes break the `always_comb`/`always_ff`
exclusivity (§9.2.2.2/§9.2.2.4). The general constructor for a design
WITH procedural processes: compute `driverWins` (`driverWins_cons`/…) and
`Process2.procWins` (`simp [Process2.procWins, Stmt2.drvWins, …]`), split
the pairwise clauses of a generate family with `pairwise_flatMap_range`,
and close each window pair with `DrvWin.overlaps_some_eq_false` + `omega`. -/
theorem driversOk_iff {names inputs : List String} {ps : List Process2} :
    driversOk names inputs ps = true ↔
      (driverWins names ps).Pairwise (fun a b => a.overlaps b = false) ∧
      (∀ w ∈ driverWins names ps, inputs.contains w.1 = false ∧
        ∀ v ∈ ps.flatMap Process2.procWins, w.overlaps v = false) ∧
      (∀ n ∈ ps.flatMap Process2.procWrites, inputs.contains n = false) ∧
      ps.Pairwise (fun p q => p.exclClash names q = false) := by
  simp only [driversOk, Bool.and_eq_true, drvWinsDisjoint_iff, procExclusiveOk_iff,
    List.all_eq_true, Bool.not_eq_true', and_assoc]

/-- The exclusivity clause holds vacuously when no process has a
procedural window. -/
theorem procExclusiveOk_of_procWins_nil {names : List String} {ps : List Process2}
    (h : ∀ p ∈ ps, p.procWins = []) : procExclusiveOk names ps = true := by
  rw [procExclusiveOk_iff]
  induction ps with
  | nil => exact List.Pairwise.nil
  | cons p ps ih =>
    refine List.pairwise_cons.mpr ⟨fun q _ => ?_, ih fun q hq => h q (List.mem_cons.mpr (Or.inr hq))⟩
    exact Process2.exclClash_of_procWins_nil_left (h p (List.mem_cons.mpr (Or.inl rfl))) q

/-- **The one-driver rule for continuous-only processes**: no procedural
writes, pairwise disjoint windows on the module's signals, none of them an
input port. (The procedural clauses — the §6.5 mixture, the §9.2.2.2/
§9.2.2.4 exclusivity — hold vacuously: no process has a procedural
window, `procWins_nil_of_procWrites`.) -/
theorem driversOk_of_continuous {names inputs : List String} {ps : List Process2}
    (hpw : ps.flatMap Process2.procWrites = [])
    (hdis : (driverWins names ps).Pairwise (fun a b => a.overlaps b = false))
    (hin : ∀ w ∈ driverWins names ps, inputs.contains w.1 = false) :
    driversOk names inputs ps = true := by
  have hnil := procWins_nil_of_procWrites hpw
  have hvs : ps.flatMap Process2.procWins = [] := List.flatMap_eq_nil_iff.mpr hnil
  rw [driversOk_iff]
  refine ⟨hdis, fun w hw => ⟨hin w hw, by simp [hvs]⟩, by simp [hpw], ?_⟩
  exact procExclusiveOk_iff.mp (procExclusiveOk_of_procWins_nil hnil)

/-- A design passing the one-driver rule is its own guard. -/
theorem Design2.driverGuard_of_ok {names inputs : List String} {m : Design2}
    (h : driversOk names inputs m.processes.toList = true) :
    m.driverGuard names inputs = m := by
  simp [Design2.driverGuard, h]

/-- **`instantiateH` decomposed**: the recursive instantiation, and the
top's one-driver rule passing on its result (vacuous for an instance-free
top). -/
theorem PDesign.instantiateH_of_rec {d : PDesign} {lib : List PDesign} {args : List Int}
    {F : Nat} {m : Design2}
    (h : PDesign.instantiateRec (lib.length + 1) lib {} d args F = .ok m)
    (hok : driversOk d.declNames d.inputNames m.processes.toList = true) :
    d.instantiateH lib args F = .ok m := by
  simp only [PDesign.instantiateH, PDesign.instantiateHFrom, h, Res.ok_bind, PDesign.topGuard,
    PDesign.driverGuard, Design2.driverGuard_of_ok hok, ite_self]

/-- The total hierarchical family on an instance-free design is the flat
total family. -/
theorem PDesign.instantiateHD2_flat (d : PDesign) (lib : List PDesign) (args : List Int)
    (h : GenItem.listInstFree d.generates = true) :
    d.instantiateHD2 lib args = d.instantiateD2 args := by
  simp only [PDesign.instantiateHD2, PDesign.instantiateD2, PDesign.instantiateH_flat d lib _ _ h]
  cases d.instantiate2 args (PDesign.surfaceFuel args) <;> rfl

/-- The total family agrees with a successful hierarchical instantiation at
the surface fuel. -/
theorem PDesign.instantiateHD2_of_ok {d : PDesign} {lib : List PDesign} {args : List Int}
    {m : Design2} (h : d.instantiateH lib args (PDesign.surfaceFuel args) = .ok m) :
    d.instantiateHD2 lib args = m := by
  simp [PDesign.instantiateHD2, h]

/-! ## The flat top's one-driver rule (`instantiateG2`, WP2) -/

/-- The loud error design passes the one-driver rule (its one process is
loud, not a driver). -/
@[simp] theorem Design2.errorDesign_driverGuard (n msg : String) (names inputs : List String) :
    (Design2.errorDesign n msg).driverGuard names inputs = .errorDesign n msg := by
  simp [Design2.driverGuard, driversOk, driverWins, Design2.errorDesign, Process2.drvWins,
    Process2.procWrites, Process2.procWins, drvWinsDisjoint, procExclusiveOk]

/-- **`instantiateG2` without its guard**: an instantiation whose process
list passes the one-driver rule. -/
theorem PDesign.instantiateG2_of_ok {d : PDesign} {args : List Int} {F : Nat} {m : Design2}
    (h : d.instantiate2 args F = .ok m)
    (hok : driversOk d.declNames d.inputNames m.processes.toList = true) :
    d.instantiateG2 args F = .ok m := by
  simp only [PDesign.instantiateG2, h, Res.ok_bind, PDesign.driverGuard,
    Design2.driverGuard_of_ok hok]

/-- **`name.sem` of a flat envelope without its guard** — the last step of
either recipe (module docstring): the successful instantiation at the
surface fuel and the one-driver rule on its process list give
`d.instantiateGD2 args = m`, i.e. `name.sem P₁ … Pₙ = m`. -/
theorem PDesign.instantiateGD2_of_ok {d : PDesign} {args : List Int} {m : Design2}
    (h : d.instantiate2 args (PDesign.surfaceFuel args) = .ok m)
    (hok : driversOk d.declNames d.inputNames m.processes.toList = true) :
    d.instantiateGD2 args = m := by
  simp only [PDesign.instantiateGD2, PDesign.instantiateG2_of_ok h hok]

/-- The guarded family is the guard of the total family, at every point
(the loud error design passes the rule). -/
theorem PDesign.instantiateGD2_eq_driverGuard (d : PDesign) (args : List Int) :
    d.instantiateGD2 args = d.driverGuard (d.instantiateD2 args) := by
  unfold PDesign.instantiateGD2 PDesign.instantiateG2 PDesign.instantiateD2
  cases d.instantiate2 args (PDesign.surfaceFuel args) <;>
    simp [PDesign.driverGuard, Design2.errorDesign_driverGuard] <;> rfl

/-- The guarded family is the total family wherever the rule holds on it. -/
theorem PDesign.instantiateGD2_of_driversOk {d : PDesign} {args : List Int}
    (hok : driversOk d.declNames d.inputNames (d.instantiateD2 args).processes.toList = true) :
    d.instantiateGD2 args = d.instantiateD2 args := by
  rw [PDesign.instantiateGD2_eq_driverGuard, PDesign.driverGuard, Design2.driverGuard_of_ok hok]

/-! ### Computing a symbolic family's windows -/

@[simp] theorem driverWins_map {α : Type} (names : List String) (l : List α)
    (f : α → Process2) :
    driverWins names (l.map f) = l.flatMap fun a => driverWins names [f a] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.map_cons, List.flatMap_cons, driverWins_cons, ih]

/-- `DrvWin.overlaps` of two bit windows (the `Win.overlaps` formula). -/
@[simp] theorem DrvWin.overlaps_some (n n' : String) (l₁ w₁ l₂ w₂ : Nat) :
    DrvWin.overlaps (n, some (l₁, w₁)) (n', some (l₂, w₂)) =
      (n == n' && (decide (l₁ < l₂ + w₂) && decide (l₂ < l₁ + w₁))) := rfl

/-- Two bit windows are disjoint: other signals, or disjoint bit ranges —
the form `omega` closes. -/
theorem DrvWin.overlaps_some_eq_false {n n' : String} {l₁ w₁ l₂ w₂ : Nat} :
    DrvWin.overlaps (n, some (l₁, w₁)) (n', some (l₂, w₂)) = false ↔
      n ≠ n' ∨ l₂ + w₂ ≤ l₁ ∨ l₁ + w₁ ≤ l₂ := by
  rw [DrvWin.overlaps_some]
  by_cases h : n = n'
  · subst h
    simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_false_iff, decide_eq_false_iff_not,
      ne_eq, not_true_eq_false, false_or]
    omega
  · simp [h]

/-- A whole-signal window overlaps every window of its signal. -/
@[simp] theorem DrvWin.overlaps_none_left (n : String) (b : DrvWin) :
    DrvWin.overlaps (n, none) b = (n == b.1) := by
  obtain ⟨n', o⟩ := b
  cases o <;> simp [DrvWin.overlaps]

/-- … from either side. -/
@[simp] theorem DrvWin.overlaps_none_right (a : DrvWin) (n : String) :
    DrvWin.overlaps a (n, none) = (a.1 == n) := by
  obtain ⟨n', o⟩ := a
  rcases o with _ | ⟨l, w⟩ <;> simp [DrvWin.overlaps]

/-- **A generate family's windows are pairwise disjoint** when every
cell's windows are, and every two cells `j < k` are disjoint from each
other — `List.pairwise_flatMap` over `List.range`, the shape a
`for (i = 0; i < N; i++)` expansion has (`GenItem.expand2_genFor_ascending_*`
yields `(List.range N).flatMap …`). -/
theorem pairwise_flatMap_range {α : Type} {R : α → α → Prop} {N : Nat} {f : Nat → List α}
    (hself : ∀ k, k < N → (f k).Pairwise R)
    (hcross : ∀ j k, j < k → k < N → ∀ a ∈ f j, ∀ b ∈ f k, R a b) :
    ((List.range N).flatMap f).Pairwise R := by
  rw [List.pairwise_flatMap]
  refine ⟨fun k hk => hself k (List.mem_range.mp hk), ?_⟩
  exact List.Pairwise.imp_of_mem (fun _ hb hlt => hcross _ _ hlt (List.mem_range.mp hb))
    List.pairwise_lt_range

/-- Row-major offsets `i * K + c` (`c < K`): row `i` ends where row `i' > i`
can begin. `omega` treats `i * K` as an atom; this is the fact relating two
of them (a 2-D packed array's cells, `mul2d/gen.lean`). -/
theorem rowMajor_le {K i i' : Nat} (h : i < i') : i * K + K ≤ i' * K := by
  have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt h)
  rwa [Nat.succ_mul] at this

/-! ### The one-driver rule from the comb profile -/

/-- A `Lhs2.drvWins` window and the `Comb2Base` window (`Lhs2.windows?`) of
the same target leaf: the same signal, and the same bits — or, for a
whole-signal `DrvWin`, the signal's full declared width from bit `0`. -/
def DrvWin.Matches (d : Design2) (x : DrvWin) (a : Win) : Prop :=
  x.1 = a.1 ∧
    (x.2 = some (a.2.1, a.2.2) ∨ (x.2 = none ∧ a.2.1 = 0 ∧ d.declWidth a.1 = some a.2.2))

/-- Positionwise `DrvWin.Matches` of a driver-window list and a
comb-window list (equal lengths). -/
def DrvWin.MatchList (d : Design2) : List DrvWin → List Win → Prop
  | [], [] => True
  | x :: xs, a :: as => DrvWin.Matches d x a ∧ DrvWin.MatchList d xs as
  | _, _ => False

theorem DrvWin.MatchList.append {d : Design2} :
    ∀ {xs : List DrvWin} {as : List Win} {ys : List DrvWin} {bs : List Win},
      DrvWin.MatchList d xs as → DrvWin.MatchList d ys bs →
      DrvWin.MatchList d (xs ++ ys) (as ++ bs)
  | [], [], _, _, _, h => by simpa using h
  | _ :: _, _ :: _, _, _, h, h' => ⟨h.1, DrvWin.MatchList.append h.2 h'⟩
  | [], _ :: _, _, _, h, _ => by simp [DrvWin.MatchList] at h
  | _ :: _, [], _, _, h, _ => by simp [DrvWin.MatchList] at h

theorem DrvWin.MatchList.exists_mem {d : Design2} :
    ∀ {xs : List DrvWin} {as : List Win}, DrvWin.MatchList d xs as →
      ∀ x ∈ xs, ∃ a ∈ as, DrvWin.Matches d x a
  | [], _, _, x, hx => by simp at hx
  | _ :: _, [], h, _, _ => by simp [DrvWin.MatchList] at h
  | x :: xs, a :: as, h, y, hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨a, List.mem_cons.mpr (Or.inl rfl), h.1⟩
      · obtain ⟨b, hb, hm⟩ := DrvWin.MatchList.exists_mem h.2 y hy
        exact ⟨b, List.mem_cons_of_mem _ hb, hm⟩

theorem DrvWin.MatchList.pairwise {d : Design2} {P : Win → Win → Prop}
    {Q : DrvWin → DrvWin → Prop} :
    ∀ {xs : List DrvWin} {as : List Win}, DrvWin.MatchList d xs as → as.Pairwise P →
      (∀ x a y b, a ∈ as → b ∈ as → DrvWin.Matches d x a → DrvWin.Matches d y b →
        P a b → Q x y) →
      xs.Pairwise Q
  | [], _, _, _, _ => List.Pairwise.nil
  | _ :: _, [], h, _, _ => by simp [DrvWin.MatchList] at h
  | x :: xs, a :: as, h, hp, hq => by
      rw [List.pairwise_cons] at hp ⊢
      refine ⟨fun y hy => ?_, DrvWin.MatchList.pairwise h.2 hp.2
        fun x' a' y' b' ha hb => hq x' a' y' b' (List.mem_cons_of_mem _ ha)
          (List.mem_cons_of_mem _ hb)⟩
      obtain ⟨b, hb, hm⟩ := DrvWin.MatchList.exists_mem h.2 y hy
      exact hq x a y b (List.mem_cons.mpr (Or.inl rfl)) (List.mem_cons_of_mem _ hb) h.1 hm
        (hp.1 b hb)

mutual
/-- **A target's driver windows are its comb windows**, leaf by leaf, in
order: a slice and a literal-index element select give the same bits, a
whole-signal target `(n, none)` its full declared width. -/
theorem Lhs2.drvWins_matchList {d : Design2} : ∀ (t : Lhs2) (ws : List Win),
    t.windows? d = some ws → DrvWin.MatchList d t.drvWins ws
  | .ident n, ws, h => by
      rw [Lhs2.windows?_ident] at h
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨⟨rfl, Or.inr ⟨rfl, rfl, hw⟩⟩, trivial⟩
  | .slice n lo w, ws, h => by
      rw [Lhs2.windows?_slice, Option.some.injEq] at h
      subst h
      simp [Lhs2.drvWins, DrvWin.MatchList, DrvWin.Matches]
  | .index n idx ew, ws, h => by
      cases idx
      case lit c =>
        rw [Lhs2.windows?_index_lit] at h
        obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
        simp [Lhs2.drvWins, Lhs2.indexWin?, hk, DrvWin.MatchList, DrvWin.Matches]
      all_goals simp [Lhs2.windows?, Lhs2.window?] at h
  | .concat ps, ws, h => by
      rw [Lhs2.windows?_concat] at h
      rw [Lhs2.drvWins]
      exact Lhs2.drvWinsList_matchList ps ws h
termination_by structural t => t

/-- `Lhs2.drvWins_matchList` over a concatenation's parts. -/
theorem Lhs2.drvWinsList_matchList {d : Design2} : ∀ (ps : List Lhs2) (ws : List Win),
    Lhs2.listWindows? d ps = some ws → DrvWin.MatchList d (Lhs2.drvWinsList ps) ws
  | [], ws, h => by
      rw [Lhs2.listWindows?_nil, Option.some.injEq] at h
      subst h
      simp [Lhs2.drvWinsList, DrvWin.MatchList]
  | t :: ts, ws, h => by
      obtain ⟨a, b, ha, hb, rfl⟩ := Lhs2.listWindows?_cons_eq_some.mp h
      rw [Lhs2.drvWinsList]
      exact DrvWin.MatchList.append (Lhs2.drvWins_matchList t a ha)
        (Lhs2.drvWinsList_matchList ts b hb)
termination_by structural ps => ps
end

/-- **Disjoint comb windows give disjoint driver windows** when both are
positive and in range — the whole-signal case is where that is needed:
`(n, none)` overlaps every window of `n`, and so does the comb window
`(n, 0, w)` of every POSITIVE window inside `[0, w)`. -/
theorem DrvWin.overlaps_eq_false_of_matches {d : Design2} {x y : DrvWin} {a b : Win}
    (hx : DrvWin.Matches d x a) (hy : DrvWin.Matches d y b)
    (ha : 0 < a.2.2) (hb : 0 < b.2.2)
    (hia : ∃ dw, d.declWidth a.1 = some dw ∧ a.2.1 + a.2.2 ≤ dw)
    (hib : ∃ dw, d.declWidth b.1 = some dw ∧ b.2.1 + b.2.2 ≤ dw)
    (h : Win.overlaps a b = false) : DrvWin.overlaps x y = false := by
  obtain ⟨n, lo, w⟩ := a
  obtain ⟨n', lo', w'⟩ := b
  obtain ⟨xn, xo⟩ := x
  obtain ⟨yn, yo⟩ := y
  obtain ⟨hxn, hxo⟩ := hx
  obtain ⟨hyn, hyo⟩ := hy
  obtain ⟨dw, hdw, hlw⟩ := hia
  obtain ⟨dw', hdw', hlw'⟩ := hib
  simp only at hxn hyn hxo hyo ha hb hdw hdw' hlw hlw'
  subst hxn hyn
  rw [Win.overlaps_eq_false] at h
  rcases hxo with hxo | ⟨hxo, hlo, hxw⟩ <;> rcases hyo with hyo | ⟨hyo, hlo', hyw⟩ <;>
    subst hxo hyo
  · rw [DrvWin.overlaps_some_eq_false]
    exact h
  · subst hlo'
    rw [DrvWin.overlaps_none_right, beq_eq_false_iff_ne]
    rintro rfl
    have : dw = w' := Option.some.inj (hdw.symm.trans hyw)
    simp only [ne_eq, not_true_eq_false, false_or] at h
    omega
  · subst hlo
    rw [DrvWin.overlaps_none_left, beq_eq_false_iff_ne]
    rintro rfl
    have : dw' = w := Option.some.inj (hdw'.symm.trans hxw)
    simp only [ne_eq, not_true_eq_false, false_or] at h
    omega
  · subst hlo hlo'
    rw [DrvWin.overlaps_none_left, beq_eq_false_iff_ne]
    rintro rfl
    simp only [ne_eq, not_true_eq_false, false_or] at h
    omega

/-- **The one-driver rule from the comb profile.** A `CombDesign` whose
write windows are all positive passes `driversOk` at any signal list
`names` and any list `inputs` of its input ports: its processes are all
continuous (`assign`), `CombDesign.disjoint` (distinct processes) and
`selfDisjoint` (one concatenation target) are the rule's pairwise
disjointness on the comb windows, and `notInput` its input clause
(`DrvWin.MatchList` carries each to the driver windows). With
`PDesign.instantiate2_inputNames` this is
`PDesign.instantiateGD2_of_combDesign`. -/
theorem driversOk_of_combDesign {m : Design2} {names inputs : List String}
    (hc : CombDesign m) (hpos : ∀ i n lo w, m.Writes i (n, lo, w) → 0 < w)
    (hin : ∀ n ∈ inputs, n ∈ m.inputNames.toList) :
    driversOk names inputs m.processes.toList = true := by
  -- Process `i` of the list is process `i` of the design.
  have hget : ∀ (i : Nat) (hi : i < m.processes.toList.length),
      m.processes[i]? = some m.processes.toList[i] := by
    intro i hi
    rw [← Array.getElem?_toList]
    exact List.getElem?_eq_getElem hi
  -- Each process is an assign whose driver windows match its comb windows.
  have hproc : ∀ (i : Nat) (hi : i < m.processes.toList.length), ∃ t e ws,
      m.processes.toList[i] = .assign t e ∧ m.processes[i]? = some (.assign t e) ∧
        t.windows? m = some ws ∧ t.wins m = ws ∧ DrvWin.MatchList m t.drvWins ws := by
    intro i hi
    obtain ⟨t, e, ws, hp, hw⟩ := hc.assign i _ (hget i hi)
    exact ⟨t, e, ws, hp, hp ▸ hget i hi, hw, Lhs2.wins_of_windows? hw,
      Lhs2.drvWins_matchList t ws hw⟩
  -- Facts about one comb window of process `i`.
  have hwin : ∀ (i : Nat) (t : Lhs2) (e : Expr2) (a : Win),
      m.processes[i]? = some (.assign t e) → a ∈ t.wins m →
        m.Writes i a ∧ 0 < a.2.2 ∧ ∃ dw, m.declWidth a.1 = some dw ∧ a.2.1 + a.2.2 ≤ dw := by
    intro i t e a hp ha
    have hW : m.Writes i a := ⟨t, e, hp, ha⟩
    obtain ⟨n, lo, w⟩ := a
    exact ⟨hW, hpos i n lo w hW, hc.inWidth i n lo w hW⟩
  -- No procedural writes.
  have hpw : m.processes.toList.flatMap Process2.procWrites = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨t, e, ws, hpi, -⟩ := hproc i hi
    rw [hpi]
    rfl
  -- A driver window comes from some process's comb window.
  have hsrc : ∀ x ∈ driverWins names m.processes.toList, ∃ (i : Nat) (t : Lhs2) (e : Expr2)
      (a : Win), m.processes[i]? = some (.assign t e) ∧ a ∈ t.wins m ∧ DrvWin.Matches m x a := by
    intro x hx
    simp only [driverWins, List.mem_flatMap, List.mem_filter] at hx
    obtain ⟨p, hp, hxp, -⟩ := hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨t, e, ws, hpi, hpi', -, hws, hml⟩ := hproc i hi
    rw [hpi] at hxp
    obtain ⟨a, ha, hm⟩ := hml.exists_mem x hxp
    exact ⟨i, t, e, a, hpi', hws ▸ ha, hm⟩
  apply driversOk_of_continuous hpw
  · -- pairwise disjoint: within one process, and across two
    simp only [driverWins]
    rw [List.pairwise_flatMap]
    refine ⟨fun p hp => ?_, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
      obtain ⟨t, e, ws, hpi, hpi', -, hws, hml⟩ := hproc i hi
      rw [hpi]
      apply List.Pairwise.filter
      have hsd := hc.selfDisjoint i t e hpi'
      rw [hws] at hsd
      exact hml.pairwise hsd fun x a y b ha hb hxa hyb hab => by
        obtain ⟨-, hpa, hia⟩ := hwin i t e a hpi' (hws ▸ ha)
        obtain ⟨-, hpb, hib⟩ := hwin i t e b hpi' (hws ▸ hb)
        exact DrvWin.overlaps_eq_false_of_matches hxa hyb hpa hpb hia hib hab
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij x hx y hy
      obtain ⟨t, e, ws, hpi, hpi', -, hws, hml⟩ := hproc i hi
      obtain ⟨t', e', ws', hpj, hpj', -, hws', hml'⟩ := hproc j hj
      rw [hpi] at hx
      rw [hpj] at hy
      obtain ⟨a, ha, hxa⟩ := hml.exists_mem x (List.mem_filter.mp hx).1
      obtain ⟨b, hb, hyb⟩ := hml'.exists_mem y (List.mem_filter.mp hy).1
      obtain ⟨hWa, hpa, hia⟩ := hwin i t e a hpi' (hws ▸ ha)
      obtain ⟨hWb, hpb, hib⟩ := hwin j t' e' b hpj' (hws' ▸ hb)
      exact DrvWin.overlaps_eq_false_of_matches hxa hyb hpa hpb hia hib
        (hc.disjoint i j a b (Nat.ne_of_lt hij) hWa hWb)
  · -- no driver window on an input port
    intro x hx
    obtain ⟨i, t, e, a, hpi, ha, hxa⟩ := hsrc x hx
    have hdrv : Driven m a.1 := ⟨i, a.2.1, a.2.2, ⟨t, e, hpi, ha⟩⟩
    have hni := hc.notInput a.1 hdrv
    rw [Bool.eq_false_iff]
    intro hcont
    rw [List.contains_iff_mem, hxa.1] at hcont
    exact hni (hin _ hcont)

/-- A flat instantiation's input ports are its definition's
(`PDesign.instantiate2_declSig`). -/
theorem PDesign.instantiate2_inputNames {d : PDesign} {args : List Int} {F : Nat}
    {m : Design2} (h : d.instantiate2 args F = .ok m) :
    ∀ n ∈ d.inputNames, n ∈ m.inputNames.toList := by
  intro n hn
  have hs := PDesign.instantiate2_declSig h
  simp only [PDesign.inputNames, List.mem_map, List.mem_filter] at hn
  obtain ⟨pd, ⟨hpd, hinp⟩, rfl⟩ := hn
  have hmem : (pd.name, pd.isInput, pd.isOutput) ∈ d.declSig :=
    List.mem_map.mpr ⟨pd, hpd, rfl⟩
  rw [← hs] at hmem
  obtain ⟨dc, hdc, heq⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at heq
  simp only [Design2.inputNames, Array.toList_filterMap, List.mem_filterMap]
  exact ⟨dc, hdc, by simp [heq.1, heq.2.1, hinp]⟩

/-- **`name.sem` of a flat envelope from the comb profile** (WP2's
reusable recipe, module docstring): the instantiation at the surface fuel,
`CombDesign` of the instantiated design (which the settle theorem needs
anyway) and positive write windows give `d.instantiateGD2 args = m`. -/
theorem PDesign.instantiateGD2_of_combDesign {d : PDesign} {args : List Int} {m : Design2}
    (h : d.instantiate2 args (PDesign.surfaceFuel args) = .ok m) (hc : CombDesign m)
    (hpos : ∀ i n lo w, m.Writes i (n, lo, w) → 0 < w) :
    d.instantiateGD2 args = m :=
  PDesign.instantiateGD2_of_ok h
    (driversOk_of_combDesign hc hpos (PDesign.instantiate2_inputNames h))

end LeanModels.Sv
