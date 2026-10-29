import LeanModels.Sv.Hier2

/-!
# The `always_comb` alias guard (`LeanModels.Sv` — WP4 round 6, lane B)

**Decided by Thomas, 2026-10-29: refuse an `always_comb` block that reads a
continuous copy of a variable it writes, loudly.** The self-read guard
(`CombGuard2.lean`) sees one process on its own result. It cannot see this
design:

```systemverilog
assign w = t;
always_comb begin y = w; t = a; end
```

The block reads `w` and writes `t` — different variables — yet `w` follows
`t` through a continuous assignment, so the block's own write of `t` changes
a signal the block read earlier in the same run. IEEE 1800-2023 §9.2.2.2.1
puts `w` in the block's implicit sensitivity list (it is read and not written
by the block), so the update of `w` must wake the block. Whether it does
depends on WHEN the simulator applies the update: §4.7 ("the simulator may
suspend execution and place the partially completed event as a pending event
in the event region") and §4.8 (its `assign p = q; … q = 0; $display(p);`
example: "the simulator is correct in displaying either a 1 or a 0") leave
both orders open. Xcelium 24.03 and Verilator 5.042 apply the update after
the block suspends at its event control, which re-runs the block (`y = a`);
Icarus 12.0 applies it SYNCHRONOUSLY inside the block's run, the block is
not waiting yet, the wake-up is lost, and `y` keeps the previous `w`
(`docs/sv-oracle-disagreements.md`, "Icarus propagates a copy inside the
block's own run"). The model's settle semantics gives Xcelium's answer. The
tools split, so the block is refused (policy: refuse where the tools split).

## The rule

A body is refused when, on some control path through it, a statement reads
a bit that is **downstream, through at least one continuous assignment, of a
bit the path writes at that statement or later**. "Continuous assignment"
means every `Process2.assign` of the flat design — after `Hier2.lean`'s
flattening these include the port connections, so a port loop (a child's
input and output port tied to one parent variable) exists only at this
level — and the check does not look at what the right-hand side computes:
`assign w = t`, `assign w = ~t`, `assign w = t[1:0]`, a chain of such
assigns and a port loop are all refused, not by the kind of functor the
simulator builds for them.

Not refused, because every tool agrees on them (measured, round 3 and 4):

* write-then-read, `assign w = t; always_comb begin t = a; y = w; end`: the
  read comes after the last write of its source on every path;
* a SEPARATE `always_comb` copy, `always_comb w = t;` beside the block: the
  copy is a process, not an `assign`, and is woken like any other process;
* a read of a copy of a variable the block does not write.

## The check

`fanOut fl A` is the set of windows reached from the windows `A` through
at least one hop of the design's continuous assignments `fl` (each
`(reads, writes)`, `Process2.aflow`): an assignment fires when one of its
read windows overlaps `A` or an already reached window, and then contributes
its write windows. The walk `Stmt2.aliasViol` is `Stmt2.combViol`
(`CombGuard2.lean`) with two changes: the written-after set `A` is replaced
by its fan-out before it is compared with the reads (`readsViol [] (fanOut …)`,
the self-read guard's own `readsViol` with an empty must-write set — a copy
is never written by the block, so "already written on every path" never
excuses a read of it), and the zero-hop case is left to the self-read guard
(`fanOut` contains only windows reached by an assignment). Reads (`Expr2.rdW`)
and may-writes (`Stmt2.mayW`) are the self-read guard's, so the bit
granularity is the same: constant slices are exact, run-time indices cover
their whole signal.

## Where it applies (BESIDE `name.sem`, like `RangeGuard2.lean`)

`Design2.aliasGuard` replaces each `Process2.alwaysComb` whose body the walk
refuses by `Process2.unsupported "AlwaysComb:alias-read" msg`; every other
process is untouched. The guard needs the whole flat design, so it runs on
the INSTANTIATED design: `load_design_sv2` (`Ingest2.lean`) at the defaults
and at every point of the probe sidecar, the differential runner
(`harness/sv/runner2.lean`) at each row's point, and
`PDesign.aliasReport` for any other tool. It is NOT part of `name.sem`:
the recorded lemmas `PDesign.instantiate2_eq`, `PDesign.assemble2_processes`,
`PDesign.instantiateG2_of_ok`, `PDesign.instantiateGD2_of_ok`,
`PDesign.instantiateGD2_eq_driverGuard`, `Design2.driverGuard_of_ok`,
`PDesign.instantiateH_of_rec` and the ∀-N proofs of `ripple_add`, `mul2d`,
`partsel`, `ripple_fa` (and `CombViewMain.lean`, which unfolds
`instantiateGD2`) are stated for the unguarded family, so a guard inside
`instantiate2`/`instantiateG2`/`instantiateGD2` would falsify them
(`RangeGuard2.lean` records the same constraint for the legacy-range guard).
A ∀-N proof that wants the guard gone uses
`Design2.aliasGuard_of_noComb` (a design without `always_comb` is its own
guard — `ripple_add`, `mul2d` and `ripple_fa` are continuous-only; `partsel`
has two `always_comb` blocks that read only the input `b` and write `w_hi` /
`w_lo`, which no `assign` reads, so the census finds it admitted at every row's
point but no ∀-N statement of that is recorded),
`Design2.aliasGuard_of_noAssign` (no continuous assignment: the proof API's
designs, `CombAlias2Example.lean`) or `Design2.aliasGuard_of_admits` (the
admission is decided by the walk, `decide`/`simp` at a closed or a symbolic
width).

A hierarchy is checked ONCE, on the flattened design: a child's signals
carry the instance prefix (`u.w`), and the message names the instance when
the violating signal is one of an instance's (`aliasMsg`).

## Justification (`CombAlias2Sound.lean`)

Proved there, and only that: the walk is sound for control paths — on EVERY
control path of an admitted body, no read of a bit is downstream (through
the design's continuous assignments, at bit granularity) of a bit the path
writes at or after the read (`Stmt2.aliasViol_epaths`, via
`Down.mem_fanOut`/`fanOut_closed`) — and the design-level facts the examples need
(identity on admitted designs, idempotence, no assigns ⇒ no violation). The
event-driven schedule equivalence (a simulator that applies the copy's
update inside the block's run reads the same value as one that defers it) is
NOT formalized: `Sem2.lean` has no intra-block propagation semantics to
prove it against, and the argument that the two schedules agree on an
admitted body is the measured mechanism in `docs/sv-oracle-disagreements.md`.
-/

namespace LeanModels.Sv

open CombGuard

namespace CombGuard

/-! ## Continuous flows and their fan-out -/

/-- One continuous assignment as a flow: the windows its evaluation reads
(right-hand side and the target's run-time index expressions), then the
windows it may write. -/
abbrev AFlow := List BWin × List BWin

/-- The window lists share a bit (the intersection of some pair is
non-empty). -/
def touches (F R : List BWin) : Bool :=
  R.any fun r => F.any fun f => (r.inter f).2.2 != 0

/-- The assignments of `rem` that read a bit of `S`. -/
def hitsOf (S : List BWin) (rem : List AFlow) : List AFlow :=
  rem.filter fun fl => touches S fl.1

/-- The assignments of `rem` that read no bit of `S`. -/
def missOf (S : List BWin) (rem : List AFlow) : List AFlow :=
  rem.filter fun fl => !touches S fl.1

/-- The reached windows: `acc` so far; each round fires the assignments of
`rem` that read a bit of `A ++ acc` (each fires once and leaves `rem`) and
appends their write windows; no assignment left to fire, or no fuel, ends
it. With the fuel `rem.length` every assignment gets its chance
(`fanAux_closed`). -/
def fanAux : Nat → List AFlow → List BWin → List BWin → List BWin
  | 0, _, _, acc => acc
  | n + 1, rem, A, acc =>
      let hit := hitsOf (A ++ acc) rem
      if hit.isEmpty then acc
      else fanAux n (missOf (A ++ acc) rem) A (acc ++ hit.flatMap (·.2))

/-- **The fan-out of `A` through the continuous assignments `fl`**: the
write windows of every assignment reachable from `A` by at least one hop
(`A` itself is not in it unless a loop leads back). -/
def fanOut (fl : List AFlow) (A : List BWin) : List BWin := fanAux fl.length fl A []

/-- The alias check of one read set against one written-after set: the
first read window that overlaps a window downstream of `X`. -/
def aliasChk (fl : List AFlow) (X R : List BWin) : Option BWin :=
  readsViol [] (fanOut fl X) R

end CombGuard

/-- The flow of a process: an `assign` reads its right-hand side and its
target's index expressions and may write its target; no other process is a
continuous assignment. -/
def Process2.aflow (wd : String → Option Nat) : Process2 → List AFlow
  | .assign t e => [(e.rdW wd ++ t.rdW wd, t.mayW wd)]
  | _ => []

/-- The continuous flows of a process list (after flattening these include
the port connections). -/
def aliasFlows (wd : String → Option Nat) (ps : List Process2) : List AFlow :=
  ps.flatMap (Process2.aflow wd)

/-! ## The walk -/

mutual
/-- **The first alias-read violation** of statement `s` (`none`: none),
given the windows `A` some path may write after `s`. The shape of
`Stmt2.combViol` with the must-write set dropped and every written set
replaced by its fan-out; an assignment reads its right-hand side and its
target's index expressions BEFORE it writes its target. -/
def Stmt2.aliasViol (wd : String → Option Nat) (fl : List AFlow) (A : List BWin) :
    Stmt2 → Option BWin
  | .blockingAssign t e => aliasChk fl (t.mayW wd ++ A) (e.rdW wd ++ t.rdW wd)
  | .nbaAssign t e => aliasChk fl A (e.rdW wd ++ t.rdW wd)
  | .ifStmt c a b =>
      aliasChk fl (a.mayW wd ++ Stmt2.optMayW wd b ++ A) (c.rdW wd) <|>
        a.aliasViol wd fl A <|> Stmt2.optAliasViol wd fl A b
  | .block ss => Stmt2.listAliasViol wd fl A ss.toList
  | .caseStmt subj its d _ _ =>
      aliasChk fl (CaseItem2.listMayW wd its.toList ++ Stmt2.optMayW wd d ++ A) (subj.rdW wd) <|>
        CaseItem2.listAliasViol wd fl A (Stmt2.optMayW wd d) (Stmt2.optAliasViol wd fl A d)
          its.toList
  | .unsupported _ _ => none
termination_by structural s => s

/-- `Stmt2.aliasViol` of an optional statement. -/
def Stmt2.optAliasViol (wd : String → Option Nat) (fl : List AFlow) (A : List BWin) :
    Option Stmt2 → Option BWin
  | none => none
  | some s => s.aliasViol wd fl A
termination_by structural o => o

/-- A sequence: each statement sees the may-writes of the ones after it. -/
def Stmt2.listAliasViol (wd : String → Option Nat) (fl : List AFlow) (A : List BWin) :
    List Stmt2 → Option BWin
  | [] => none
  | s :: ss =>
      s.aliasViol wd fl (Stmt2.listMayW wd ss ++ A) <|> Stmt2.listAliasViol wd fl A ss
termination_by structural ss => ss

/-- The arms of a `case` (`dA`: the default's may-writes, `dV`: the
default's violation), as `CaseItem2.listCombViol`. -/
def CaseItem2.listAliasViol (wd : String → Option Nat) (fl : List AFlow) (A dA : List BWin)
    (dV : Option BWin) : List CaseItem2 → Option BWin
  | [] => dV
  | .mk pats body :: rest =>
      aliasChk fl (body.mayW wd ++ CaseItem2.listMayW wd rest ++ dA ++ A)
          (Expr2.listRdW wd pats.toList) <|>
        body.aliasViol wd fl A <|> CaseItem2.listAliasViol wd fl A dA dV rest
termination_by structural its => its
end

/-! ## The guard -/

/-- The walk from an empty written-after set finds no alias read. -/
def Stmt2.aliasAdmits (wd : String → Option Nat) (fl : List AFlow) (body : Stmt2) : Bool :=
  (body.aliasViol wd fl []).isNone

/-- The first written window `x` of the body whose fan-out overlaps the
violating window `W` (the message names its signal). -/
def aliasSource (wd : String → Option Nat) (fl : List AFlow) (body : Stmt2) (W : BWin) :
    Option String :=
  (body.mayW wd).findSome? fun x => if touches (fanOut fl [x]) [W] then some x.1 else none

/-- The refusal message for a violating window `W` of the `always_comb` of
module `mname`. A signal of a flattened instance (`u.w`) is named with its
instance. -/
def aliasMsg (mname : String) (src : Option String) (W : BWin) : String :=
  let bits := if W.2.2 = 1 then s!"bit [{W.2.1}]" else s!"bits [{W.2.1 + W.2.2 - 1}:{W.2.1}]"
  let parts := W.1.splitOn "."
  let loc := parts.getLast?.getD W.1
  let path := ".".intercalate parts.dropLast
  let inst := if parts.length > 1 then
      s!" (signal '{loc}' of instance '{path}', flattened name '{W.1}')"
    else ""
  let from_ := match src with
    | some s => s!"'{s}'"
    | none => "a variable"
  s!"always_comb block of module '{mname}' reads {bits} of '{W.1}'{inst}, a continuous copy (an `assign`, a net or a port connection, possibly through a chain of them) of {from_}, which the block writes later on that path (or in the very statement that reads the copy): IEEE 1800-2023 §9.2.2.2.1 puts the copy in the block's implicit sensitivity list, but §4.7/§4.8 let a simulator update the copy inside the block's own run, where the wake-up is lost (Icarus 12 keeps the previous value in the read), or defer the update and re-run the block (Xcelium 24.03, Verilator 5.042 and the settle semantics): no answer is safe, so the block is refused (read the copy after the last write of its source, or copy in a separate always_comb)"

/-- **The guard on one process** (`mname`: the design's name): an
`always_comb` whose body the walk refuses becomes a loud
`AlwaysComb:alias-read` process; every other process is unchanged. -/
def aliasGuardProc (mname : String) (wd : String → Option Nat) (fl : List AFlow) :
    Process2 → Process2
  | .alwaysComb b =>
      match b.aliasViol wd fl [] with
      | some W => .unsupported "AlwaysComb:alias-read" (aliasMsg mname (aliasSource wd fl b W) W)
      | none => .alwaysComb b
  | p => p

/-- **The alias guard on a flat design** (instance-free or flattened): the
design's declared widths (`Design2.combWd`) and continuous flows
(`aliasFlows`), then `aliasGuardProc` on every process. The declarations,
the name and the order of the processes are kept. -/
def Design2.aliasGuard (m : Design2) : Design2 :=
  let wd := m.combWd
  let fl := aliasFlows wd m.processes.toList
  { m with processes := m.processes.map (aliasGuardProc m.name wd fl) }

/-- The first `AlwaysComb:alias-read` message of the guarded design, if
any. -/
def Design2.aliasReport (m : Design2) : Option String :=
  m.aliasGuard.processes.toList.findSome? fun p =>
    match p with
    | .unsupported "AlwaysComb:alias-read" msg => some msg
    | _ => none

/-- Every `always_comb` of the design passes. -/
def Design2.aliasAdmits (m : Design2) : Bool := m.aliasReport.isNone

/-- **The alias guard at a parameter point** (`args`, the design already
brought to the point by `PDesign.atPoint`): the module (an instance-free one
through `instantiateG2`, a hierarchical one through `instantiateH`, as the
differential runner and `Probe2.instAtOverrides` instantiate it) under
`Design2.aliasReport`. An instantiation failure is not this guard's to
report (`none`: the semantic family is loud there already). -/
def PDesign.aliasReport (d : PDesign) (lib : List PDesign) (args : List Int) : Option String :=
  let F := PDesign.surfaceFuel args
  match (if lib.isEmpty || GenItem.listInstFree d.generates then d.instantiateG2 args F
          else d.instantiateH lib args F) with
  | .ok m => m.aliasReport
  | _ => none

/-! ## Lemmas the examples use -/

theorem aliasGuardProc_of_admits {mname : String} {wd : String → Option Nat} {fl : List AFlow}
    {body : Stmt2} (h : body.aliasViol wd fl [] = none) :
    aliasGuardProc mname wd fl (.alwaysComb body) = .alwaysComb body := by
  simp [aliasGuardProc, h]

theorem aliasGuardProc_of_viol {mname : String} {wd : String → Option Nat} {fl : List AFlow}
    {body : Stmt2} {W : BWin} (h : body.aliasViol wd fl [] = some W) :
    aliasGuardProc mname wd fl (.alwaysComb body) =
      .unsupported "AlwaysComb:alias-read" (aliasMsg mname (aliasSource wd fl body W) W) := by
  simp [aliasGuardProc, h]

/-- Only `always_comb` processes are touched. -/
theorem aliasGuardProc_of_ne {mname : String} {wd : String → Option Nat} {fl : List AFlow}
    {p : Process2} (h : ∀ b, p ≠ .alwaysComb b) : aliasGuardProc mname wd fl p = p := by
  cases p <;> first | rfl | exact absurd rfl (h _)

@[simp] theorem Design2.aliasGuard_name (m : Design2) : m.aliasGuard.name = m.name := rfl

@[simp] theorem Design2.aliasGuard_decls (m : Design2) : m.aliasGuard.decls = m.decls := rfl

theorem Design2.aliasGuard_processes (m : Design2) :
    m.aliasGuard.processes.toList =
      m.processes.toList.map (aliasGuardProc m.name m.combWd
        (aliasFlows m.combWd m.processes.toList)) := by
  simp [Design2.aliasGuard]

private theorem array_map_self {α : Type} (f : α → α) (ps : Array α)
    (h : ∀ p ∈ ps.toList, f p = p) : ps.map f = ps := by
  apply Array.ext'
  rw [Array.toList_map]
  exact (List.map_congr_left (g := id) h).trans (List.map_id _)

/-- A design without `always_comb` is its own guard — every ∀-N family the
repository proves a theorem about (`ripple_add`, `mul2d`, `partsel`,
`ripple_fa`) is continuous-only. -/
theorem Design2.aliasGuard_of_noComb {m : Design2}
    (h : ∀ p ∈ m.processes.toList, ∀ b, p ≠ .alwaysComb b) : m.aliasGuard = m := by
  have key : m.processes.map (aliasGuardProc m.name m.combWd
      (aliasFlows m.combWd m.processes.toList)) = m.processes :=
    array_map_self _ _ (fun p hp => aliasGuardProc_of_ne (h p hp))
  simp only [Design2.aliasGuard]
  rw [key]

/-- A design every `always_comb` of which the walk admits is its own
guard. -/
theorem Design2.aliasGuard_of_admits {m : Design2}
    (h : ∀ b, .alwaysComb b ∈ m.processes.toList →
      b.aliasViol m.combWd (aliasFlows m.combWd m.processes.toList) [] = none) :
    m.aliasGuard = m := by
  have key : m.processes.map (aliasGuardProc m.name m.combWd
      (aliasFlows m.combWd m.processes.toList)) = m.processes := by
    apply array_map_self
    intro p hp
    cases p with
    | alwaysComb b => exact aliasGuardProc_of_admits (h b hp)
    | _ => rfl
  simp only [Design2.aliasGuard]
  rw [key]

/-! ## Pinned shapes (`#guard`; the SV twins are the `sem2/acg_alias_*`
fixtures of `harness/sv/cases2.json`) -/

section pins

private def dcl (n : String) (w : Nat) (i : Bool := false) (o : Bool := false) : Decl :=
  { name := n, width := w, isInput := i, isOutput := o }

private def ba (n : String) (e : Expr2) : Stmt2 := .blockingAssign (.ident n) e
private def id' (n : String) : Expr2 := .ident n
private def blk (ss : List Stmt2) : Stmt2 := .block ss.toArray

private def aliasDecls : Array Decl :=
  #[dcl "a" 2 (i := true), dcl "y" 2 (o := true), dcl "t" 2, dcl "w" 2, dcl "v" 2, dcl "z" 2]

private def mk (ps : List Process2) : Design2 :=
  { name := "pin", decls := aliasDecls, processes := ps.toArray }

private def isAliasRefused : Process2 → Bool
  | .unsupported "AlwaysComb:alias-read" _ => true
  | _ => false

private def assignWT : Process2 := .assign (.ident "w") (id' "t")
private def assignVW : Process2 := .assign (.ident "v") (id' "w")

-- `assign w = t; always_comb begin y = w; t = a; end` (acg_alias_assign): refused, on all of `w`.
#guard ((mk [assignWT, .alwaysComb (blk [ba "y" (id' "w"), ba "t" (id' "a")])]).aliasReport.isSome)
#guard isAliasRefused (mk [assignWT, .alwaysComb (blk [ba "y" (id' "w"), ba "t" (id' "a")])]).aliasGuard.processes[1]!
-- write then read (admitted): `t = a; y = w;`
#guard (mk [assignWT, .alwaysComb (blk [ba "t" (id' "a"), ba "y" (id' "w")])]).aliasAdmits
-- the copy through a SEPARATE always_comb is not an `assign`: admitted.
#guard (mk [.alwaysComb (ba "w" (id' "t")),
    .alwaysComb (blk [ba "y" (id' "w"), ba "t" (id' "a")])]).aliasAdmits
-- a chain `assign w = t; assign v = w; … y = v; t = a;`: refused (transitive).
#guard !(mk [assignWT, assignVW, .alwaysComb (blk [ba "y" (id' "v"), ba "t" (id' "a")])]).aliasAdmits
-- … and in the other order of the assigns.
#guard !(mk [assignVW, assignWT, .alwaysComb (blk [ba "y" (id' "v"), ba "t" (id' "a")])]).aliasAdmits
-- three hops in the scrambled order (the shape of `acg_alias_thru` after
-- flattening: t -> u.i -> u.o -> w, two port connections around the child's
-- own assign, here v, z standing for u.i, u.o): refused.
#guard !(mk [.assign (.ident "w") (id' "z"), .assign (.ident "v") (id' "t"),
    .assign (.ident "z") (id' "v"),
    .alwaysComb (blk [ba "y" (id' "w"), ba "t" (id' "a")])]).aliasAdmits
-- … and the same chain with the write BEFORE the read: admitted.
#guard (mk [.assign (.ident "w") (id' "z"), .assign (.ident "v") (id' "t"),
    .assign (.ident "z") (id' "v"),
    .alwaysComb (blk [ba "t" (id' "a"), ba "y" (id' "w")])]).aliasAdmits
-- not by the functor: `assign w = ~t` is refused as well.
#guard !(mk [.assign (.ident "w") (.unary .bnot (id' "t")),
    .alwaysComb (blk [ba "y" (id' "w"), ba "t" (id' "a")])]).aliasAdmits
-- a copy of something the block does not write: admitted.
#guard (mk [.assign (.ident "w") (id' "a"), .alwaysComb (blk [ba "y" (id' "w"), ba "t" (id' "a")])]).aliasAdmits
-- a read after the first write but before a LATER write of the source: refused.
#guard !(mk [assignWT,
    .alwaysComb (blk [ba "t" (id' "a"), ba "y" (id' "w"), ba "t" (id' "a")])]).aliasAdmits
-- a conditional write after the read: refused (some path).
#guard !(mk [assignWT, .alwaysComb (blk [ba "y" (id' "w"),
    .ifStmt (id' "a") (ba "t" (id' "a")) none])]).aliasAdmits
-- the read in a condition, the write in a branch: refused.
#guard !(mk [assignWT, .alwaysComb (.ifStmt (id' "w") (ba "t" (id' "a")) none)]).aliasAdmits
-- one statement reading the copy of its own target: `t = w` — a loop through the copy.
#guard !(mk [assignWT, .alwaysComb (ba "t" (id' "w"))]).aliasAdmits
-- bit precision: the copy of bit 0 read, bit 1 written later — admitted …
#guard (mk [.assign (.ident "w") (.slice (id' "t") 0 1),
    .alwaysComb (blk [ba "y" (id' "w"), .blockingAssign (.slice "t" 1 1) (id' "a")])]).aliasAdmits
-- … bit 0 written later — refused.
#guard !(mk [.assign (.ident "w") (.slice (id' "t") 0 1),
    .alwaysComb (blk [ba "y" (id' "w"), .blockingAssign (.slice "t" 0 1) (id' "a")])]).aliasAdmits
-- no assigns at all: nothing to refuse.
#guard (mk [.alwaysComb (blk [ba "y" (id' "t"), ba "t" (id' "a")])]).aliasAdmits
-- the self-read (zero hops) is the other guard's: here `y = t; t = a;` is not an alias read.
#guard (mk [.alwaysComb (blk [ba "t" (id' "a"), ba "y" (id' "t")])]).aliasAdmits

end pins

/-! ## Axiom pins

Standard axioms only; the `#guard_msgs` wrappers make the build fail if any of
these drifts (the rest of the file's theorems are pinned in
`CombAlias2Sound.lean` and `CombAlias2Example.lean`). -/

/--
info: 'LeanModels.Sv.Design2.aliasGuard_of_noComb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Design2.aliasGuard_of_noComb

/--
info: 'LeanModels.Sv.Design2.aliasGuard_of_admits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Design2.aliasGuard_of_admits


end LeanModels.Sv
