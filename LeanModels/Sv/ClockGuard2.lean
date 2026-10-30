import LeanModels.Sv.Hier2

/-!
# The clock-discipline guard (`LeanModels.Sv` — WP-Q0, 2026-10-30)

**Decided by Thomas, 2026-10-30 (`svgolf/design/sequential/README.md` §4 S0):
refuse, loudly, a clocked design whose clock the cycle semantics cannot give
its real meaning.** `Sem2.cycleStep2` runs every edge-phase process
(`alwaysFF`, `alwaysPlain`, `alwaysFFR`) once per cycle and NEVER reads the
value of the clock signal (`Process2.clock?` is a name that is carried and
ignored). That is exact exactly when the clock is an input port of the top
module whose rising edge IS the cycle (the stimulus protocol: one entry is one
clock period with one rising edge), and silently wrong in every other case
(measured, `experiments.md` E2/E5 of the note): `always_ff @(posedge clk) y <=
a & b` with `clk` undriven or tied low captures every cycle in the model and
never in a simulator; `assign g = clk & en; always_ff @(posedge g)` counts every
cycle in the model and only enabled edges under Xcelium (`0 0 1 2 3 4`).

## The rules (all on the ELABORATED `Design2`, flattened hierarchy included)

Let a design's *edge processes* be those with `Process2.clock? = some c`, its
*clocks* the names `c`, its *resets* the `rn` of its `alwaysFFR` processes.

1. `Clock:source` — every clock is an INPUT port of the top module, one bit
   wide. An internal net, an assign-derived or gated signal, a register, a
   constant-tied signal or an undriven signal is refused.
2. `Clock:reset` — every asynchronous reset is an input port, different from
   its own clock, and no signal is both a clock and a reset.
3. `Clock:multiple` — at most ONE clock. (Several clocks are the sequential
   layer's S5/S6: the cycle step ticks every edge process, i.e. all clocks
   together, which no stimulus of a real simulator is bound to do.)
4. `Clock:data-read` — nothing reads the clock as DATA. A process, an
   assignment or an instance connection that mentions the clock (or a
   continuous copy of it) in an expression is refused (`clk & en`,
   `assign y = clk ^ a`, `if (clk)`, an output port exporting the clock). The
   one exemption is the PLAIN COPY `assign t = clk` (nothing but an
   identifier on the right): after flattening that is what a bare clock
   connection to a child instance looks like (`u.ck = clk`), `t` joins the
   clock's copy set, and the rule applies to every read of `t` in turn (a
   child that uses its own `ck` as data reads `u.ck`, a copy of the clock);
   a copy that reaches an OUTPUT port is a data use too.

5. `Instance:clock` (the existing kind, `Hier2.lean`, `clockGuardProc` /
   `instBodyProc`) — a child flop's clock must reach it through bare
   input-port connections, up to an input port of the top (no gating, no
   inversion, no child-internal signal). `name.sem` already carries the loud
   process; this guard REPORTS it at the loader as well (first, as the root
   cause), so a gated child clock is refused at `load_design_sv2` and at a
   `refuse` row instead of surfacing as a runtime `unsupported`. The
   flattened design then satisfies rules 1 to 4 as if the child's flop were
   written in the top.

## Where it applies (BESIDE `name.sem`, like `RangeGuard2.lean` and `CombAlias2.lean`)

`Design2.clockViolation` decides the rules on the instantiated design;
`Design2.disciplineGuard` appends the loud `Clock:*` process to a violating design.
The guard needs the whole flat design, so it runs on the INSTANTIATED design:
`load_design_sv2` (`Ingest2.lean`) at the defaults and at every point of the
probe sidecar, the differential runner (`harness/sv/runner2.lean`) at each
row's point, `Envelope2.probeCheckString` (the svGolf checker's entry), and
`PDesign.clockReport` for any other tool. It is NOT part of `name.sem`: the
recorded lemmas `PDesign.instantiate2_eq`, `PDesign.instantiateG2_of_ok`,
`PDesign.instantiateGD2_of_ok`, `PDesign.instantiateGD2_eq_driverGuard`,
`Design2.driverGuard_of_ok` and the ∀-N proofs (`ripple_add`, `mul2d`,
`partsel`, `ripple_fa`, every svGolf reference, `CombViewMain.lean`) are stated
for the unguarded family, so a guard inside `instantiate2`/`instantiateG2`/
`instantiateGD2` would falsify them (`RangeGuard2.lean` and `CombAlias2.lean`
record the same constraint). A proof that wants the guard gone uses
`Design2.disciplineGuard_of_noEdge` (a design without an edge process is its own
guard — every combinational family: `Unclocked` designs) or
`Design2.disciplineGuard_of_admits`.

## Trust

The guard is a decidable `Bool`/`Option` function of the elaborated design and
only ever REFUSES: it turns a design into a loud one or leaves it unchanged
(`disciplineGuard_of_admits`). It adds no axiom and no trusted statement; a wrong
guard can wrongly refuse a design (a completeness defect, pinned by the
accepted fixtures) or wrongly admit one (the sequential statement's own
`ClockedBy` is the second line: this guard is its loader-side twin). What an
admitted design satisfies is proved below: every clock is a declared input
port (`Design2.clockViolation_source`), all edge processes share one clock
(`Design2.clockViolation_single`), and no process other than a plain copy of
the clock's copy set reads a member of that set (`Design2.clockViolation_reads`).
-/

namespace LeanModels.Sv

/-! ## What a process reads as data -/

mutual
/-- Every signal name an expression reads (source order, with repeats). -/
def Expr2.clkReads : Expr2 → List String
  | .ident n => [n]
  | .lit _ | .unsupported _ _ => []
  | .unary _ a | .resizeSigned _ a | .squash2 a | .repl _ a | .reduce _ a | .resize _ a
  | .slice a _ _ => a.clkReads
  | .binary _ l r | .scmp _ l r | .logical _ l r | .index l r _ => l.clkReads ++ r.clkReads
  | .ternary c t f => c.clkReads ++ t.clkReads ++ f.clkReads
  | .concat parts => Expr2.clkReadsList parts.toList
termination_by structural e => e

/-- `Expr2.clkReads` of a part list, concatenated. -/
def Expr2.clkReadsList : List Expr2 → List String
  | [] => []
  | e :: es => e.clkReads ++ Expr2.clkReadsList es
termination_by structural es => es
end

mutual
/-- The signals an assignment target READS (its run-time index expressions;
the written name itself is a write). -/
def Lhs2.clkReads : Lhs2 → List String
  | .ident _ | .slice .. => []
  | .index _ i _ => i.clkReads
  | .concat ps => Lhs2.clkReadsList ps
termination_by structural t => t

/-- `Lhs2.clkReads`, concatenated over a list. -/
def Lhs2.clkReadsList : List Lhs2 → List String
  | [] => []
  | t :: ts => t.clkReads ++ Lhs2.clkReadsList ts
termination_by structural ts => ts
end

mutual
/-- Every signal name a statement reads (conditions, case subjects and
patterns, right-hand sides, target indices). -/
def Stmt2.clkReads : Stmt2 → List String
  | .blockingAssign t e | .nbaAssign t e => t.clkReads ++ e.clkReads
  | .ifStmt c t e => c.clkReads ++ t.clkReads ++ Stmt2.clkReadsOpt e
  | .block body => Stmt2.clkReadsList body.toList
  | .caseStmt subj items dflt _ _ =>
      subj.clkReads ++ CaseItem2.clkReadsList items.toList ++ Stmt2.clkReadsOpt dflt
  | .unsupported _ _ => []
termination_by structural s => s

/-- `Stmt2.clkReads` of an optional statement. -/
def Stmt2.clkReadsOpt : Option Stmt2 → List String
  | none => []
  | some s => s.clkReads
termination_by structural o => o

/-- `Stmt2.clkReads`, concatenated over a list. -/
def Stmt2.clkReadsList : List Stmt2 → List String
  | [] => []
  | s :: ss => s.clkReads ++ Stmt2.clkReadsList ss
termination_by structural ss => ss

/-- `Stmt2.clkReads` of a case arm (patterns and body). -/
def CaseItem2.clkReads : CaseItem2 → List String
  | .mk pats body => Expr2.clkReadsList pats.toList ++ body.clkReads
termination_by structural it => it

/-- `CaseItem2.clkReads`, concatenated over a list. -/
def CaseItem2.clkReadsList : List CaseItem2 → List String
  | [] => []
  | it :: rest => it.clkReads ++ CaseItem2.clkReadsList rest
termination_by structural its => its
end

/-- Every signal name a process reads as data (`[]` for a loud process). -/
def Process2.clkReads : Process2 → List String
  | .alwaysFF _ b | .alwaysPlain _ b | .alwaysComb b | .alwaysFFR _ _ b => b.clkReads
  | .assign t e => t.clkReads ++ e.clkReads
  | .unsupported _ _ => []

/-- The asynchronous-reset name of an `alwaysFFR` process. -/
def Process2.rst? : Process2 → Option String
  | .alwaysFFR _ rn _ => some rn
  | _ => none

/-- A PLAIN COPY `assign t = s` (nothing but an identifier on the right, a
whole-signal target): `(t, s)`. After flattening a bare clock connection to a
child instance is exactly this. -/
def Process2.copy? : Process2 → Option (String × String)
  | .assign (.ident t) (.ident s) => some (t, s)
  | _ => none

/-! ## The copy set of the clock -/

/-- The plain copies `(target, source)` of the list. -/
def clkCopies (ps : List Process2) : List (String × String) :=
  ps.filterMap Process2.copy?

/-- One round: the targets of the copies whose source is in `A`. -/
def clkCopyStep (cps : List (String × String)) (A : List String) : List String :=
  (A ++ cps.filterMap fun (t, s) => if A.contains s then some t else none).eraseDups

/-- The copy closure of `A`: `A` plus every target reached through plain
copies, `n` rounds (`n = cps.length` suffices: every productive round adds a
new target and there are at most that many). -/
def clkCopyClosure (cps : List (String × String)) : Nat → List String → List String
  | 0, A => A
  | n + 1, A => clkCopyClosure cps n (clkCopyStep cps A)

theorem clkCopyStep_subset (cps : List (String × String)) (A : List String) :
    ∀ x ∈ A, x ∈ clkCopyStep cps A := by
  intro x hx
  simp [clkCopyStep, hx]

theorem clkCopyClosure_subset (cps : List (String × String)) :
    ∀ (n : Nat) (A : List String), ∀ x ∈ A, x ∈ clkCopyClosure cps n A
  | 0, _, _, hx => hx
  | n + 1, A, x, hx => clkCopyClosure_subset cps n _ x (clkCopyStep_subset cps A x hx)

/-! ## The rules -/

/-- The distinct clock names of the edge processes (first-occurrence order). -/
def Design2.clockNames (d : Design2) : List String :=
  (d.processes.toList.filterMap Process2.clock?).eraseDups

/-- The distinct asynchronous-reset names (first-occurrence order; only the
reset-event phase's signals). -/
def Design2.resetNames (d : Design2) : List String :=
  (d.processes.toList.filterMap Process2.rst?).eraseDups

/-- `c` is a one-bit INPUT port of the design. -/
def Design2.clockPortOk (d : Design2) (c : String) : Bool :=
  d.decls.any fun dc => dc.isInput && dc.name == c && dc.width == 1

/-- `c` is an INPUT port of the design (any width). -/
def Design2.isInputPort (d : Design2) (c : String) : Bool :=
  d.decls.any fun dc => dc.isInput && dc.name == c

/-- The copy set of the design's clocks (module docstring, rule 4). -/
def Design2.clockCopies (d : Design2) : List String :=
  let cps := clkCopies d.processes.toList
  clkCopyClosure cps (cps.length + 1) d.clockNames

/-- A signal in quotes, for messages. -/
def clkQ (n : String) : String := "'" ++ n ++ "'"

/-- The process in a message: its kind, its clock and what it writes. -/
def Process2.clkDesc (p : Process2) : String :=
  let w := match p.procWrites.eraseDups with
    | [] => ""
    | ws => s!" (writes {String.intercalate ", " (ws.map clkQ)})"
  match p with
  | .alwaysFF c _ => s!"the `always_ff @(posedge {c})` process{w}"
  | .alwaysPlain c _ => s!"the `always @(posedge {c})` process{w}"
  | .alwaysFFR c rn _ => s!"the `always_ff @(posedge {c} or negedge {rn})` process{w}"
  | .alwaysComb _ => s!"the `always_comb` process{w}"
  | .assign t _ => s!"the continuous assignment to {clkQ t.name}"
  | .unsupported k _ => s!"a loud `{k}` process"

/-- What a signal that is not an input port is, for the messages of rules 1
and 2: the design's own account of who drives it. -/
def Design2.clockOrigin (d : Design2) (c : String) : String :=
  let ps := d.processes.toList
  if ps.any (fun p => p.drvWins.any (·.1 == c)) then
    "driven inside the design by a continuous assignment, i.e. a derived, gated or constant-tied signal"
  else if ps.any (fun p => p.clock?.isSome && p.procWrites.contains c) then
    "a register"
  else if ps.any (fun p => p.procWrites.contains c) then
    "driven by combinational logic"
  else
    match d.decls.toList.find? (·.name == c) with
    | some dc =>
        if dc.isOutput then "an output port that nothing inside the design drives"
        else "an internal signal that nothing drives"
    | none => "not declared at all"

/-- The common closing sentence of the messages: why the model cannot give
such a design its meaning. -/
def clkWhy : String :=
  "the cycle semantics runs every edge process once per cycle and never reads the clock's value (Sem2.cycleStep2), so it is exact only when the clock is an input port of the top module whose edge is the cycle and nothing else uses it"

/-- The message of rule 1 for the edge process `p` clocked by `c`. -/
def Design2.clockSourceMsg (d : Design2) (p : Process2) (c : String) : String :=
  if d.isInputPort c then
    let w := ((d.decls.toList.find? (·.name == c)).map (·.width)).getD 0
    s!"{p.clkDesc} is clocked by input port {clkQ c}, which is {w} bits wide: a clock is a one-bit input port; {clkWhy}"
  else
    s!"{p.clkDesc} is clocked by {clkQ c}, which is not an input port of module {clkQ d.name} (it is {d.clockOrigin c}): {clkWhy}; use an input port of the top module as the clock"

/-- **Rule 1** (`Clock:source`): every edge process is clocked by a one-bit
INPUT port of the module. -/
def Design2.clockSourceViol (d : Design2) : Option (String × String) :=
  d.processes.toList.findSome? fun p =>
    p.clock?.bind fun c =>
      if d.clockPortOk c then none else some ("Clock:source", d.clockSourceMsg p c)

/-- **Rule 2** (`Clock:reset`): every asynchronous reset is an input port,
not its own clock, and no signal is both a clock and a reset. -/
def Design2.clockResetViol (d : Design2) : Option (String × String) :=
  let clks := d.clockNames
  d.processes.toList.findSome? fun p =>
    match p with
    | .alwaysFFR c rn _ =>
        if !d.isInputPort rn then
          some ("Clock:reset",
            s!"{p.clkDesc} uses {clkQ rn} as its asynchronous reset, which is not an input port of module {clkQ d.name} (it is {d.clockOrigin rn}): a reset the design generates itself is a real asynchronous event in hardware but only a value at a snapshot in the cycle semantics (the reset-event phase compares the settled inputs between snapshots); name an input port as the reset")
        else if rn == c then
          some ("Clock:reset",
            s!"{p.clkDesc} uses {clkQ c} as both its clock and its asynchronous reset")
        else if clks.contains rn then
          some ("Clock:reset",
            s!"{p.clkDesc} uses {clkQ rn} as its asynchronous reset, but {clkQ rn} is also the clock of another edge process: an input port is a clock or a reset, not both")
        else none
    | _ => none

/-- The message of rule 3. -/
def Design2.clockMultiMsg (d : Design2) (clks : List String) : String :=
  s!"module {clkQ d.name} has {clks.length} clocks ({String.intercalate ", " (clks.map clkQ)}): the cycle step ticks every edge process once, i.e. all of its clocks together, which no stimulus of a real simulator is bound to do; independent or interleaved clocks need the clock-domain model of the sequential layer (S5/S6) and are refused until then; use one clock port; {clkWhy}"

/-- **Rule 3** (`Clock:multiple`): at most one clock. -/
def Design2.clockMultiViol (d : Design2) : Option (String × String) :=
  if d.clockNames.length ≤ 1 then none
  else some ("Clock:multiple", d.clockMultiMsg d.clockNames)

/-- The process is a plain copy `assign t = s` whose source is in `A`. -/
def Process2.copiesFrom (A : List String) (p : Process2) : Bool :=
  match p.copy? with
  | some (_, s) => A.contains s
  | none => false

/-- The first process that reads a member of the clock's copy set as data
(a plain copy from the set is exempt), with the member it reads. -/
def Design2.clockReadHit (d : Design2) : Option (Process2 × String) :=
  let A := d.clockCopies
  d.processes.toList.findSome? fun p =>
    if p.copiesFrom A then none
    else (p.clkReads.find? (A.contains ·)).map fun r => (p, r)

/-- A member of the clock's copy set that is not a clock but an output port
(a plain copy of the clock reaches the environment). -/
def Design2.clockOutputHit (d : Design2) : Option String :=
  let clks := d.clockNames
  d.clockCopies.find? fun r =>
    !clks.contains r && d.decls.any fun dc => dc.name == r && dc.isOutput

/-- **Rule 4** (`Clock:data-read`): nothing reads the clock (or a plain copy
of it) as data, except the plain copies themselves; a copy must not reach an
output port. -/
def Design2.clockReadViol (d : Design2) : Option (String × String) :=
  let clks := d.clockNames
  let clk := clks.headD ""
  match d.clockReadHit with
  | some (p, r) =>
      let what :=
        if clks.contains r then s!"the clock {clkQ r}"
        else s!"{clkQ r}, a continuous copy of the clock {clkQ clk}"
      some ("Clock:data-read",
        s!"{p.clkDesc} reads {what} as data: a clock may only be the sensitivity of edge processes (and be copied by a plain `assign t = clk`, which is what a bare instance connection is), because {clkWhy}; a clock used as data (`clk & en`, `clk ^ a`, `if (clk)`) is a gated or derived clock")
  | none =>
      d.clockOutputHit.map fun r =>
        ("Clock:data-read",
          s!"output port {clkQ r} carries a continuous copy of the clock {clkQ clk}: the clock is used as data; {clkWhy}")

/-- **Rule 5** (`Instance:clock`): the flattened design carries the loud
child-clock process of `Hier2.lean` (`clockGuardProc` / `instBodyProc`),
reported with its own message. -/
def Design2.clockInstanceViol (d : Design2) : Option (String × String) :=
  d.processes.toList.findSome? fun p =>
    match p with
    | .unsupported "Instance:clock" msg => some ("Instance:clock", msg)
    | _ => none

/-- **The clock discipline**: the first violated rule (5, 1, 2, 3, 4 in this
order: a refused child clock is the root cause of anything the flattened
design shows), as `(kind, message)`. -/
def Design2.clockViolation (d : Design2) : Option (String × String) :=
  match d.clockInstanceViol with
  | some r => some r
  | none =>
  match d.clockSourceViol with
  | some r => some r
  | none =>
      match d.clockResetViol with
      | some r => some r
      | none =>
          match d.clockMultiViol with
          | some r => some r
          | none => d.clockReadViol

/-- `none` when the design passes the clock discipline. -/
def Design2.clockReport (d : Design2) : Option (String × String) := d.clockViolation

/-- The design passes the clock discipline. -/
def Design2.clockAdmits (d : Design2) : Bool := d.clockViolation.isNone

/-- **The guard**: the design itself when it passes, else the design with the
loud `Clock:*` process appended (so `run2`, the differential runner and
`load_design_sv2` refuse). Everything else is unchanged. -/
def Design2.disciplineGuard (d : Design2) : Design2 :=
  match d.clockViolation with
  | none => d
  | some (k, msg) => { d with processes := d.processes.push (.unsupported k msg) }

/-- **The clock guard at a parameter point** (`args`, the design already
brought to the point by `PDesign.atPoint`): the module (an instance-free one
through `instantiateG2`, a hierarchical one through `instantiateH`, as the
differential runner and `Probe2.instAtOverrides` instantiate it) under
`Design2.clockReport`. An instantiation failure is not this guard's to report
(`none`: the semantic family is loud there already). -/
def PDesign.clockReport (d : PDesign) (lib : List PDesign) (args : List Int) :
    Option (String × String) :=
  let F := PDesign.surfaceFuel args
  match (if lib.isEmpty || GenItem.listInstFree d.generates then d.instantiateG2 args F
          else d.instantiateH lib args F) with
  | .ok m => m.clockReport
  | _ => none

/-! ## Lemmas the examples use -/

@[simp] theorem Design2.disciplineGuard_name (d : Design2) :
    d.disciplineGuard.name = d.name := by
  unfold Design2.disciplineGuard; split <;> rfl

@[simp] theorem Design2.disciplineGuard_decls (d : Design2) :
    d.disciplineGuard.decls = d.decls := by
  unfold Design2.disciplineGuard; split <;> rfl

/-- A design that passes is its own guard. -/
theorem Design2.disciplineGuard_of_admits {d : Design2} (h : d.clockViolation = none) :
    d.disciplineGuard = d := by
  simp [Design2.disciplineGuard, h]

/-- A violating design is refused: its guard carries the loud `Clock:*`
process of the first violated rule. -/
theorem Design2.disciplineGuard_of_viol {d : Design2} {k msg : String}
    (h : d.clockViolation = some (k, msg)) :
    d.disciplineGuard = { d with processes := d.processes.push (.unsupported k msg) } := by
  simp [Design2.disciplineGuard, h]

private theorem clkCopyClosure_nil (cps : List (String × String)) :
    ∀ n : Nat, clkCopyClosure cps n [] = []
  | 0 => rfl
  | n + 1 => by
      have hf : cps.filterMap (fun (_ : String × String) => (none : Option String)) = [] := by
        induction cps <;> simp_all
      have : clkCopyStep cps [] = [] := by
        simp [clkCopyStep, hf]
      simp [clkCopyClosure, this, clkCopyClosure_nil cps n]

private theorem clockNames_nil_of_noEdge {d : Design2}
    (h : ∀ p ∈ d.processes.toList, p.clock? = none) : d.clockNames = [] := by
  have : d.processes.toList.filterMap Process2.clock? = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro p hp
    exact h p hp
  simp [Design2.clockNames, this]

private theorem clockSourceViol_of_noEdge {d : Design2}
    (h : ∀ p ∈ d.processes.toList, p.clock? = none) : d.clockSourceViol = none := by
  unfold Design2.clockSourceViol
  rw [List.findSome?_eq_none_iff]
  intro p hp
  simp [h p hp]

private theorem clockResetViol_of_noEdge {d : Design2}
    (h : ∀ p ∈ d.processes.toList, p.clock? = none) : d.clockResetViol = none := by
  unfold Design2.clockResetViol
  rw [List.findSome?_eq_none_iff]
  intro p hp
  have hp' := h p hp
  cases p with
  | alwaysFFR c rn b => simp [Process2.clock?] at hp'
  | _ => rfl

private theorem clockReadViol_of_noEdge {d : Design2}
    (h : ∀ p ∈ d.processes.toList, p.clock? = none) : d.clockReadViol = none := by
  have hc := clockNames_nil_of_noEdge h
  have hA : d.clockCopies = [] := by
    simp [Design2.clockCopies, hc, clkCopyClosure_nil]
  have hhit : d.clockReadHit = none := by
    unfold Design2.clockReadHit
    rw [List.findSome?_eq_none_iff]
    intro p _
    simp [hA, Process2.copiesFrom]
  have hout : d.clockOutputHit = none := by
    simp [Design2.clockOutputHit, hA]
  simp [Design2.clockReadViol, hhit, hout]

/-- A design without an edge-phase process and without a refused child clock
(every combinational family) passes the clock discipline, so its guard is the
identity. -/
theorem Design2.clockViolation_of_noEdge {d : Design2}
    (h : ∀ p ∈ d.processes.toList, p.clock? = none) (hi : d.clockInstanceViol = none) :
    d.clockViolation = none := by
  have hc := clockNames_nil_of_noEdge h
  simp [Design2.clockViolation, hi, clockSourceViol_of_noEdge h, clockResetViol_of_noEdge h,
    Design2.clockMultiViol, hc, clockReadViol_of_noEdge h]

theorem Design2.disciplineGuard_of_noEdge {d : Design2}
    (h : ∀ p ∈ d.processes.toList, p.clock? = none) (hi : d.clockInstanceViol = none) :
    d.disciplineGuard = d :=
  Design2.disciplineGuard_of_admits (Design2.clockViolation_of_noEdge h hi)

/-! ## What an admitted design satisfies -/

private theorem clockViolation_none {d : Design2} (h : d.clockViolation = none) :
    d.clockInstanceViol = none ∧ d.clockSourceViol = none ∧ d.clockResetViol = none ∧
      d.clockMultiViol = none ∧ d.clockReadViol = none := by
  unfold Design2.clockViolation at h
  cases h0 : d.clockInstanceViol with
  | some r => simp [h0] at h
  | none =>
  cases h1 : d.clockSourceViol with
  | some r => simp [h0, h1] at h
  | none =>
    cases h2 : d.clockResetViol with
    | some r => simp [h0, h1, h2] at h
    | none =>
      cases h3 : d.clockMultiViol with
      | some r => simp [h0, h1, h2, h3] at h
      | none => simp [h0, h1, h2, h3] at h; exact ⟨rfl, rfl, rfl, rfl, h⟩

/-- **Rule 1 holds**: every clock of an admitted design is a declared
one-bit input port. -/
theorem Design2.clockViolation_source {d : Design2} (h : d.clockViolation = none)
    {p : Process2} (hp : p ∈ d.processes.toList) {c : String} (hc : p.clock? = some c) :
    d.clockPortOk c = true := by
  have hs := (clockViolation_none h).2.1
  unfold Design2.clockSourceViol at hs
  rw [List.findSome?_eq_none_iff] at hs
  have := hs p hp
  rw [hc] at this
  refine Decidable.byContradiction fun hok => ?_
  simp [hok] at this

/-- **Rule 3 holds**: all edge processes of an admitted design share one
clock. -/
theorem Design2.clockViolation_single {d : Design2} (h : d.clockViolation = none)
    {p q : Process2} (hp : p ∈ d.processes.toList) (hq : q ∈ d.processes.toList)
    {c c' : String} (hc : p.clock? = some c) (hc' : q.clock? = some c') : c = c' := by
  have hm := (clockViolation_none h).2.2.2.1
  unfold Design2.clockMultiViol at hm
  have hle : d.clockNames.length ≤ 1 :=
    Decidable.byContradiction fun hlt => by simp [hlt] at hm
  have h1 : c ∈ d.clockNames := by
    unfold Design2.clockNames
    exact List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨p, hp, hc⟩)
  have h2 : c' ∈ d.clockNames := by
    unfold Design2.clockNames
    exact List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨q, hq, hc'⟩)
  rcases hcn : d.clockNames with _ | ⟨x, _ | ⟨y, zs⟩⟩
  · rw [hcn] at h1; simp at h1
  · rw [hcn] at h1 h2
    simp at h1 h2
    rw [h1, h2]
  · rw [hcn] at hle; simp at hle

/-- The clocks are in their own copy set. -/
theorem Design2.clockNames_subset_copies (d : Design2) :
    ∀ c ∈ d.clockNames, c ∈ d.clockCopies := by
  intro c hc
  unfold Design2.clockCopies
  exact clkCopyClosure_subset _ _ _ c hc

/-- **Rule 4 holds**: in an admitted design no process reads a member of the
clock's copy set as data, except a plain copy whose source is in the set
(`assign t = s`, the shape of a bare clock connection). -/
theorem Design2.clockViolation_reads {d : Design2} (h : d.clockViolation = none)
    {p : Process2} (hp : p ∈ d.processes.toList) :
    p.copiesFrom d.clockCopies = true ∨ ∀ r ∈ p.clkReads, r ∉ d.clockCopies := by
  have hr := (clockViolation_none h).2.2.2.2
  have hhit : d.clockReadHit = none := by
    unfold Design2.clockReadViol at hr
    cases h1 : d.clockReadHit with
    | none => rfl
    | some pr => simp [h1] at hr
  unfold Design2.clockReadHit at hhit
  rw [List.findSome?_eq_none_iff] at hhit
  have := hhit p hp
  by_cases hc : p.copiesFrom d.clockCopies = true
  · exact Or.inl hc
  · right
    intro r hr' hmem
    simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff] at this
    have := List.find?_eq_none.mp this r hr'
    simp [hmem] at this

/-! ## Pinned shapes (`#guard`; the SV twins are the `sem2/clk_*` fixtures
of `Examples/system-verilog` and the `clk_*` rows of `harness/sv/cases2.json`) -/

section pins

private def dcl (n : String) (w : Nat := 1) (i : Bool := false) (o : Bool := false) : Decl :=
  { name := n, width := w, isInput := i, isOutput := o }

private def id' (n : String) : Expr2 := .ident n
private def nba (n : String) (e : Expr2) : Stmt2 := .nbaAssign (.ident n) e
private def blk (ss : List Stmt2) : Stmt2 := .block ss.toArray
private def mk (ds : List Decl) (ps : List Process2) : Design2 :=
  { name := "pin", decls := ds.toArray, processes := ps.toArray }

/-- clk, rst_n, en, d inputs; q output; g, r internal. -/
private def baseDecls : List Decl :=
  [dcl "clk" (i := true), dcl "rst_n" (i := true), dcl "en" (i := true),
   dcl "d" 4 (i := true), dcl "q" 4 (o := true), dcl "g", dcl "r"]

private def kindOf (d : Design2) : Option String := d.clockViolation.map (·.1)

/-- `always_ff @(posedge clk) if (en) q <= q ^ d`. -/
private def ffEn : Process2 :=
  .alwaysFF "clk" (.ifStmt (id' "en") (nba "q" (.binary .xor (id' "q") (id' "d"))) none)

-- ACCEPTED: the plain synchronous design, the async-reset block, a pipeline.
#guard (mk baseDecls [ffEn]).clockAdmits
#guard (mk baseDecls [.alwaysFFR "clk" "rst_n"
    (.ifStmt (id' "rst_n") (nba "q" (id' "d")) (some (nba "q" (.lit (LVec.ofNat 4 0)))))]).clockAdmits
#guard (mk baseDecls [ffEn, .alwaysFF "clk" (nba "r" (id' "en"))]).clockAdmits
-- a design with no edge process is its own guard (every combinational family).
#guard (mk baseDecls [.assign (.ident "q") (id' "d")]).clockAdmits
#guard (mk baseDecls [.assign (.ident "q") (id' "d")]).disciplineGuard.processes.size == 1

-- Rule 1 `Clock:source`: undriven internal clock, constant-tied clock,
-- assign-derived (gated) clock, register used as a clock, output port.
#guard kindOf (mk baseDecls [.alwaysFF "g" (nba "q" (id' "d"))]) == some "Clock:source"
#guard kindOf (mk baseDecls [.assign (.ident "g") (.lit (LVec.ofNat 1 0)),
    .alwaysFF "g" (nba "q" (id' "d"))]) == some "Clock:source"
#guard kindOf (mk baseDecls [.assign (.ident "g") (.binary .and (id' "clk") (id' "en")),
    .alwaysFF "g" (nba "q" (id' "d"))]) == some "Clock:source"
#guard kindOf (mk baseDecls [.alwaysFF "clk" (nba "r" (.unary .bnot (id' "r"))),
    .alwaysFF "r" (nba "q" (id' "d"))]) == some "Clock:source"
#guard kindOf (mk baseDecls [.alwaysFF "q" (nba "q" (id' "d"))]) == some "Clock:source"
-- a wide input is not a clock.
#guard kindOf (mk baseDecls [.alwaysFF "d" (nba "q" (id' "d"))]) == some "Clock:source"
-- the message names the process, the clock and the rule's cause.
#guard match (mk baseDecls [.assign (.ident "g") (.lit (LVec.ofNat 1 0)),
    .alwaysFF "g" (nba "q" (id' "d"))]).clockViolation with
  | some (_, msg) => (msg.splitOn "driven inside the design by a continuous assignment").length == 2
      && (msg.splitOn "always_ff @(posedge g)").length == 2
  | none => false

-- Rule 5 `Instance:clock`: the child-clock loud process of Hier2 is reported first.
#guard kindOf (mk baseDecls [ffEn, .unsupported "Instance:clock" "instance 'u': ..."])
    == some "Instance:clock"

-- Rule 2 `Clock:reset`: internal reset, reset = clock, reset also a clock.
#guard kindOf (mk baseDecls [.alwaysFFR "clk" "g" (nba "q" (id' "d"))]) == some "Clock:reset"
#guard kindOf (mk baseDecls [.alwaysFFR "clk" "clk" (nba "q" (id' "d"))]) == some "Clock:reset"
#guard kindOf (mk baseDecls [.alwaysFFR "clk" "rst_n" (nba "q" (id' "d")),
    .alwaysFF "rst_n" (nba "r" (id' "d"))]) == some "Clock:reset"

-- Rule 3 `Clock:multiple`: a second clock PORT is refused too.
#guard kindOf (mk (baseDecls ++ [dcl "clk2" (i := true)])
    [ffEn, .alwaysFF "clk2" (nba "r" (id' "en"))]) == some "Clock:multiple"

-- Rule 4 `Clock:data-read`: the clock read as data in an assign, an if
-- condition, a case subject, a target index, an output copy.
#guard kindOf (mk baseDecls [ffEn, .assign (.ident "r") (.binary .xor (id' "clk") (id' "en"))])
    == some "Clock:data-read"
#guard kindOf (mk baseDecls [.alwaysFF "clk" (.ifStmt (id' "clk") (nba "q" (id' "d")) none)])
    == some "Clock:data-read"
#guard kindOf (mk baseDecls [ffEn, .alwaysComb (.caseStmt (id' "clk") #[] none false .none)])
    == some "Clock:data-read"
#guard kindOf (mk baseDecls [ffEn,
    .alwaysComb (.blockingAssign (.index "q" (id' "clk") 1) (id' "en"))]) == some "Clock:data-read"
#guard kindOf (mk (baseDecls ++ [dcl "o" (o := true)]) [ffEn, .assign (.ident "o") (id' "clk")])
    == some "Clock:data-read"
-- a plain copy that nothing reads is the shape of a bare instance connection: admitted …
#guard (mk baseDecls [ffEn, .assign (.ident "g") (id' "clk")]).clockAdmits
-- … but once the copy is READ (a child using its clock port as data) it is refused,
-- and the message names the copy.
#guard kindOf (mk baseDecls [ffEn, .assign (.ident "g") (id' "clk"),
    .assign (.ident "r") (.binary .and (id' "g") (id' "en"))]) == some "Clock:data-read"
#guard match (mk baseDecls [ffEn, .assign (.ident "g") (id' "clk"),
    .assign (.ident "r") (.binary .and (id' "g") (id' "en"))]).clockViolation with
  | some (_, msg) => (msg.splitOn "a continuous copy of the clock 'clk'").length == 2
  | none => false
-- chains of copies are followed (in any order).
#guard kindOf (mk baseDecls [ffEn, .assign (.ident "r") (id' "g"), .assign (.ident "g") (id' "clk"),
    .assign (.ident "q") (.resize 4 (id' "r"))]) == some "Clock:data-read"
-- the reset may be read as data (every sync-reset body reads it).
#guard (mk baseDecls [.alwaysFFR "clk" "rst_n"
    (.ifStmt (.unary .lnot (id' "rst_n")) (nba "q" (id' "d")) none),
    .assign (.ident "r") (id' "rst_n")]).clockAdmits

-- The guard: identity on an admitted design, one appended loud process on a refused one.
#guard (mk baseDecls [ffEn]).disciplineGuard.processes.size == 1
#guard (mk baseDecls [.alwaysFF "g" (nba "q" (id' "d"))]).disciplineGuard.processes.size == 2
#guard match (mk baseDecls [.alwaysFF "g" (nba "q" (id' "d"))]).disciplineGuard.processes[1]? with
  | some (Process2.unsupported "Clock:source" _) => true
  | _ => false

end pins

/-! ## Axiom pins

Standard axioms only; the `#guard_msgs` wrappers make the build fail if any of
these drifts. -/

/--
info: 'LeanModels.Sv.Design2.clockViolation_of_noEdge' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Design2.clockViolation_of_noEdge

/--
info: 'LeanModels.Sv.Design2.clockViolation_source' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Design2.clockViolation_source

/--
info: 'LeanModels.Sv.Design2.clockViolation_single' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Design2.clockViolation_single

/--
info: 'LeanModels.Sv.Design2.clockViolation_reads' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Design2.clockViolation_reads

end LeanModels.Sv
