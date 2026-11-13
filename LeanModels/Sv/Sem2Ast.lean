import LeanModels.Sv.Semantics

import LeanModels.Sv.Semantics

/-!
# SV semantic tier (`LeanModels.Sv` — phase 2, "Design2")

The CV32E40P semantic-tier extension of the M0 cycle semantics: bit/element
selects (read and write, constant and dynamic index), constant part-selects,
replication, reduction operators, bitwise width conversion, signed
comparisons (`$signed` casts are same-width bit identities and vanish at
instantiation), `case` / `unique case` / `case … inside` (§12.5.4), and
**asynchronous active-low reset** event lists (`@(posedge clk or negedge
rst_n)` — the `[areset rn]` discipline every clocked CV32E40P module uses).

The M0 layer (`Ast.lean`/`Semantics.lean`) is **untouched**: this file
defines a superset AST (`Expr2`/`Lhs2`/`Stmt2`/`Process2`/`Design2`) and its
own interpreter, reusing the M0 value core (`Basic.lean`), state, schedule
oracle, `Res`, and the M0 operator evaluators. Instantiated sv-0.2 envelopes
lower into `Design2` via `PDesign.instantiate2` (`Param2.lean`).

## The differential ledger (rows first, rules second)

Every rule below was pinned on Xcelium 24.03 **and** Icarus Verilog (both
agreeing) before it was implemented; the `#guard` rows at the end of this
file replay the exact pinned facts (`scratchpad/rows/pin1–pin4.sv`, plus the
probe examples under `Examples/system-verilog/sem2/` in the phase-2 harness
`harness/sv/diff_test2.py`). `case … inside` is the one exception: Icarus
does not parse the construct at all, so its rows are Xcelium-verified only
(recorded gap).

* **Select read** (`v[i]`, `m[i]` on multi-dim packed): a select of `elemW`
  bits at offset `i*elemW`. An `x`/`z` bit in the index, or an out-of-range
  index, reads all-x (pin1 R02/R03/R05, pin2a W05). Multi-dim packed arrays
  are ONE bit vector; `m[i]` is the `elemW`-bit chunk (R04).
* **Select write**: an `x`/`z`-bit or out-of-range index writes NOTHING —
  the target holds (pin2a W01/W03/W06/W08, pin4 Z05). A known in-range index
  writes exactly the addressed bits (W02/W04).
* **Reductions**: `|`,`&`,`^` fold the bit tables of `Logic.or/and/xor`
  (so `|` with any 1 is 1, `&` with any 0 is 0, else x when any x/z);
  `~|`,`~&`,`~^`/`^~` are their negations (pin1 R08–R11, pin4 Z07).
* **Width conversion** (`Resize`): **bitwise**, never the arithmetic
  x-collapse — zero-extension keeps x bits, truncation keeps the low bits
  (pin4 Z01–Z04).
* **Signed comparison** (both operands signed, LRM §11.8.1): two's-
  complement compare; any x/z bit gives x (pin4 S01–S05). `$signed`/
  `$unsigned` at equal width changes no bits — the *operator* carries the
  signedness, so the casts vanish at instantiation.
* **Plain `case`** matches with **case equality** (`===`, exact 4-state:
  subject `xx` matches item `xx`, `x ≠ z`), first match wins, else
  `default`, else no-op (pin2a C01/C02).
* **`case … inside`** matches with wildcard equality `==?` (§12.5.4,
  §11.4.6): `x`/`z` bits in the ITEM are don't-cares; a subject `x`/`z` bit
  in a cared position is a non-match (falls through, `default` if nothing
  matches). Pin2b I01–I09 (Xcelium).
* **`unique`/`unique0`/`priority`** retain their check mode as data and select
  the first matching arm when the claim holds (pin2a C04/C05, pin2b I08/I09).
  The public `run2` path validates the selected settled state and returns the
  named loud result `CaseCheck:unique`, `CaseCheck:unique0`, or
  `CaseCheck:priority` on a violation; it never silently falls through to
  plain-case behavior. The low-level statement evaluator remains the
  structure-preserving first-match primitive used by the validator.
* **Async active-low reset** (`Process2.alwaysFFR`): the LRM two-edge
  sensitivity at cycle granularity. `cycleStep2` inserts a **reset-event
  phase** between the input comb-settle and the posedge phase: for each
  `alwaysFFR` process whose reset signal made a **negedge** transition
  (§9.4.2: `1→0`, `1→x/z`, `x/z→0`) between the end of the previous cycle
  and this cycle's settled inputs, the WHOLE body runs pre-edge (NBA
  discipline, then commit, then settle). Running the whole body — not just
  a reset branch — is load-bearing: on `rst_n: 1→x` the canonical body
  `if (!rst_n) … else …` takes the ELSE branch at the negedge event, so a
  downstream FF samples the *new* value at the same posedge (pin3 CYCLE 6,
  both simulators). Reset-assert pre-edge visibility is pin3 CYCLE 3/0: a
  same-cycle dependent FF samples the already-reset value. While reset
  stays asserted no new event fires, but the posedge still runs the body,
  whose reset branch holds the state (CYCLE 4). Reset DEassertion (`0→1`,
  `x→1`) is a posedge of `rst_n` and fires nothing (CYCLE 5/7).
  Level-vs-edge honesty: the phase is **edge-triggered** on the cycle
  boundary values (previous cycle's final value vs this cycle's settled
  value); sub-cycle reset pulses are not representable at cycle
  granularity — that is the granularity of the whole M0 scheduler, not a
  new approximation.
-/

namespace LeanModels.Sv

/-! ## Value-core additions (`LVec`) -/

namespace LVec

/-- Read `w` bits starting at bit `lo` (LSB-first). Positions beyond the
source width read `x` — the LRM's out-of-range select value. In-range
constant slices (`v[msb:lsb]` after instantiation) never hit the x-fill. -/
def extract (v : LVec) (lo w : Nat) : LVec :=
  ⟨.ofFn (n := w) fun i => v.bits[lo + i.val]?.getD .lx⟩

/-- Write `part` into `v` at bit offset `lo` (LSB-first); bits of `part`
that would land beyond `v`'s width are dropped (cannot arise from typed
sources). The select-write primitive. -/
def insertAt (v : LVec) (lo : Nat) (part : LVec) : LVec :=
  ⟨.ofFn (n := v.width) fun i =>
    if lo ≤ i.val ∧ i.val < lo + part.width then part.bits[i.val - lo]?.getD .lx
    else v.bits[i.val]?.getD .lx⟩

/-- Two's-complement value if fully known, else `none` (signed compare
support; width 0 gives 0). -/
def toInt? (v : LVec) : Option Int :=
  match v.toNat? with
  | none => none
  | some n =>
      if v.width == 0 then some 0
      else if n < 2 ^ (v.width - 1) then some (n : Int)
      else some ((n : Int) - (2 : Int) ^ v.width)

/-- Bitwise width conversion (implicit conversion of an unsigned operand,
LRM §10.7/§11.8.2): zero-extend or keep the low bits. **Not** the
arithmetic x-collapse — x/z bits pass through bit by bit (pin4 Z01–Z04). -/
def resizeU (v : LVec) (w : Nat) : LVec :=
  ⟨.ofFn (n := w) fun i => v.bits[i.val]?.getD .l0⟩

/-- Resizing a vector to its existing width is the identity.  This is the
canonical width bridge shared by the semantic and native E layers. -/
theorem resizeU_of_width {v : LVec} {w : Nat} (h : v.width = w) :
    v.resizeU w = v := by
  cases v with
  | mk bits =>
      simp only [resizeU, width] at h ⊢
      subst w
      congr 1
      apply Array.ext
      · simp
      · intro i hi hi'
        simp [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi']

/-- Replication `{n{v}}` (§11.4.12.1). -/
def replVec (n : Nat) (v : LVec) : LVec :=
  ⟨(Array.replicate n v.bits).flatten⟩

/-- Wildcard-equality case match (`==?` as a case-inside guard, §12.5.4 /
§11.4.6, restricted to same-width operands): item bits `x`/`z` are
don't-cares; every cared position must hold a *known, equal* subject bit.
A subject x/z bit in a cared position is a fall-through, exactly like a
definite mismatch (the `x` result of `==?` does not select a case arm). -/
def matchesWild (subj item : LVec) : Bool :=
  subj.eqWildcard item == .l1

end LVec

/-! ## The semantic-tier AST -/

/-- `case` statement check qualifier (§12.5.3). Kept as data so the
 structure-preserving statement evaluator can select arms without a rewrite;
 the public `run2` validator turns a violated claim into a named loud result. -/
inductive CaseCheck where
  | none | unique | unique0 | priority
deriving Repr, BEq, DecidableEq, Inhabited

/-- Matching mode for an integral case statement.  The constructor is shared
by the symbolic envelope and the instantiated semantic tier; qualifiers stay
in `CaseCheck` and do not alter execution. -/
inductive CaseMode where
  | normal | inside | casez | casex
deriving Repr, BEq, DecidableEq, Inhabited

def CaseMode.isNormal : CaseMode → Bool
  | .normal => true
  | _ => false

def CaseMode.isInside : CaseMode → Bool
  | .inside => true
  | _ => false

/-- Semantic-tier expressions: the M0 vocabulary plus selects, replication,
reductions, bitwise resize, and signed comparison. `scmp` ops are the four
order comparisons (`.lt/.le/.gt/.ge` of `BinOp`) with two's-complement
semantics — the extractor marks a comparison signed only when BOTH operands
are signed (§11.8.1); `$signed` casts at equal width change no bits and
vanish at instantiation. -/
inductive Expr2 where
  | resizeSigned (width : Nat) (operand : Expr2)
  /-- Convert x/z bits to zero at a 2-state storage boundary (§6.3.1). -/
  | squash2 (operand : Expr2)
  | lit (value : LVec)
  | ident (name : String)
  | unary (op : UnaryOp) (arg : Expr2)
  | binary (op : BinOp) (left right : Expr2)
  /-- Signed order comparison (`op` must be one of `.lt .le .gt .ge`). -/
  | scmp (op : BinOp) (left right : Expr2)
  /-- Logical `&&` / `||` (`isAnd` selects), §11.4.7: 1-bit result;
  definite-false (`&&`) / definite-true (`||`) operands decide even when
  the other side is x (pin5 L01–L12). -/
  | logical (isAnd : Bool) (left right : Expr2)
  | ternary (cond thenE elseE : Expr2)
  | concat (parts : Array Expr2)
  /-- Constant slice: `w` bits at LSB offset `lo` (an instantiated
  `v[msb:lsb]` or constant-index element select). -/
  | slice (base : Expr2) (lo w : Nat)
  /-- Dynamic element select: `elemW` bits at offset `index*elemW`
  (`elemW = 1` is a plain bit select). x/z or out-of-range index → all-x. -/
  | index (base : Expr2) (idx : Expr2) (elemW : Nat)
  | repl (count : Nat) (arg : Expr2)
  | reduce (op : RedOp) (arg : Expr2)
  /-- Bitwise width conversion of an unsigned operand (zero-extend /
  truncate). Signed widening resolves at instantiation or is loud. -/
  | resize (width : Nat) (arg : Expr2)
  | unsupported (svKind : String) (text : String)
deriving Repr, BEq, Inhabited

/-- Assignment targets: whole signal, constant slice, dynamic element select,
or a concatenation of direct leaves. Concatenations are used by continuous
assignments and are updated from one sampled RHS value. -/
inductive Lhs2 where
  | ident (name : String)
  | slice (name : String) (lo w : Nat)
  | index (name : String) (idx : Expr2) (elemW : Nat)
  | concat (parts : List Lhs2)
deriving Repr, BEq, Inhabited

/-- The written signal's name. -/
def Lhs2.name : Lhs2 → String
  | .ident n | .slice n _ _ | .index n _ _ => n
  | .concat (part :: _) => part.name
  | .concat [] => ""

mutual
/-- Semantic-tier statements: M0 shapes over `Expr2`/`Lhs2` plus `case`.
`items` are `CaseItem2`s in source order (a comma list is ONE item with
several patterns); `inside` selects wildcard matching (§12.5.4) over case
equality. -/
inductive Stmt2 where
  | blockingAssign (target : Lhs2) (value : Expr2)
  | nbaAssign (target : Lhs2) (value : Expr2)
  | ifStmt (cond : Expr2) (thenBranch : Stmt2) (elseBranch : Option Stmt2)
  | block (body : Array Stmt2)
  | caseStmt (subject : Expr2) (items : Array CaseItem2)
      (default? : Option Stmt2) (mode : CaseMode) (check : CaseCheck)
  | unsupported (svKind : String) (text : String)
deriving Repr, Inhabited

/-- One case arm: pattern list (source order) and body. -/
inductive CaseItem2 where
  | mk (pats : Array Expr2) (body : Stmt2)
deriving Repr, Inhabited
end

def CaseItem2.pats : CaseItem2 → Array Expr2 | .mk p _ => p
def CaseItem2.body : CaseItem2 → Stmt2 | .mk _ b => b

/-- Semantic-tier processes. `alwaysFFR` is
`always_ff @(posedge clock or negedge rstn)` — the async active-low reset
shape (see the module docstring's reset-event ledger). Continuous `assign`
targets may be selects (partial drivers: several assigns drive disjoint
slices of one signal, ff_one-style). -/
inductive Process2 where
  | alwaysFF (clock : String) (body : Stmt2)
  | alwaysPlain (clock : String) (body : Stmt2)
  | alwaysComb (body : Stmt2)
  | assign (target : Lhs2) (value : Expr2)
  | alwaysFFR (clock rstn : String) (body : Stmt2) (resetHigh : Bool := false)
  | unsupported (svKind : String) (text : String)
deriving Repr, Inhabited

/-- A semantic-tier design (same `Decl` record as M0 — multi-dim packed
declarations are ONE vector; element widths live in the select nodes). -/
structure Design2 where
  name : String
  decls : Array Decl
  processes : Array Process2
deriving Repr, Inhabited

def Design2.inputNames (d : Design2) : Array String :=
  d.decls.filterMap fun dc => if dc.isInput then some dc.name else none

def Design2.outputNames (d : Design2) : Array String :=
  d.decls.filterMap fun dc => if dc.isOutput then some dc.name else none

/-- Loud-node scan (harness early warning; the interpreter is loud
regardless, exactly like M0). -/
def Design2.hasUnsupported (d : Design2) : Bool :=
  d.processes.any fun p =>
    match p with
    | .unsupported _ _ => true
    | .alwaysFF _ s | .alwaysPlain _ s | .alwaysComb s | .alwaysFFR _ _ s _ => stmtHas s
    | .assign t e => lhsHas t || exprHas e
where
  exprHas : Expr2 → Bool
    | .unsupported _ _ => true
    | .lit _ | .ident _ => false
    | .unary _ a | .repl _ a | .reduce _ a | .resize _ a
    | .resizeSigned _ a | .squash2 a => exprHas a
    | .binary _ a b | .scmp _ a b | .logical _ a b => exprHas a || exprHas b
    | .ternary c a b => exprHas c || exprHas a || exprHas b
    | .slice a _ _ => exprHas a
    | .index a i _ => exprHas a || exprHas i
    | .concat ps => ps.attach.any fun ⟨p, _⟩ => exprHas p
  lhsHas : Lhs2 → Bool
    | .ident _ | .slice .. => false
    | .index _ i _ => exprHas i
    | .concat _ => false
  stmtHas : Stmt2 → Bool
    | .unsupported _ _ => true
    | .blockingAssign t e | .nbaAssign t e => lhsHas t || exprHas e
    | .ifStmt c t e =>
        exprHas c || stmtHas t || (match e with | some s => stmtHas s | none => false)
    | .block body => body.attach.any fun ⟨s, _⟩ => stmtHas s
    | .caseStmt subj items dflt _ _ =>
        exprHas subj
        || items.attach.any (fun ⟨it, _⟩ => caseItemHas it)
        || (match dflt with | some s => stmtHas s | none => false)
  caseItemHas : CaseItem2 → Bool
    | .mk pats body =>
        pats.attach.any (fun ⟨p, _⟩ => exprHas p) || stmtHas body

/-! ## Case matching -/

/-- One case guard: plain `case` uses case equality (`===`, exact 4-state
match — pin2a C01); `case … inside` uses wildcard equality (`==?` with
item-side don't-cares — pin2b). Either way a non-1 result falls through. -/
def caseHit : CaseMode → LVec → LVec → Bool
  | .normal, subj, item => subj == item
  | .inside, subj, item => LVec.matchesWild subj item
  | .casez, subj, item => LVec.matchesCase false subj item
  | .casex, subj, item => LVec.matchesCase true subj item

/-! ## The NBA queue

Semantic-tier NBA entries carry the resolved write window: `(name, lo,
part)`. An assign whose dynamic index is x/z/out-of-range enqueues nothing
(the pinned no-op rule) — resolution happens at ISSUE time, like the RHS
evaluation (§10.4.2). -/

abbrev NbaQueue2 := List (String × Nat × LVec)

/- The root marker is deliberately separate from the value bits: symbolic
substitution may replace the operand while the select still has the source
declaration's signedness. -/
def Expr2.indexSigned : Expr2 → Bool
  | .resizeSigned _ _ => true
  | _ => false

/-- Read a dynamic select index using the source expression's signedness.
`resizeSigned` is the width-preserving marker emitted for a signed
declaration or `$signed` index; an unmarked index follows the unsigned
`toNat?` rule. -/
def indexInt? (idx : Expr2) (v : LVec) : Option Int :=
  if idx.indexSigned then v.toInt? else v.toNat?.map Int.ofNat

theorem indexInt?_congr {a b : Expr2} {v : LVec}
    (h : a.indexSigned = b.indexSigned) : indexInt? a v = indexInt? b v := by
  simp [indexInt?, h]

/-- Commit in issue order; last write to overlapping bits wins. -/
def commitNba2 (st : SvState) (nba : NbaQueue2) : SvState :=
  nba.foldl
    (fun s (u : String × Nat × LVec) =>
      match SvState.lookup s u.1 with
      | some old => SvState.set s u.1 (old.insertAt u.2.1 u.2.2)
      | none => s)
    st




/-! ## Qualified-case obligations

`CaseCheck` is retained metadata.  A qualified case cannot silently acquire
plain-case semantics on a violating input: before a process executes, the
validator below checks the selected case's match set and returns a named loud
result when `unique`, `unique0`, or `priority` is violated.  Ordinary cases
take the old execution path unchanged. -/

mutual
def Stmt2.hasQualifiedCase : Stmt2 → Bool
  | .caseStmt _ items dflt _ check =>
      check != .none
      || CaseItem2.listHasQualifiedCase items.toList
      || (match dflt with | some s => s.hasQualifiedCase | none => false)
  | .ifStmt _ t e => t.hasQualifiedCase || (match e with | some s => s.hasQualifiedCase | none => false)
  | .block body => Stmt2.listHasQualifiedCase body.toList
  | .blockingAssign _ _ | .nbaAssign _ _ | .unsupported _ _ => false

def Stmt2.listHasQualifiedCase : List Stmt2 → Bool
  | [] => false
  | s :: rest => s.hasQualifiedCase || Stmt2.listHasQualifiedCase rest

def CaseItem2.listHasQualifiedCase : List CaseItem2 → Bool
  | [] => false
  | .mk _ body :: rest => body.hasQualifiedCase || CaseItem2.listHasQualifiedCase rest
end

/-! ## Phase classification -/

/-- Comb-phase processes (`unsupported` scheduled here for loudness — the
M0 rule). -/
def Process2.isCombPhase : Process2 → Bool
  | .alwaysComb _ | .assign _ _ | .unsupported _ _ => true
  | .alwaysFF _ _ | .alwaysPlain _ _ | .alwaysFFR _ _ _ _ => false

/-- Edge-phase processes: every posedge-clocked block, INCLUDING the
async-reset ones (the posedge fires with reset asserted too — the body's
reset branch is what holds the state, pin3 CYCLE 4). -/
def Process2.isEdgePhase : Process2 → Bool
  | .alwaysFF _ _ | .alwaysPlain _ _ | .alwaysFFR _ _ _ _ => true
  | _ => false

def Process2.hasQualifiedCase : Process2 → Bool
  | .alwaysComb body | .alwaysFF _ body | .alwaysPlain _ body | .alwaysFFR _ _ body _ => body.hasQualifiedCase
  | .assign _ _ | .unsupported _ _ => false

def Design2.combIndices (d : Design2) : List Nat :=
  (List.range d.processes.size).filter fun i =>
    match d.processes[i]? with
    | some p => p.isCombPhase
    | none => false

def Design2.edgeIndices (d : Design2) : List Nat :=
  (List.range d.processes.size).filter fun i =>
    match d.processes[i]? with
    | some p => p.isEdgePhase
    | none => false


def Design2.resetIndices (d : Design2) (prev cur : SvState) : List Nat :=
  (List.range d.processes.size).filter fun i =>
    match d.processes[i]? with
    | some (.alwaysFFR _ rn _ resetHigh) =>
        if resetHigh then isPosedge (SvState.bit0 prev rn) (SvState.bit0 cur rn)
        else isNegedge (SvState.bit0 prev rn) (SvState.bit0 cur rn)
    | _ => false


end LeanModels.Sv
