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
* **`unique`/`unique0`/`priority`** do not change execution: the first
  matching arm runs; a violation (multiple matches / no match) is a
  simulator *warning* only (pin2a C04/C05, pin2b I08/I09). `Design2` keeps
  the check mode as data — the disjointness/completeness CLAIMS are future
  proof obligations at spec level, not simulation behavior.
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

/-- Reduction `|`: fold of the `Logic.or` table (identity `0`) — `1` if any
bit is 1, `0` if all bits 0, else `x`; width-0 gives `0`. -/
def redOr (v : LVec) : Logic := v.bits.foldl Logic.or .l0

/-- Reduction `&`: fold of the `Logic.and` table (identity `1`). -/
def redAnd (v : LVec) : Logic := v.bits.foldl Logic.and .l1

/-- Reduction `^`: fold of the `Logic.xor` table (identity `0`). -/
def redXor (v : LVec) : Logic := v.bits.foldl Logic.xor .l0

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

/-- Replication `{n{v}}` (§11.4.12.1). -/
def replVec (n : Nat) (v : LVec) : LVec :=
  ⟨(Array.replicate n v.bits).flatten⟩

/-- Wildcard-equality case match (`==?` as a case-inside guard, §12.5.4 /
§11.4.6, restricted to same-width operands): item bits `x`/`z` are
don't-cares; every cared position must hold a *known, equal* subject bit.
A subject x/z bit in a cared position is a fall-through, exactly like a
definite mismatch (the `x` result of `==?` does not select a case arm). -/
def matchesWild (subj item : LVec) : Bool :=
  subj.width == item.width &&
  (Array.zip subj.bits item.bits).all fun (s, p) =>
    !p.isKnown || (s.isKnown && s == p)

end LVec

/-! ## The semantic-tier AST -/

/-- Reduction operators (`| & ^ ~| ~& ~^`). -/
inductive RedOp where
  | or | and | xor | nor | nand | xnor
deriving Repr, BEq, DecidableEq, Inhabited

/-- Evaluate a reduction (negated forms via `Logic.not`). -/
def evalRedOp : RedOp → LVec → Logic
  | .or, v => v.redOr
  | .and, v => v.redAnd
  | .xor, v => v.redXor
  | .nor, v => v.redOr.not
  | .nand, v => v.redAnd.not
  | .xnor, v => v.redXor.not

/-- `case` statement check qualifier (§12.5.3). Execution-irrelevant in
this tier (violations are simulator warnings, pinned as such); kept as
data because `unique`'s disjointness/completeness claims become proof
obligations at spec level. -/
inductive CaseCheck where
  | none | unique | unique0 | priority
deriving Repr, BEq, DecidableEq, Inhabited

/-- Semantic-tier expressions: the M0 vocabulary plus selects, replication,
reductions, bitwise resize, and signed comparison. `scmp` ops are the four
order comparisons (`.lt/.le/.gt/.ge` of `BinOp`) with two's-complement
semantics — the extractor marks a comparison signed only when BOTH operands
are signed (§11.8.1); `$signed` casts at equal width change no bits and
vanish at instantiation. -/
inductive Expr2 where
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

/-- Assignment targets: whole signal, constant slice, or dynamic element
select (index evaluated at execution time; x/z or out-of-range index writes
nothing — the target holds). -/
inductive Lhs2 where
  | ident (name : String)
  | slice (name : String) (lo w : Nat)
  | index (name : String) (idx : Expr2) (elemW : Nat)
deriving Repr, BEq, Inhabited

/-- The written signal's name. -/
def Lhs2.name : Lhs2 → String
  | .ident n | .slice n _ _ | .index n _ _ => n

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
      (default? : Option Stmt2) (inside : Bool) (check : CaseCheck)
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
  | alwaysFFR (clock rstn : String) (body : Stmt2)
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
    | .alwaysFF _ s | .alwaysPlain _ s | .alwaysComb s | .alwaysFFR _ _ s => stmtHas s
    | .assign t e => lhsHas t || exprHas e
where
  exprHas : Expr2 → Bool
    | .unsupported _ _ => true
    | .lit _ | .ident _ => false
    | .unary _ a | .repl _ a | .reduce _ a | .resize _ a => exprHas a
    | .binary _ a b | .scmp _ a b | .logical _ a b => exprHas a || exprHas b
    | .ternary c a b => exprHas c || exprHas a || exprHas b
    | .slice a _ _ => exprHas a
    | .index a i _ => exprHas a || exprHas i
    | .concat ps => ps.attach.any fun ⟨p, _⟩ => exprHas p
  lhsHas : Lhs2 → Bool
    | .ident _ | .slice .. => false
    | .index _ i _ => exprHas i
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
def caseHit (inside : Bool) (subj item : LVec) : Bool :=
  if inside then LVec.matchesWild subj item
  else subj == item

/-! ## The NBA queue

Semantic-tier NBA entries carry the resolved write window: `(name, lo,
part)`. An assign whose dynamic index is x/z/out-of-range enqueues nothing
(the pinned no-op rule) — resolution happens at ISSUE time, like the RHS
evaluation (§10.4.2). -/

abbrev NbaQueue2 := List (String × Nat × LVec)

/-- Commit in issue order; last write to overlapping bits wins. -/
def commitNba2 (st : SvState) (nba : NbaQueue2) : SvState :=
  nba.foldl
    (fun s (u : String × Nat × LVec) =>
      match SvState.lookup s u.1 with
      | some old => SvState.set s u.1 (old.insertAt u.2.1 u.2.2)
      | none => s)
    st

/-! ## The fueled interpreter core -/

mutual

/-- Evaluate a semantic-tier expression (M0 discipline: fuel matched
first, decremented into every recursive call; both ternary arms evaluated;
loud on `unsupported` nodes reached). -/
def evalExpr2 (fuel : Nat) (st : SvState) (e : Expr2) : Res LVec :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match e with
    | .lit v => .ok v
    | .ident name => readSignal st name
    | .unary op a => do
        return evalUnaryOp op (← evalExpr2 fuel st a)
    | .binary op l r => do
        let a ← evalExpr2 fuel st l
        let b ← evalExpr2 fuel st r
        return evalBinOp op a b
    | .scmp op l r => do
        let a ← evalExpr2 fuel st l
        let b ← evalExpr2 fuel st r
        match a.toInt?, b.toInt? with
        | some x, some y =>
            return .ofLogic (match op with
              | .lt => if x < y then .l1 else .l0
              | .le => if x ≤ y then .l1 else .l0
              | .gt => if x > y then .l1 else .l0
              | .ge => if x ≥ y then .l1 else .l0
              | _ => .lx)  -- non-order op: outside the constructor contract
        | _, _ => return .ofLogic .lx
    | .logical isAnd l r => do
        let a ← evalExpr2 fuel st l
        let b ← evalExpr2 fuel st r
        let res : Logic :=
          if isAnd then
            if a.isKnownZero || b.isKnownZero then .l0
            else if a.condTrue && b.condTrue then .l1
            else .lx
          else
            if a.condTrue || b.condTrue then .l1
            else if a.isKnownZero && b.isKnownZero then .l0
            else .lx
        return .ofLogic res
    | .ternary c t f => do
        let cv ← evalExpr2 fuel st c
        let tv ← evalExpr2 fuel st t
        let fv ← evalExpr2 fuel st f
        return LVec.ternary cv tv fv
    | .concat parts => do
        let vs ← evalExprs2 fuel st parts.toList
        return LVec.concatMany vs.toArray
    | .slice base lo w => do
        return (← evalExpr2 fuel st base).extract lo w
    | .index base idx elemW => do
        let bv ← evalExpr2 fuel st base
        let iv ← evalExpr2 fuel st idx
        match iv.toNat? with
        | some i =>
            if (i + 1) * elemW ≤ bv.width then
              return bv.extract (i * elemW) elemW
            else
              return LVec.xVec elemW      -- out-of-range read: all-x (W05)
        | none => return LVec.xVec elemW  -- x/z index read: all-x (R02/R03/R05)
    | .repl n a => do
        return LVec.replVec n (← evalExpr2 fuel st a)
    | .reduce op a => do
        return .ofLogic (evalRedOp op (← evalExpr2 fuel st a))
    | .resize w a => do
        return (← evalExpr2 fuel st a).resizeU w
    | .unsupported svKind _ => .unsupported s!"unsupported expression '{svKind}'"

def evalExprs2 (fuel : Nat) (st : SvState) (es : List Expr2) : Res (List LVec) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match es with
    | [] => .ok []
    | e :: rest => do
        let v ← evalExpr2 fuel st e
        let vs ← evalExprs2 fuel st rest
        return v :: vs

/-- Resolve an assignment target to its write window `(name, lo, width)` —
`none` window = the pinned no-write case (x/z or out-of-range dynamic
index; the statement is still executed for its RHS side… M0 expressions are
pure, so "executed" just means the assignment is dropped). -/
def resolveLhs2 (fuel : Nat) (st : SvState) : Lhs2 → Res (String × Option (Nat × Nat))
  | .ident n => do
      match SvState.lookup st n with
      | some old => return (n, some (0, old.width))
      | none => .unsupported s!"unknown assignment target '{n}'"
  | .slice n lo w => .ok (n, some (lo, w))
  | .index n idx elemW => do
      let iv ← evalExpr2 fuel st idx
      match SvState.lookup st n with
      | none => .unsupported s!"unknown assignment target '{n}'"
      | some old =>
          match iv.toNat? with
          | some i =>
              if (i + 1) * elemW ≤ old.width then
                return (n, some (i * elemW, elemW))
              else
                return (n, none)  -- OOB write: no-op (Z05)
          | none => return (n, none)  -- x/z-index write: no-op (W01/W03/W06/W08)

/-- Execute one statement (blocking hits the state via `insertAt`;
nonblocking enqueues the resolved window; `case` per `caseHit`, first
match, `default`, else no-op — check qualifiers do not alter execution). -/
def execStmt2 (fuel : Nat) (st : SvState) (nba : NbaQueue2) (stmt : Stmt2) :
    Res (SvState × NbaQueue2) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match stmt with
    | .blockingAssign target value => do
        let v ← evalExpr2 fuel st value
        let (n, win) ← resolveLhs2 fuel st target
        match win with
        | none => return (st, nba)
        | some (lo, w) =>
            match SvState.lookup st n with
            | some old => return (SvState.set st n (old.insertAt lo (v.resizeU w)), nba)
            | none => .unsupported s!"unknown assignment target '{n}'"
    | .nbaAssign target value => do
        let v ← evalExpr2 fuel st value
        let (n, win) ← resolveLhs2 fuel st target
        match win with
        | none => return (st, nba)
        | some (lo, w) => return (st, nba ++ [(n, lo, v.resizeU w)])
    | .ifStmt cond thenBranch elseBranch => do
        let c ← evalExpr2 fuel st cond
        if c.condTrue then
          execStmt2 fuel st nba thenBranch
        else
          match elseBranch with
          | some s => execStmt2 fuel st nba s
          | none => .ok (st, nba)
    | .caseStmt subject items default? inside _check => do
        let sv ← evalExpr2 fuel st subject
        execCase2 fuel st nba sv items.toList default? inside
    | .block body => execStmts2 fuel st nba body.toList
    | .unsupported svKind _ => .unsupported s!"unsupported statement '{svKind}'"

/-- Walk the case items in source order; first hit executes; exhausted
items fall to `default` (no default: no-op — pin2a C05 / pin2b I09). -/
def execCase2 (fuel : Nat) (st : SvState) (nba : NbaQueue2) (subj : LVec) :
    List CaseItem2 → Option Stmt2 → Bool → Res (SvState × NbaQueue2)
  | [], default?, _ =>
      match fuel with
      | 0 => .timeout
      | fuel + 1 =>
          match default? with
          | some s => execStmt2 fuel st nba s
          | none => .ok (st, nba)
  | .mk pats body :: rest, default?, inside =>
      match fuel with
      | 0 => .timeout
      | fuel + 1 => do
          let pvs ← evalExprs2 fuel st pats.toList
          if pvs.any (fun pv => caseHit inside subj pv) then
            execStmt2 fuel st nba body
          else
            execCase2 fuel st nba subj rest default? inside

def execStmts2 (fuel : Nat) (st : SvState) (nba : NbaQueue2) (ss : List Stmt2) :
    Res (SvState × NbaQueue2) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match ss with
    | [] => .ok (st, nba)
    | s :: rest => do
        let (st', nba') ← execStmt2 fuel st nba s
        execStmts2 fuel st' nba' rest

end

/-! ## Phase classification -/

/-- Comb-phase processes (`unsupported` scheduled here for loudness — the
M0 rule). -/
def Process2.isCombPhase : Process2 → Bool
  | .alwaysComb _ | .assign _ _ | .unsupported _ _ => true
  | .alwaysFF _ _ | .alwaysPlain _ _ | .alwaysFFR _ _ _ => false

/-- Edge-phase processes: every posedge-clocked block, INCLUDING the
async-reset ones (the posedge fires with reset asserted too — the body's
reset branch is what holds the state, pin3 CYCLE 4). -/
def Process2.isEdgePhase : Process2 → Bool
  | .alwaysFF _ _ | .alwaysPlain _ _ | .alwaysFFR _ _ _ => true
  | _ => false

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

/-! ## Comb settle -/

/-- Run one comb-phase process (continuous assigns may target selects —
partial drivers read-modify-write their slice; several assigns driving
disjoint slices of one signal settle to the union, undriven bits stay x). -/
def runCombProcess2 (fuel : Nat) (st : SvState) : Process2 → Res SvState
  | .assign target value => do
      let v ← evalExpr2 fuel st value
      let (n, win) ← resolveLhs2 fuel st target
      match win with
      | none => .ok st
      | some (lo, w) =>
          match SvState.lookup st n with
          | some old => .ok (SvState.set st n (old.insertAt lo (v.resizeU w)))
          | none => .unsupported s!"unknown assign target '{n}'"
  | .alwaysComb body => do
      let (st', nba) ← execStmt2 fuel st [] body
      match nba with
      | [] => .ok st'
      | (name, _) :: _ =>
          .unsupported
            s!"nonblocking assignment to '{name}' inside always_comb is outside the cycle semantics"
  | .alwaysFF _ _ | .alwaysPlain _ _ | .alwaysFFR _ _ _ => .ok st
  | .unsupported svKind _ => .unsupported s!"unsupported process '{svKind}'"

def combPass2 (d : Design2) (fuel : Nat) (st : SvState) : List Nat → Res SvState
  | [] => .ok st
  | i :: rest => do
      let st' ← match d.processes[i]? with
        | some p => runCombProcess2 fuel st p
        | none => pure st
      combPass2 d fuel st' rest

/-- σ-ordered settle passes to fixpoint, fuel-bounded (M0 discipline). -/
def combSettle2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (st : SvState)
    (k : Nat) : Res (SvState × Nat) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 => do
      let st' ← combPass2 d fuel st (σ.choose k d.combIndices)
      if st' == st then .ok (st', k + 1)
      else combSettle2 d σ fuel st' (k + 1)

/-! ## Reset-event phase -/

/-! `isNegedge` and `SvState.bit0` were defined HERE and are now in `Basic`
and `Semantics` respectively. The region tier needs the same two, and it
sits BELOW this module in the import graph, so a copy was made — and the
copy disagreed with this original on the `x`/`z` cases. Moving them down
is what makes the two tiers agree by construction. Nothing else changes:
the names are unqualified and identical, so `resetIndices` below reads the
same rule it always did. -/

/-- Indices of `alwaysFFR` processes whose reset input made a §9.4.2
negedge between `prev` (end of previous cycle) and `cur` (this cycle's
settled inputs) — the ready set of the reset-event phase. -/
def Design2.resetIndices (d : Design2) (prev cur : SvState) : List Nat :=
  (List.range d.processes.size).filter fun i =>
    match d.processes[i]? with
    | some (.alwaysFFR _ rn _) => isNegedge (SvState.bit0 prev rn) (SvState.bit0 cur rn)
    | _ => false

/-- Run one process at a reset event (only `alwaysFFR` bodies are ever
listed). The WHOLE body runs — on `rst_n: 1→x` the canonical
`if (!rst_n)` takes the else branch at the event (pin3 CYCLE 6). -/
def runResetProcess2 (fuel : Nat) (st : SvState) (nba : NbaQueue2) :
    Process2 → Res (SvState × NbaQueue2)
  | .alwaysFFR _ _ body => execStmt2 fuel st nba body
  | _ => .ok (st, nba)

def resetPass2 (d : Design2) (fuel : Nat) (st : SvState) (nba : NbaQueue2) :
    List Nat → Res (SvState × NbaQueue2)
  | [] => .ok (st, nba)
  | i :: rest => do
      let (st', nba') ← match d.processes[i]? with
        | some p => runResetProcess2 fuel st nba p
        | none => pure (st, nba)
      resetPass2 d fuel st' nba' rest

/-! ## Edge phase -/

def runEdgeProcess2 (fuel : Nat) (st : SvState) (nba : NbaQueue2) :
    Process2 → Res (SvState × NbaQueue2)
  | .alwaysFF _ body => execStmt2 fuel st nba body
  | .alwaysPlain _ body => execStmt2 fuel st nba body
  | .alwaysFFR _ _ body => execStmt2 fuel st nba body
  | .alwaysComb _ | .assign _ _ => .ok (st, nba)
  | .unsupported svKind _ => .unsupported s!"unsupported process '{svKind}'"

def edgePass2 (d : Design2) (fuel : Nat) (st : SvState) (nba : NbaQueue2) :
    List Nat → Res (SvState × NbaQueue2)
  | [] => .ok (st, nba)
  | i :: rest => do
      let (st', nba') ← match d.processes[i]? with
        | some p => runEdgeProcess2 fuel st nba p
        | none => pure (st, nba)
      edgePass2 d fuel st' nba' rest

/-! ## The cycle -/

def applyInputs2 (d : Design2) (inputs : SvState) (st : SvState) : SvState :=
  d.inputNames.foldl
    (fun s name =>
      match SvState.lookup inputs name with
      | some v => SvState.set s name v
      | none => s)
    st

def initState2 (d : Design2) : SvState :=
  d.decls.toList.map fun dc => (dc.name, dc.init.getD (LVec.xVec dc.width))

/-- One clock cycle of the semantic tier — the M0 five sub-steps with the
reset-event phase inserted between the input settle and the posedge:

1. overwrite declared inputs from the stimulus;
2. comb settle;
3. **reset-event phase**: `alwaysFFR` bodies whose reset made a negedge
   (vs. the end of the previous cycle) run once in σ order, NBA committed,
   comb settled — reset values are visible to the posedge samplers (pin3);
4. edge phase: every posedge process runs once in σ order;
5. NBA commit; 6. comb settle. The result is the cycle's snapshot. -/
def cycleStep2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (inputs : SvState)
    (st : SvState) (k : Nat := 0) : Res (SvState × Nat) := do
  let st0 := applyInputs2 d inputs st
  let (st1, k1) ← combSettle2 d σ fuel st0 k
  let rdy := d.resetIndices st st1
  let (st2, k2) ←
    match rdy with
    | [] => pure (st1, k1)
    | _ => do
        let (str, nbar) ← resetPass2 d fuel st1 [] (σ.choose k1 rdy)
        combSettle2 d σ fuel (commitNba2 str nbar) (k1 + 1)
  let (st3, nba) ← edgePass2 d fuel st2 [] (σ.choose k2 d.edgeIndices)
  let st4 := commitNba2 st3 nba
  combSettle2 d σ fuel st4 (k2 + 1)

def runFrom2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (st : SvState)
    (k : Nat) : List SvState → Res (List SvState)
  | [] => .ok []
  | inputs :: rest => do
      let (st', k') ← cycleStep2 d σ fuel inputs st k
      let tr ← runFrom2 d σ fuel st' k' rest
      return st' :: tr

/-- The semantic-tier entry point (M0 contract shape: startup from
declaration initializers, all else x; one snapshot per stimulus entry). -/
def run2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (stim : List SvState) :
    Res (List SvState) :=
  runFrom2 d σ fuel (initState2 d) 0 stim

/-! ## The pinned-fact table (`#guard` twins of the diff rows)

Row ids refer to the pin probes in the module docstring; every row was
green on Xcelium AND Icarus before the rule landed (case-inside rows:
Xcelium only — Icarus cannot parse the construct). -/

-- pin1 R01–R03: dynamic bit select; x/z index reads x.
private def v86 : LVec := .lit "10100110"
#guard evalExpr2 32 [] (.index (.lit v86) (.lit (.ofNat 3 2)) 1) == .ok (.lit "1")
#guard evalExpr2 32 [] (.index (.lit v86) (.lit (.lit "xxx")) 1) == .ok (.lit "x")
#guard evalExpr2 32 [] (.index (.lit v86) (.lit (.lit "01x")) 1) == .ok (.lit "x")

-- pin1 R04–R05: 2D element select m[i] = 8-bit chunk; x index → all-x.
private def m4x8 : LVec := .lit "10100001101100101100001111010100"  -- 32'hA1B2C3D4
#guard (evalExpr2 32 [] (.index (.lit m4x8) (.lit (.ofNat 2 3)) 8)).toOption.map
        LVec.toBinString == some "10100001"
#guard (evalExpr2 32 [] (.index (.lit m4x8) (.lit (.lit "xx")) 8)).toOption.map
        LVec.toBinString == some "xxxxxxxx"

-- pin2a W05: out-of-range dynamic read → x.
#guard (evalExpr2 32 [] (.index (.lit v86) (.lit (.ofNat 4 9)) 1)) == .ok (.lit "x")

-- pin1 R06: constant part select v[6:3].
#guard (evalExpr2 32 [] (.slice (.lit v86) 3 4)).toOption.map LVec.toBinString
        == some "0100"

-- pin1 R07 / pin4 Z06: replication.
#guard (evalExpr2 32 [] (.repl 3 (.lit (.lit "10")))).toOption.map LVec.toBinString
        == some "101010"
#guard (evalExpr2 32 [] (.repl 2 (.lit (.lit "1x")))).toOption.map LVec.toBinString
        == some "1x1x"

-- pin1 R08–R11, pin4 Z07: reductions.
#guard evalRedOp .or (.lit "00000000") == .l0
#guard evalRedOp .or (.lit "000x0000") == .lx
#guard evalRedOp .or (.lit "100x0000") == .l1
#guard evalRedOp .and (.lit "11111111") == .l1
#guard evalRedOp .and (.lit "11111110") == .l0
#guard evalRedOp .and (.lit "1111111x") == .lx
#guard evalRedOp .xor (.lit "10110000") == .l1
#guard evalRedOp .xor (.lit "1011000x") == .lx
#guard evalRedOp .nor (.lit "00000000") == .l1
#guard evalRedOp .nand (.lit "11111111") == .l0
#guard evalRedOp .or (.lit "zz") == .lx
#guard evalRedOp .and (.lit "zz") == .lx

-- pin4 S01–S05: signed comparison; $signed at equal width is bit identity.
#guard (evalExpr2 32 [] (.scmp .lt (.lit (.ofNat 8 0xFF)) (.lit (.ofNat 8 1))))
        == .ok (.lit "1")
#guard (evalExpr2 32 [] (.binary .lt (.lit (.ofNat 8 0xFF)) (.lit (.ofNat 8 1))))
        == .ok (.lit "0")
#guard (evalExpr2 32 [] (.scmp .ge (.lit (.ofNat 8 0xFF)) (.lit (.ofNat 8 1))))
        == .ok (.lit "0")
#guard (evalExpr2 32 [] (.scmp .lt (.lit (.ofNat 8 0x80)) (.lit (.ofNat 8 0x7F))))
        == .ok (.lit "1")
#guard (evalExpr2 32 [] (.scmp .lt (.lit (.lit "x1111111")) (.lit (.ofNat 8 0x7F))))
        == .ok (.lit "x")

-- pin5 L01–L12: logical && / || (definite-false/true short-outs, else x).
#guard evalExpr2 8 [] (.logical true (.lit (.lit "00")) (.lit (.lit "xx"))) == .ok (.lit "0")
#guard evalExpr2 8 [] (.logical true (.lit (.lit "xx")) (.lit (.lit "00"))) == .ok (.lit "0")
#guard evalExpr2 8 [] (.logical true (.lit (.lit "10")) (.lit (.lit "xx"))) == .ok (.lit "x")
#guard evalExpr2 8 [] (.logical true (.lit (.lit "10")) (.lit (.lit "01"))) == .ok (.lit "1")
#guard evalExpr2 8 [] (.logical true (.lit (.lit "0x")) (.lit (.lit "10"))) == .ok (.lit "x")
#guard evalExpr2 8 [] (.logical true (.lit (.lit "zz")) (.lit (.lit "10"))) == .ok (.lit "x")
#guard evalExpr2 8 [] (.logical false (.lit (.lit "10")) (.lit (.lit "xx"))) == .ok (.lit "1")
#guard evalExpr2 8 [] (.logical false (.lit (.lit "xx")) (.lit (.lit "01"))) == .ok (.lit "1")
#guard evalExpr2 8 [] (.logical false (.lit (.lit "00")) (.lit (.lit "00"))) == .ok (.lit "0")
#guard evalExpr2 8 [] (.logical false (.lit (.lit "xx")) (.lit (.lit "00"))) == .ok (.lit "x")

-- pin4 Z01–Z04: bitwise resize (zero-extend keeps x bits; truncate keeps
-- low bits) — never the arithmetic collapse.
#guard (LVec.resizeU (.lit "1010") 12).toBinString == "000000001010"
#guard (LVec.resizeU (.lit "10100101") 4).toBinString == "0101"
#guard (LVec.resizeU (.lit "x1x0") 12).toBinString == "00000000x1x0"
#guard (LVec.resizeU (.lit "1x000101") 4).toBinString == "0101"

-- pin2a W01/W02/W06/W08 + pin4 Z05: select writes (x/z/OOB index = no-op).
private def wrProbe (idx : String) : Res (SvState × NbaQueue2) :=
  execStmt2 32 [("v", LVec.ofNat 8 0x0F)] []
    (.blockingAssign (.index "v" (.lit (.lit idx)) 1) (.lit (.lit "1")))
#guard (wrProbe "xxx").toOption.map (fun (st, _) => SvState.showSignal st "v")
        == some "00001111"
#guard (wrProbe "110").toOption.map (fun (st, _) => SvState.showSignal st "v")
        == some "01001111"
#guard (wrProbe "zzz").toOption.map (fun (st, _) => SvState.showSignal st "v")
        == some "00001111"
#guard (wrProbe "1x0").toOption.map (fun (st, _) => SvState.showSignal st "v")
        == some "00001111"
#guard (execStmt2 32 [("v", LVec.ofNat 8 0x0F)] []
          (.blockingAssign (.index "v" (.lit (.ofNat 5 20)) 1) (.lit (.lit "1")))).toOption.map
        (fun (st, _) => SvState.showSignal st "v") == some "00001111"

-- pin2a W03/W04: element write via x index no-op; known index hits chunk.
#guard (execStmt2 32 [("m", LVec.lit "00010001001000100011001101000100")] []
          (.blockingAssign (.index "m" (.lit (.lit "xx")) 8) (.lit (.ofNat 8 0xFF)))).toOption.map
        (fun (st, _) => SvState.showSignal st "m")
        == some "00010001001000100011001101000100"
#guard (execStmt2 32 [("m", LVec.lit "00010001001000100011001101000100")] []
          (.blockingAssign (.index "m" (.lit (.ofNat 2 1)) 8) (.lit (.ofNat 8 0xFF)))).toOption.map
        (fun (st, _) => SvState.showSignal st "m")
        == some "00010001001000101111111101000100"

-- pin2a C01–C05: plain case = case equality (x matches x); expression
-- labels; unique does not change execution (first match; no match+no
-- default = no-op).
private def oSet (v : Nat) : Stmt2 := .blockingAssign (.ident "o") (.lit (.ofNat 2 v))
private def caseProbe (subj : String) (items : Array CaseItem2)
    (dflt : Option Stmt2) (inside : Bool := false) : Option String :=
  (execStmt2 64 [("s", LVec.lit subj), ("o", LVec.xVec 2)] []
    (.caseStmt (.ident "s") items dflt inside .none)).toOption.map
    fun (st, _) => SvState.showSignal st "o"
#guard caseProbe "xx"
        #[.mk #[.lit (.lit "00")] (oSet 0), .mk #[.lit (.lit "xx")] (oSet 1)]
        (some (oSet 2))
        == some "01"
#guard caseProbe "0x"
        #[.mk #[.lit (.lit "00")] (oSet 0), .mk #[.lit (.lit "01")] (oSet 1)]
        (some (oSet 3))
        == some "11"
-- fifo style: case (1'b1) with signal labels, first match wins.
#guard (execStmt2 64 [("s", LVec.lit "11"), ("p", LVec.xVec 3)] []
          (.caseStmt (.lit (.lit "1"))
            #[.mk #[.index (.ident "s") (.lit (.ofNat 1 0)) 1]
                (.blockingAssign (.ident "p") (.lit (.ofNat 3 1))),
              .mk #[.index (.ident "s") (.lit (.ofNat 1 1)) 1]
                (.blockingAssign (.ident "p") (.lit (.ofNat 3 2)))]
            (some (.blockingAssign (.ident "p") (.lit (.ofNat 3 7)))) false .unique)).toOption.map
        (fun (st, _) => SvState.showSignal st "p") == some "001"
#guard (execStmt2 64 [("s", LVec.lit "00"), ("p", LVec.ofNat 3 5)] []
          (.caseStmt (.lit (.lit "1"))
            #[.mk #[.index (.ident "s") (.lit (.ofNat 1 0)) 1]
                (.blockingAssign (.ident "p") (.lit (.ofNat 3 1))),
              .mk #[.index (.ident "s") (.lit (.ofNat 1 1)) 1]
                (.blockingAssign (.ident "p") (.lit (.ofNat 3 2)))]
            none false .unique)).toOption.map
        (fun (st, _) => SvState.showSignal st "p") == some "101"

-- pin2b I01–I09: case inside (wildcard match, item-side don't-cares;
-- subject x in a cared position falls through; comma lists).
#guard caseProbe "10"
        #[.mk #[.lit (.lit "0z")] (oSet 0), .mk #[.lit (.lit "1z")] (oSet 1)]
        (some (oSet 2)) true == some "01"
#guard caseProbe "0x"
        #[.mk #[.lit (.lit "00")] (oSet 0), .mk #[.lit (.lit "01")] (oSet 1)]
        (some (oSet 2)) true == some "10"
#guard caseProbe "1x"
        #[.mk #[.lit (.lit "0z")] (oSet 0), .mk #[.lit (.lit "1z")] (oSet 1)]
        (some (oSet 2)) true == some "01"
#guard caseProbe "10"
        #[.mk #[.lit (.lit "1x")] (oSet 1)]
        (some (oSet 2)) true == some "01"
#guard caseProbe "01"
        #[.mk #[.lit (.lit "00"), .lit (.lit "01")] (oSet 0)]
        (some (oSet 2)) true == some "00"
#guard caseProbe "z0"
        #[.mk #[.lit (.lit "00")] (oSet 0), .mk #[.lit (.lit "10")] (oSet 1)]
        (some (oSet 2)) true == some "10"
#guard caseProbe "x1"
        #[.mk #[.lit (.lit "z1")] (oSet 1)]
        (some (oSet 2)) true == some "01"

-- pin3: the async-reset design, all 8 pinned cycles (see the docstring's
-- reset ledger). Model of rows/pin3.sv `ar`.
private def arDesign : Design2 :=
  { name := "ar"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "rst_n", width := 1, isInput := true },
      { name := "d", width := 4, isInput := true },
      { name := "q", width := 4, isOutput := true },
      { name := "q2", width := 4, isOutput := true }]
    processes := #[
      .alwaysFFR "clk" "rst_n"
        (.ifStmt (.unary .bnot (.ident "rst_n"))
          (.nbaAssign (.ident "q") (.lit (.ofNat 4 0)))
          (some (.nbaAssign (.ident "q") (.ident "d")))),
      .alwaysFF "clk" (.nbaAssign (.ident "q2") (.ident "q"))] }

private def arStim : List SvState := [
  [("rst_n", LVec.lit "0"), ("d", LVec.ofNat 4 5)],
  [("rst_n", LVec.lit "1"), ("d", LVec.ofNat 4 5)],
  [("d", LVec.ofNat 4 7)],
  [("rst_n", LVec.lit "0"), ("d", LVec.ofNat 4 9)],
  [("d", LVec.ofNat 4 3)],
  [("rst_n", LVec.lit "1")],
  [("rst_n", LVec.lit "x"), ("d", LVec.ofNat 4 6)],
  [("rst_n", LVec.lit "1"), ("d", LVec.ofNat 4 2)]]

#guard (Res.toOption (run2 arDesign σ_src 64 arStim)).map
        (fun tr => tr.map fun st =>
          (SvState.showSignal st "q", SvState.showSignal st "q2"))
      == some [
        ("0000", "0000"),  -- c0: x→0 negedge resets pre-edge; q2 samples 0
        ("0101", "0000"),  -- c1: release; q2 samples pre-edge q
        ("0111", "0101"),  -- c2
        ("0000", "0000"),  -- c3: 1→0 negedge — reset visible to q2 SAME cycle
        ("0000", "0000"),  -- c4: held low: posedge reset branch holds
        ("0011", "0000"),  -- c5: deassert = posedge of rst_n, no event
        ("0110", "0110"),  -- c6: 1→x negedge runs ELSE branch pre-edge!
        ("0010", "0110")]  -- c7: x→1 = posedge, no event

-- Reset phase and edge phase both fire for a held-low reset with data
-- changing (the level-idempotence half of the ledger): q stays 0.
#guard (Res.toOption (run2 arDesign σ_src 64
        [[("rst_n", LVec.lit "0"), ("d", LVec.ofNat 4 5)],
         [("d", LVec.ofNat 4 9)], [("d", LVec.ofNat 4 1)]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "q")
      == some ["0000", "0000", "0000"]

-- Partial continuous drivers (ff_one shape): two assigns drive disjoint
-- bits of one net; undriven bits stay x.
private def partialDrv : Design2 :=
  { name := "pd"
    decls := #[
      { name := "a", width := 2, isInput := true },
      { name := "y", width := 4 }]
    processes := #[
      .assign (.slice "y" 0 1) (.index (.ident "a") (.lit (.ofNat 1 0)) 1),
      .assign (.slice "y" 2 1) (.index (.ident "a") (.lit (.ofNat 1 1)) 1)] }

#guard (Res.toOption (run2 partialDrv σ_src 64 [[("a", LVec.lit "11")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "y")
      == some ["x1x1"]

end LeanModels.Sv
