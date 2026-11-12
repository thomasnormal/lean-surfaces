import LeanModels.C.C23.Expr

/-!
# §6.8 Statements and blocks — M2 inch 4

C23 (N3220) §6.8. Citations follow `docs/c23-spec-mirror.md`; refusals
name their Annex J.2 index.

## Fuel arrives HERE, and the census is why

`Expr.lean` is fuel-free and says so at length. Statements are not.
Measured on the shipped corpus:

| | |
| --- | ---: |
| loops (`for` 50, `do` 29, `while` 5) | **84** |
| …containing a call | 64 |
| **…containing NO call at all** | **20** |

**It is the loop, not the call, that forces fuel** — those 20 need it
just the same — which is what corrected the inch-3 draft's "fuel arrives
at inch 5". `execStmt` therefore takes a fuel argument and recurses on it
at exactly ONE place: the loop step. Every other statement recurses
structurally on `Stmt`, so the fuel-free reasoning of inch 3 keeps
working underneath.

The `∃ n, ∀ fuel ≥ n, … = .ok …` threshold form
(`docs/c-semantics-design.md` §4.2) is assembled AROUND `execStmt`.
`fuelMono` — that more fuel never changes a decided answer — is stated
and proved below, because it is the lemma every later threshold argument
rests on.

## TIMEOUT is not a refusal, so it does not live in `Except`

`docs/c23-goal.md` §3: *"TIMEOUT — fuel exhausted. The only exhaustion
outcome; never conflated with REFUSE."* The Python tier's `Run` agrees
structurally: `.ok` and `.exn` carry state, **`.timeout` carries none**,
because a timeout is not an observation of anything.

So the stack gains a base:

```
ExecM α := SemMWith Mem Refusal CDetail Mem α
        = ExceptT Refusal (StateT Mem (Except (Loud CDetail Mem))) α
```

where Core's `Loud` carries fuel exhaustion and the out-of-tier frontier,
and nothing else. A timeout discards
the memory, correctly — there is no world to report.

## WHERE REFUSAL LIVES — RULED, at `docs/family-architecture.md` §3.4

This file first argued that `unsupported` should ride in `ExceptT`
(state-carrying), against Python's `Run` and the ES lane's `Halt`, so an
inch-6 REFUSE row could say what had happened by the time the model
declined.

**The ruling went the other way, and this lane's own census is part of
why.** Putting a refusal in `ExceptT` makes it catchable in principle,
and the implicit defence was that nothing in C intercepts control flow.
The corpus refutes that: **`setjmp` 2, `longjmp` 2, 5 `jmp_buf`
objects** — and signal handlers in the language at large. Inside `ρ`,
"no catch reaches a refusal" is a per-language, per-construct proof
obligation; uncatchability belongs to the definition.

So `unsupported` lives in Core's `Loud` base, and the diagnostic need
is met the better way: **`Loud.unsupported` carries a structured payload
— the cause, plus an OPTIONAL memory snapshot captured AT the refusal
site.** §3.4's existing law pays for it, because every refusal already
routes through a NAMED primitive with its own `@[spec]` lemma, and that
primitive performs the `get` itself (`refuseUnsupported`), so no call
site can forget to.

**Two guards, both structural rather than advisory**: the snapshot is
optional, and it is NEVER an observable — `Halt`'s `BEq` ignores it, and
`Outcome`, which is what a scoreboard compares, has nowhere to put a
`Mem` at all.

`Halt` carrying `timeout` with no state was already aligned and the
ruling confirms it on the merits: state at fuel exhaustion would invite
treating a TIMEOUT as an observation.
-/

namespace LeanModels.C.C23

open LeanModels.C (CType Expr Stmt Decl)

/-! ## The monad

`Loud` and the stack are `Core`'s now (`LeanModels/Core/Outcome.lean`),
so statements and expressions run in the SAME stack — `ExecM` is `EvalM`.
That is not a coincidence to tidy away: it is what the ruling bought. An
expression cannot time out (inch 3 is fuel-free) and a statement can, but
neither can catch a refusal, so one type serves both. -/

/-- The statement evaluator's monad — the same stack expressions use. -/
abbrev ExecM (α : Type) := EvalM α

/-- Run a statement against a starting memory. -/
def ExecM.run (m : Mem) (x : ExecM α) :
    Except (Loud CDetail Mem) (Except Refusal α × Mem) :=
  EvalM.run m x

/-- The verdict, in `docs/c23-goal.md` §3's vocabulary. -/
def ExecM.verdict (m : Mem) (x : ExecM α) : Outcome α := EvalM.verdict m x

/-- Fuel exhaustion, as a named primitive — never a bare `throw`, and not
a `Refusal` at all. Carries no state: a timeout is not an observation. -/
def exhausted : ExecM α := fun _ => .error .timeout

/-! ## §6.8.7 — how a statement can finish

A C statement does not simply complete: it can leave its block in five
ways, and the enclosing construct decides what each one means. -/

/-- The completion of a statement (§6.8.7). -/
inductive Flow where
  /-- Fell off the end. -/
  | normal
  /-- §6.8.7.3 `break` — 8 sites. -/
  | brk
  /-- §6.8.7.2 `continue` — 6 sites. -/
  | cont
  /-- §6.8.7.4 `return`, with a value at 98 of its 103 sites. -/
  | ret (value : Option CVal)
  /-- §6.8.7.1 `goto` — 7 sites reaching exactly 3 labels, every one a
  FORWARD jump within the same function. A `Flow.goto` propagating
  outward to a labelled statement serves that shape; a general `goto`
  needs a CFG, and the census says this corpus does not have one. -/
  | goto (label : String)
deriving Repr, Inhabited, BEq

/-- Does this completion escape the enclosing block? -/
def Flow.escapes : Flow → Bool
  | .normal => false
  | _ => true

/-! ## Reaching inch 3

`ExecM` IS `EvalM`, so there is no lift — the ruling that put `Halt`
underneath both is what removed it. `liftEval` remains as a name, because
naming the boundary is worth more than saving a line: it marks every
place a statement reaches into the expression layer. -/

/-- Reach into the expression evaluator. The identity, deliberately. -/
@[inline] def liftEval (x : EvalM α) : ExecM α := x

/-- Evaluate an expression for its value. -/
def evalE (ctx : Ctx) (e : Expr) : ExecM CVal := liftEval (evalExpr ctx e)

/-- Evaluate an expression for its truth (§6.8.5, §6.8.6: a controlling
expression is compared unequal to 0). -/
def evalCond (ctx : Ctx) (e : Expr) : ExecM Bool :=
  liftEval (do let v ← evalExpr ctx e; truthy v)

/-! ## §6.7.11 — initialization of omitted members

The original census reported every corpus initializer as full. That claim
missed Clang's `array_filler` representation and is not evidence that partial
initialization is absent. §6.7.11p10 initializes unmentioned members as
objects with static storage duration, i.e. to zero.

The interpreter implements this rule and tests partial initializers against
the native compiler.

**Zero-initialization is TYPE-DIRECTED, not a memset.** §6.7.11p10 says
the unmentioned members are initialized *as if by `= 0`*, and for a
pointer member that is a NULL POINTER, not all-bits-zero. Writing zero
bytes over a pointer member would make it read back as an integer and
`loadPtr` would refuse it — a wrong answer that looks like a right one.
So the recursion below dispatches on the member's type. -/

mutual

/-- §6.7.11p10 — initialize an object to zero, as if it had static
storage duration. Type-directed: see the section note. -/
def zeroInit : Nat → Ctx → Ptr → CType → ExecM Unit
  | 0, _, _, _ => exhausted
  | fuel + 1, ctx, p, ty =>
    match intTyOf? (ctx.layout.normalizeTy ty) with
    -- an integer member: the value zero at its own width
    | some t => liftEval (writeMem (fun m => Mem.storeInt m p t 0))
    | none =>
      if isPtrType ty then
        -- §6.3.2.3p3: `= 0` on a pointer is a NULL POINTER, not zero bytes
        liftEval (writeMem (fun m => Mem.storePtr m p Ptr.null))
      else
        match ctx.layout.elem ty with
        | some (et, n) =>
            match ctx.layout.size et with
            | some esz => zeroElems fuel ctx p et esz n 0
            | none => refuseUnsupported s!"no size for element type '{et}'"
        | none =>
          match ctx.layout.members ty with
          | some ms => zeroMembers fuel ctx p ty ms
          | none => refuseUnsupported s!"cannot zero-initialize '{ty}'"

/-- Zero the elements of an array, from index `i` up. -/
def zeroElems : Nat → Ctx → Ptr → CType → Nat → Nat → Nat → ExecM Unit
  | 0, _, _, _, _, _, _ => exhausted
  | fuel + 1, ctx, p, et, esz, n, i =>
    if i ≥ n then pure ()
    else do
      zeroInit fuel ctx (Mem.member p (i * esz)) et
      zeroElems fuel ctx p et esz n (i + 1)

/-- Zero the members of a structure, in declaration order. -/
def zeroMembers : Nat → Ctx → Ptr → CType → List (String × CType) → ExecM Unit
  | 0, _, _, _, _ => exhausted
  | _, _, _, _, [] => pure ()
  | fuel + 1, ctx, p, ty, (nm, mty) :: rest => do
      match ctx.layout.fieldOff ty nm with
      | some off => zeroInit fuel ctx (Mem.member p off) mty
      | none => refuseUnsupported s!"no offset for member '{nm}'"
      zeroMembers fuel ctx p ty rest

end

/-! ### The initializer proper -/

mutual

/-- §6.7.11 — initialize the object at `p`, of type `ty`, from `e`.

A scalar initializer is an assignment (§6.7.11p11). A brace-enclosed list
initializes an aggregate member by member (p9), **in declaration order**,
and every member the list does not reach is zeroed (p10). -/
def initObject : Nat → Ctx → Ptr → CType → Expr → ExecM Unit
  | 0, _, _, _, _ => exhausted
  | fuel + 1, ctx, p, ty, e =>
    match e with
    | .implicitValueInit _ _ => zeroInit fuel ctx p ty
    | .arrayInitList inits filler field _ _ =>
        -- Clang's array_filler is [default filler, positional entries...].
        -- Only its implicit-zero default is in tier; retain and refuse other
        -- shapes rather than guessing their repeated initialization semantics.
        match inits, filler, ctx.layout.elem ty with
        | [], .implicitValueInit _ _ :: entries, some (et, n) =>
            match ctx.layout.size et with
            | some esz => initElems fuel ctx p et esz n 0 entries
            | none => refuseUnsupported s!"no size for element type '{et}'"
        | _, _, _ => refuseUnsupported "unsupported Clang array_filler initializer"
    | .initList inits field _ _ =>
        if (ty.startsWith "union ") then
          match ctx.layout.members ty, inits with
          | some ms, e :: _ =>
              let target := field.getD ((ms.head?.map (·.1)).getD "")
              match ctx.layout.fieldOff ty target with
              | some off => initObject fuel ctx (Mem.member p off) (ms.find? (·.1 == target) |>.map (·.2) |>.getD ty) e
              | none => refuseUnsupported s!"no offset for union member '{target}'"
          | _, _ => refuseUnsupported "union initializer has no member"
        else
        match ctx.layout.elem ty with
        -- an ARRAY: elements at i * sizeof(elem), then §6.7.11p10 on the tail
        | some (et, n) =>
            match ctx.layout.size et with
            | some esz => initElems fuel ctx p et esz n 0 inits
            | none => refuseUnsupported s!"no size for element type '{et}'"
        | none =>
          match ctx.layout.members ty with
          -- a STRUCTURE: members in declaration order, then p10 on the rest
          | some ms => initMembers fuel ctx p ty ms inits
          | none => refuseUnsupported s!"cannot initialize aggregate '{ty}'"
    -- §6.7.11p11 — a scalar initializer is a single expression.
    | _ => do
        let v ← evalE ctx e
        liftEval (storeAt p (ctx.layout.normalizeTy ty) v)

/-- Array elements, then zero-fill (§6.7.11p10). -/
def initElems : Nat → Ctx → Ptr → CType → Nat → Nat → Nat → List Expr → ExecM Unit
  | 0, _, _, _, _, _, _, _ => exhausted
  | fuel + 1, ctx, p, et, esz, n, i, es =>
    match es with
    -- the list ran out: every remaining element is zeroed
    | [] => zeroElems fuel ctx p et esz n i
    | e :: rest =>
        if i ≥ n then
          -- §6.7.11p2 is a CONSTRAINT: more initializers than elements.
          refuseUnsupported "more initializers than array elements"
        else do
          initObject fuel ctx (Mem.member p (i * esz)) et e
          initElems fuel ctx p et esz n (i + 1) rest

/-- Structure members in declaration order, then zero-fill. -/
def initMembers : Nat → Ctx → Ptr → CType → List (String × CType) → List Expr → ExecM Unit
  | 0, _, _, _, _, _ => exhausted
  | fuel + 1, ctx, p, ty, ms, es =>
    match ms, es with
    | [], [] => pure ()
    | [], _ :: _ => refuseUnsupported "more initializers than structure members"
    -- the list ran out: §6.7.11p10 zeroes every member it did not reach
    | rest, [] => zeroMembers fuel ctx p ty rest
    | (nm, mty) :: mrest, e :: erest => do
        match ctx.layout.fieldOff ty nm with
        | some off => initObject fuel ctx (Mem.member p off) mty e
        | none => refuseUnsupported s!"no offset for member '{nm}'"
        initMembers fuel ctx p ty mrest erest

end

/-! Install the statement-layer initializer callback used by compound
literals in the expression evaluator. -/
def Ctx.withCompoundInit (ctx : Ctx) : Ctx :=
  { ctx with compoundInit := fun fuel env ids layout p ty e =>
      initObject fuel { ctx with env := env, idEnv := ids, layout := layout } p ty e }

/-! ## §6.8.7.1 — `goto`, and why a label search is enough

Measured: the corpus's **7 `goto`s reach exactly 3 labels**
(`after_moves` x3, `out` x3, `reset_ok` x1), and **every one is a FORWARD
jump to a label in the same function at the same or an enclosing block
level.** That is precisely the shape a block can serve by scanning the
statements it has not run yet; a backward or into-a-block jump would need
a control-flow graph, and this corpus has none. A jump whose label is not
found propagates outward, and reaching the top of a function unmatched is
a refusal rather than a silent fall-through. -/

/-- The statements from `label` onward, if it is among these. -/
def findLabel (name : String) : List Stmt → Option (List Stmt)
  | [] => none
  | s :: rest =>
      match s with
      | .label n body sp => if n == name then some (.label n body sp :: rest)
                            else findLabel name rest
      | _ => findLabel name rest

def hasDecl : List Stmt → Bool
  | [] => false
  | .decl _ _ :: _ => true
  | _ :: rest => hasDecl rest

/-! ## §6.8 — the statement evaluator

Fuel decreases on EVERY recursive call, not only at the loop step. That
is stricter than §4.6.1 needs — a block is not an iteration — but it
makes the recursion structural on `Nat` with no measure to justify, and
fuel is a bound on total work rather than on iterations alone. The
`∃ n, ∀ fuel ≥ n` threshold form is unaffected: it quantifies over fuel
from outside. -/

inductive SwitchItem where
  | label (value : Option Expr)
  | rangeLabel (lo hi : Expr)
  | stmt (s : Stmt)

def switchCaseTail : Stmt → List SwitchItem
  | .caseS v b _ => .label (some v) :: switchCaseTail b
  | .caseRange lo hi b _ => .rangeLabel lo hi :: switchCaseTail b
  | .defaultS b _ => .label none :: switchCaseTail b
  | s => [.stmt s]

def switchItems : Stmt → List SwitchItem
  | .compound body _ => body.flatMap switchItems
  | .caseS v b _ => .label (some v) :: switchCaseTail b
  | .caseRange lo hi b _ => .rangeLabel lo hi :: switchCaseTail b
  | .defaultS b _ => .label none :: switchCaseTail b
  | s => [.stmt s]

def containsCaseLabel (s : Stmt) : Bool :=
  s.substmts.any fun t => match t with
    | .caseS .. | .caseRange .. | .defaultS .. => true
    | _ => false

def switchHasNestedLabel : Stmt → Bool
  | .compound body _ => body.any fun s =>
      match s with
      | .caseS _ b _ | .caseRange _ _ b _ | .defaultS b _ => containsCaseLabel b
      | _ => containsCaseLabel s
  | s => containsCaseLabel s

def switchFindAux (ctx : Ctx) (cv : CVal) :
    List SwitchItem → Option (List Stmt) → Option (List Stmt) → EvalM (Option (List Stmt))
  | [], selected, fallback =>
      pure ((selected.orElse (fun _ => fallback)).map List.reverse)
  | .label label :: rest, selected, fallback =>
      match selected with
      | some _ => switchFindAux ctx cv rest selected fallback
      | none =>
          match label with
          | none => switchFindAux ctx cv rest none (some [])
          | some e => do
              let v ← evalExpr ctx e
              let (_, a) ← asInt cv
              let (_, b) ← asInt v
              if a == b then switchFindAux ctx cv rest (some []) fallback
              else switchFindAux ctx cv rest none fallback
  | .rangeLabel lo hi :: rest, selected, fallback =>
      match selected with
      | some _ => switchFindAux ctx cv rest selected fallback
      | none => do
          let lv ← evalExpr ctx lo
          let hv ← evalExpr ctx hi
          let (_, a) ← asInt cv
          let (_, l) ← asInt lv
          let (_, h) ← asInt hv
          if l ≤ a && a ≤ h then switchFindAux ctx cv rest (some []) fallback
          else switchFindAux ctx cv rest none fallback
  | .stmt s :: rest, selected, fallback =>
      match selected, fallback with
      | some acc, _ => switchFindAux ctx cv rest (some (s :: acc)) fallback
      | none, some acc => switchFindAux ctx cv rest none (some (s :: acc))
      | none, none => switchFindAux ctx cv rest none none
  termination_by items _ _ => items.length

def switchFind (ctx : Ctx) (cv : CVal) (body : Stmt) : EvalM (Option (List Stmt)) :=
  switchFindAux ctx cv (switchItems body) none none

mutual

def execSwitch : Nat → Ctx → Expr → Stmt → ExecM Flow
  | 0, _, _, _ => exhausted
  | fuel + 1, ctx, cond, body => do
      if switchHasNestedLabel body then
        refuseUnsupported "case label nested in a control statement"
      let cv ← evalE ctx cond
      let selected ← switchFind ctx cv body
      match selected with
      | none => pure .normal
      | some statements => do
          let f ← execBlock fuel ctx statements
          match f with
          | .brk => pure .normal
          | other => pure other

/-- §6.8 — execute one statement, yielding how it completed. -/
def execStmt : Nat → Ctx → Stmt → ExecM Flow
  | 0, _, _ => exhausted
  | fuel + 1, ctx, s => match s with
    -- §6.8.3 — a block. Declarations inside it extend the environment,
    -- which is why the block threads a context rather than reading one.
    | .compound body _ => do
        let m₀ ← get
        let base := m₀.count
        let runMemset : List CVal → EvalM CVal := fun vs =>
          match vs with
          | [p, byte, count] => do
              let q ← asPtr p
              let (_, b) ← asInt byte
              let (_, n) ← asInt count
              if n < 0 then refuseUnsupported "memset: negative size"
              else do
                let bs := List.replicate n.toNat (CByte.conc (UInt8.ofNat b.toNat))
                writeMem (fun m => m.storeBytes q bs)
                pure (.ptr q)
          | _ => refuseUnsupported "memset: wrong argument count"
        let f ← execBlock fuel ctx body
        let m₁ ← get
        set (m₁.killFrom base)
        pure f
    -- §6.8.4 — an expression statement: evaluated for its EFFECTS, value
    -- discarded. 297 sites, the largest statement class in the corpus.
    | .expr e _ => do let _ ← evalE ctx e; pure .normal
    | .nullStmt _ => pure .normal
    | .switchS c body _ => execSwitch fuel ctx c body
    | .caseS _ _ _ | .caseRange _ _ _ _ | .defaultS _ _ =>
        refuseUnsupported "case/default escaped a switch body"
    -- §6.8.5.1 — `if`. Measured: only 51 of 253 carry an `else`, so the
    -- else-less arm is the common path and is written first.
    | .ifS c t none _ => do
        if (← evalCond ctx c) then execStmt fuel ctx t else pure .normal
    | .ifS c t (some e) _ => do
        if (← evalCond ctx c) then execStmt fuel ctx t else execStmt fuel ctx e
    -- §6.8.7.4 — `return`, with a value at 98 of 103 sites.
    | .ret none _ => pure (.ret none)
    | .ret (some e) _ => do let v ← evalE ctx e; pure (.ret (some v))
    | .breakS _ => pure .brk              -- §6.8.7.3, 8 sites
    | .continueS _ => pure .cont          -- §6.8.7.2, 6 sites
    | .goto l _ => pure (.goto l)         -- §6.8.7.1, 7 sites
    -- A labelled statement runs its body; the LABEL is found by the
    -- enclosing block (`findLabel`), not by the statement itself.
    | .label _ body _ => execStmt fuel ctx body
    -- §6.8.6.2 — `while`. 5 sites.
    | .whileS c body _ => execLoop fuel ctx (some c) none body false
    -- §6.8.6.3 — `do … while`: the body runs BEFORE the first test. 29 sites.
    | .doS body c _ => execLoop fuel ctx (some c) none body true
    -- §6.8.6.4 — `for`. 50 sites; 48 carry `init`, 49 carry `cond`, 50 carry
    -- `inc` — so THREE sites omit a clause (two omit `init`, one omits
    -- `cond`) and the omitted-clause arms are
    -- three sites rather than a third of them. An omitted `cond` is TRUE.
    | .forS init c inc body _ => do
        match init with
        | some i => do
            let f ← execStmt fuel ctx i
            match f with
            | .normal => execLoop fuel ctx c inc body false
            | other => pure other
        | none => execLoop fuel ctx c inc body false
    -- A bare declaration reaching here is one the block did not thread;
    -- `execBlock` handles them, so this is unreachable in practice and
    -- refuses rather than silently doing nothing.
    | .decl _ _ => refuseUnsupported "declaration outside a block"
    | .unsupported k _ _ => refuseUnsupported s!"out of tier: {k}"

/-- Run a block's statements in order, threading the environment that
declarations extend and honouring a forward `goto` into the remainder. -/
def execBlock : Nat → Ctx → List Stmt → ExecM Flow
  | 0, _, _ => exhausted
  | _, _, [] => pure .normal
  | fuel + 1, ctx, s :: rest =>
    match s with
    -- §6.7 — a declaration extends the environment for the REST of the
    -- block. C23 §6.7p5 sequences declarators left to right, each fully
    -- before the next, which `declare` follows.
    | .decl ds _ => do
        let ctx' ← declare fuel ctx ds
        execBlock fuel ctx' rest
    | _ => do
      let f ← execStmt fuel ctx s
      match f with
      | .normal => execBlock fuel ctx rest
      | .goto l =>
          -- §6.8.7.1: a forward jump lands on a label later in THIS block,
          -- or propagates outward to an enclosing one.
          match findLabel l rest with
          | some tail =>
              if hasDecl rest then
                refuseUnsupported "goto skips a block declaration"
              else execBlock fuel ctx tail
          | none => pure (.goto l)
      | other => pure other

/-- One loop, with fuel decreasing per ITERATION.

`post` is `do … while`: the body runs before the first test. `inc` is
`for`'s third clause, evaluated after the body and before the next test —
and, per §6.8.6.4p2, **also after a `continue`**, which is the detail a
model gets wrong by treating `continue` as `break`. -/
def execLoop : Nat → Ctx → Option Expr → Option Expr → Stmt → Bool → ExecM Flow
  | 0, _, _, _, _, _ => exhausted
  | fuel + 1, ctx, cond, inc, body, post => do
      -- an omitted controlling expression is TRUE (§6.8.6.4p2)
      let go ← if post then pure true
               else match cond with
                    | some c => evalCond ctx c
                    | none => pure true
      if !go then pure .normal
      else do
        let f ← execStmt fuel ctx body
        match f with
        | .brk => pure .normal            -- §6.8.7.3: break ENDS the loop
        | .ret v => pure (.ret v)
        | .goto l => pure (.goto l)
        | .normal | .cont => do
            -- §6.8.6.4p2: `continue` still runs the increment.
            match inc with
            | some e => do let _ ← evalE ctx e; pure ()
            | none => pure ()
            execLoop fuel ctx cond inc body false

/-- §6.7 — create the objects a declaration introduces and bind their
names, left to right.

Measured: 273 of 321 `VarDecl`s carry an initializer, and **75
`InitListExpr` nodes** appear in the corpus (35 top-level, 40 nested).
Both shapes go through `initObject` (§6.7.11). -/
def declare : Nat → Ctx → List Decl → ExecM Ctx
  | 0, _, _ => exhausted
  | _, ctx, [] => pure ctx
  | fuel + 1, ctx, d :: ds =>
    match d with
    | .var id name ty storage init _recordId _ => do
        if storage == some "static" then
          match id with
          | some declaration =>
              match ctx.idEnv.lookup? declaration with
              | some o => declare fuel { ctx with env := (name, o) :: ctx.env } ds
              | none => refuseUnsupported s!"static object '{name}' has no initialized storage"
          | none => refuseUnsupported s!"static object '{name}' has no declaration identity"
        else
          match storage with
          | some "auto" | some "register" | some "static" | none => pure ()
          | some s => refuseUnsupported s!"block-scope storage class '{s}' is outside the tier"
          match ctx.layout.size ty with
          | none => refuseUnsupported s!"no layout for declared type '{ty}'"
          | some sz => do
            -- §6.2.4p6: an automatic object lives from block entry, with
            -- an INDETERMINATE representation until something writes it;
            -- block-scope `static` instead keeps its static lifetime.
            let m ← get
            let dur := if storage == some "static" then Duration.static_ else Duration.automatic
            let (m', o) := m.alloc dur sz (some ty)
            set m'
            let idEnv' := match id with
              | some declaration => (declaration, o) :: ctx.idEnv
              | none => ctx.idEnv
            let ctx' := { ctx with env := (name, o) :: ctx.env }
            let ctx' := { ctx' with idEnv := idEnv' }
            match init with
            | none => declare fuel ctx' ds
            | some e => do
                -- §6.7.11 — scalar or aggregate, one entry point.
                initObject fuel ctx' (Ptr.toObject o) ty e
                declare fuel ctx' ds
    | .empty _ => declare fuel ctx ds
    | .record _ _ _ _ | .enum _ _ _ | .typedef _ _ _ _ =>
        declare fuel ctx ds
    | _ => refuseUnsupported "non-object declaration in a block"

end

/-! ## §6.5.3.3 — function calls: inch 5

**The call graph is almost entirely acyclic, and the census is the
decision-relevant fact.** Of 58 defined functions, exactly **one is
directly self-recursive** (`bound`, the search) and there is **one mutual
cycle of size two** (`bound` ↔ `score_move`). Everything else is a DAG.

So fuel, which arrived at inch 4 for loops, arrives here for a call graph
whose cyclic part is two functions wide. It is still needed — a model
cannot know the graph is acyclic without proving it — but the measurement
says the fuel-consuming surface is small, and it names exactly which
functions a termination argument would have to be about.

Where the 320 call sites go:

| | sites |
| --- | ---: |
| to one of the 58 DEFINED functions | **155** |
| to one of the 27 libc externals — cause `libc` | **146** |
| INDIRECT, every one through `movecb` | **19** |

Nearly half of all calls leave the tier, and they refuse as `libc` — the
cause that retires by widening the slice, never pooled with the others. -/

/-- The functions a call can reach, with the layout and enumeration
constants they need. -/
structure Program where
  fns : List LeanModels.C.FunctionDefn
  layout : Layout := Layout.unknown
  enums : List (String × Int) := []
  enumIds : List (LeanModels.C.DeclarationId × Int) := []
  /-- **§6.2.1p4 — the file-scope objects a function body can SEE.**

  This field is a bug fix, not a feature. `callFn` used to start every
  frame at `env := []`, which is the rule *"no object declared outside a
  function is visible inside one"* — and C's rule is the opposite: an
  identifier declared at file scope has file scope, and that scope runs to
  the end of the translation unit. The old spelling was not a missing
  capability, it was a wrong law, and it was invisible because the corpus
  the tier was built on passes everything through parameters.

  Measured on `gcc.c-torture`: **69 of 300 tests refused with `unbound
  name`, and all 69 of the names were file-scope objects** — 100 %, no
  locals and no typos (`docs/backlog/c.md` 2026-08-24-c-22). -/
  globals : Env := []
  globalIds : IdEnv := []

def Program.find? (p : Program) (name : String) : Option LeanModels.C.FunctionDefn :=
  p.fns.find? (·.name == name)

def Program.findId? (p : Program) (id : LeanModels.C.DeclarationId) :
    Option LeanModels.C.FunctionDefn :=
  p.fns.find? (fun f => f.id == some id)

-- `evalArgsLR` lived here, unreachable, as "the shape the repair will
-- re-attach to". The repair did not re-attach to it: argument evaluation
-- had to move INTO `Expr.lean`'s mutual block to borrow `evalExpr`'s
-- measure, so the real function is `C23.evalArgs` and this copy is deleted
-- rather than left as a second answer to one question.

/-- §6.5.3.3p4 / §6.9.2p7 — give each parameter its own automatic object
and store the argument into it.

A parameter IS an object (§6.9.2p7: "the parameters are declared as if by
declaration in the compound statement"), which is why 1 of the corpus's
31 `&`-of-automatic sites takes the address of one. Measured parameter
counts: 0-9, and 39 of 58 functions take two or fewer. -/
def bindParams (lay : Layout) : Ctx → List LeanModels.C.Decl → List CVal → ExecM Ctx
  | ctx, [], [] => pure ctx
  | _, [], _ :: _ => refuseUnsupported "more arguments than parameters"
  | _, _ :: _, [] => refuseUnsupported "fewer arguments than parameters"
  | ctx, d :: ps, v :: vs =>
    match d with
    | .param id n ty _ =>
        match lay.size ty with
        | none => refuseUnsupported s!"no layout for parameter type '{ty}'"
        | some sz => do
            -- §6.9.2p7 holds for an UNNAMED parameter too: the object
            -- exists and is initialized with the converted argument. The
            -- allocation and the store are OUTSIDE the match on `n` on
            -- purpose — eliding them for the unnamed case is not
            -- expressible here without moving code, which is the point.
            -- (Whether the allocation is unobservable when nothing names
            -- the object is a LEMMA about `Mem`, not a shortcut; it is not
            -- claimed, so it is not taken.)
            let m ← get
            let (m', o) := m.alloc .automatic sz (some ty)
            set m'
            liftEval (storeAt (Ptr.toObject o) (lay.normalizeTy ty) v)
            -- …and the ONLY difference an unnamed parameter makes is that
            -- no identifier denotes the object, which in this model is
            -- exactly one thing: no environment entry. This is the single
            -- place the absence is decided.
            let env' := match n with
                        | some nm => (nm, o) :: ctx.env
                        | none => ctx.env
            let idEnv' := match id with
                          | some declaration => (declaration, o) :: ctx.idEnv
                          | none => ctx.idEnv
            bindParams lay { ctx with env := env', idEnv := idEnv' } ps vs
    | _ => refuseUnsupported "non-parameter in a parameter list"

/-- §6.5.3.3 — call a defined function with already-evaluated arguments.

The handler the callee's frame carries is built HERE, closing over the
decremented fuel: that is the whole recursion, and it is why fuel is a
parameter of this function rather than of `evalExpr`.

A `void` function answers `.undef`, not a fabricated zero — the value of
a `void` call may not be used (§6.5.3.3p3), and `.undef` is the value
every consumer already refuses. Returning `0` would have been a number
somebody could read. -/
def callFn : Nat → Program → LeanModels.C.FunctionDefn → List CVal → ExecM CVal
  | 0, _, _, _ => exhausted
  | fuel + 1, prog, f, args =>
    match f.body with
    | none => refuseUnsupported s!"'{f.name}' is a prototype, not a definition"
    | some body => do
        if f.params.any fun d => match d with
          | .param _ none ty _ => isPtrType ty
          | _ => false then
          refuseUnsupported "unnamed pointer parameter (array-bound effects are not retained by clang)"
        let m₀ ← get
        let base := m₀.count
        let runMemset : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [p, byte, count] => do
              let q ← asPtr p
              let (_, b) ← asInt byte
              let (_, n) ← asInt count
              if n < 0 then refuseUnsupported "memset: negative size"
              else do
                let bs := List.replicate n.toNat (CByte.conc (UInt8.ofNat b.toNat))
                liftEval (writeMem (fun m => m.storeBytes q bs))
                pure (.ptr q)
          | _ => refuseUnsupported "memset: wrong argument count"
        let runMemcpy : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [dst, src, count] => do
              let dp ← asPtr dst
              let sp ← asPtr src
              let (_, n) ← asInt count
              if n < 0 then refuseUnsupported "memcpy: negative size"
              else do
                let bs ← liftEval (readMem (fun m => m.loadBytes sp n.toNat))
                liftEval (writeMem (fun m => m.storeBytes dp bs))
                pure (.ptr dp)
          | _ => refuseUnsupported "memcpy: wrong argument count"
        let runSprintf : List CVal → ExecM CVal := fun vs =>
          match vs with
          | dst :: fmt :: args => do
              let dp ← asPtr dst
              let fp ← asPtr fmt
              let m ← get
              let (_, fo, off) ← liftEval (m.resolve fp 0)
              let rec takeSprintfString : List CByte → Option (List CByte)
                | [] => none
                | .conc x :: rest =>
                    if x == 0 then some []
                    else (takeSprintfString rest).map (fun tail => CByte.conc x :: tail)
                | _ => none
              let pattern ← match takeSprintfString (fo.bytes.drop off) with
                | some bytes => pure bytes
                | none => refuseUnsupported "sprintf: non-concrete or unterminated format"
              let rec formatSprintf : List CByte → List CVal → ExecM (List CByte)
                | [], _ => pure []
                | .conc 37 :: .conc 37 :: rest, as => do
                    let tail ← formatSprintf rest as
                    pure (CByte.conc 37 :: tail)
                | .conc 37 :: .conc 100 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← formatSprintf rest as
                    pure ((toString n).toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 108 :: .conc 117 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← formatSprintf rest as
                    pure ((toString n).toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 48 :: .conc 50 :: .conc 100 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let rendered := if n >= 0 && n < 10 then "0" ++ toString n else toString n
                    let tail ← formatSprintf rest as
                    pure (rendered.toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 115 :: rest, a :: as => do
                    let sp ← asPtr a
                    let current ← get
                    let (_, string, stringOff) ← liftEval (current.resolve sp 0)
                    let chars ← match takeSprintfString (string.bytes.drop stringOff) with
                      | some bytes => pure bytes
                      | none => refuseUnsupported "sprintf: non-concrete or unterminated string argument"
                    let tail ← formatSprintf rest as
                    pure (chars ++ tail)
                | .conc 37 :: [], _ => refuseUnsupported "sprintf: trailing percent"
                | .conc 37 :: .conc _ :: _, _ => refuseUnsupported "sprintf: unsupported format"
                | .conc b :: rest, as => do
                    let tail ← formatSprintf rest as
                    pure (CByte.conc b :: tail)
                | _, _ => refuseUnsupported "sprintf: non-concrete format byte"
              let chars ← formatSprintf pattern args
              let bytes := chars ++ [CByte.conc 0]
              liftEval (writeMem (fun mem => mem.storeBytes dp bytes))
              pure (.int IntTy.int_ chars.length)
          | _ => refuseUnsupported "sprintf: missing destination or format argument"
        let runPrintf : List CVal → ExecM CVal := fun vs =>
          match vs with
          | fmt :: args => do
              let fp ← asPtr fmt
              let m ← get
              let (_, source, off) ← liftEval (m.resolve fp 0)
              let rec takePrintfString : List CByte → Option (List CByte)
                | [] => none
                | .conc x :: rest =>
                    if x == 0 then some []
                    else (takePrintfString rest).map (fun tail => CByte.conc x :: tail)
                | _ => none
              let pattern ← match takePrintfString (source.bytes.drop off) with
                | some bytes => pure bytes
                | none => refuseUnsupported "printf: non-concrete or unterminated format"
              let rec format : List CByte → List CVal → ExecM (List CByte)
                | [], _ => pure []
                | .conc 37 :: .conc 37 :: rest, as => do
                    let tail ← format rest as
                    pure (CByte.conc 37 :: tail)
                | .conc 37 :: .conc 100 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← format rest as
                    pure ((toString n).toList.map (fun c => CByte.conc (UInt8.ofNat c.toNat)) ++ tail)
                | .conc 37 :: .conc 99 :: rest, a :: as => do
                    let (_, n) ← asInt a
                    let tail ← format rest as
                    pure (CByte.conc (UInt8.ofNat n.toNat) :: tail)
                | .conc 37 :: .conc 115 :: rest, a :: as => do
                    let sp ← asPtr a
                    let current ← get
                    let (_, string, stringOff) ← liftEval (current.resolve sp 0)
                    let chars ← match takePrintfString (string.bytes.drop stringOff) with
                      | some bytes => pure bytes
                      | none => refuseUnsupported "printf: non-concrete or unterminated string argument"
                    let tail ← format rest as
                    pure (chars ++ tail)
                | .conc 37 :: .conc _ :: _, _ => refuseUnsupported "printf: unsupported format"
                | .conc 37 :: [], _ => refuseUnsupported "printf: trailing percent"
                | .conc b :: rest, as => do
                    let tail ← format rest as
                    pure (CByte.conc b :: tail)
                | _, _ => refuseUnsupported "printf: non-concrete format byte"
              let bytes ← format pattern args
              modify (fun mem => mem.emitStdout bytes)
              pure (.int IntTy.int_ bytes.length)
          | _ => refuseUnsupported "printf: missing format argument"
        let runBuiltinStrcpy : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [dst, src] => do
              let dp ← asPtr dst
              let sp ← asPtr src
              let m ← get
              let (_, source, off) ← liftEval (m.resolve sp 0)
              let rec takeString : List CByte → Option (List CByte)
                | [] => none
                | .conc x :: rest =>
                    if x == 0 then some [CByte.conc 0]
                    else (takeString rest).map (fun tail => CByte.conc x :: tail)
                | _ => none
              match takeString (source.bytes.drop off) with
              | some bytes =>
                  liftEval (writeMem (fun mem => mem.storeBytes dp bytes))
                  pure (.ptr dp)
              | none => refuseUnsupported "__builtin_strcpy: non-concrete or unterminated string"
          | _ => refuseUnsupported "__builtin_strcpy: wrong argument count"
        let runStrcmp : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [left, right] => do
              let lp ← asPtr left
              let rp ← asPtr right
              let m ← get
              let (_, lo, loff) ← liftEval (m.resolve lp 0)
              let (_, ro, roff) ← liftEval (m.resolve rp 0)
              let rec cmpStr : List CByte → List CByte → Option Int
                | [], _ | _, [] => none
                | .conc x :: xs, .conc y :: ys =>
                    if x == 0 && y == 0 then some 0
                    else if x == 0 then some (-1)
                    else if y == 0 then some 1
                    else if x < y then some (-1)
                    else if x > y then some 1
                    else cmpStr xs ys
                | _, _ => none
              match cmpStr (lo.bytes.drop loff) (ro.bytes.drop roff) with
              | some v => pure (.int IntTy.int_ v)
              | none => refuseUnsupported "strcmp: non-concrete or unterminated string"
          | _ => refuseUnsupported "strcmp: wrong argument count"
        let runMemcmp : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [left, right, count] => do
              let lp ← asPtr left
              let rp ← asPtr right
              let (_, n) ← asInt count
              if n < 0 then refuseUnsupported "memcmp: negative size"
              else do
                let a ← liftEval (readMem (fun m => m.loadBytes lp n.toNat))
                let b ← liftEval (readMem (fun m => m.loadBytes rp n.toNat))
                let rec cmp : List CByte → List CByte → Option Int
                  | [], [] => some 0
                  | .conc x :: xs, .conc y :: ys =>
                      if x < y then some (-1)
                      else if x > y then some 1
                      else cmp xs ys
                  | _, _ => none
                match cmp a b with
                | some v => pure (.int IntTy.int_ v)
                | none => refuseUnsupported "memcmp: non-concrete byte"
          | _ => refuseUnsupported "memcmp: wrong argument count"
        let runStrlen : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [src] => do
              let sp ← asPtr src
              let m ← get
              let (_, source, off) ← liftEval (m.resolve sp 0)
              let rec scan : List CByte → Nat → Option Nat
                | [], _ => none
                | b :: rest, n =>
                    match b with
                    | .conc x => if x == 0 then some n else scan rest (n + 1)
                    | _ => none
              match scan (source.bytes.drop off) 0 with
              | some n => pure (.int IntTy.ulong n)
              | none => refuseUnsupported "strlen: no concrete NUL in object"
          | _ => refuseUnsupported "strlen: wrong argument count"
        let runAlloca : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [size] => do
              let (_, n) ← asInt size
              if n < 0 then refuseUnsupported "alloca: negative size"
              else do
                let m ← get
                let (m', o) := m.alloc .automatic n.toNat none
                set m'
                pure (.ptr (Ptr.toObject o))
          | _ => refuseUnsupported "alloca: wrong argument count"
        let runFfs : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [value] => do
              let (ty, n) ← asInt value
              let m := ty.modulus
              let residue := (n % m + m) % m
              let rec first (bits : Nat) (index : Nat) : Nat :=
                match bits with
                | 0 => 0
                | b + 1 => if b % 2 == 1 then index + 1 else first (b / 2) (index + 1)
              pure (.int IntTy.int_ (first residue.toNat 0))
          | _ => refuseUnsupported "__builtin_ffs: wrong argument count"
        -- GCC/Clang's fixed-width byte-swap builtins are value operations,
        -- not library calls.  Their signatures are parser-resolved in the
        -- admitted slice: unsigned short and unsigned int respectively.
        let runBswap16 : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [value] => do
              let (t, n) ← asInt value
              if t != IntTy.ushort then
                refuseUnsupported "__builtin_bswap16: argument is not unsigned short"
              else
                let lo := n % 256
                let hi := n / 256
                pure (.int IntTy.ushort (lo * 256 + hi))
          | _ => refuseUnsupported "__builtin_bswap16: wrong argument count"
        let runBswap32 : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [value] => do
              let (t, n) ← asInt value
              if t != IntTy.uint then
                refuseUnsupported "__builtin_bswap32: argument is not unsigned int"
              else
                let b0 := n % 256
                let b1 := (n / 256) % 256
                let b2 := (n / 65536) % 256
                let b3 := (n / 16777216) % 256
                pure (.int IntTy.uint
                  (b0 * 16777216 + b1 * 65536 + b2 * 256 + b3))
          | _ => refuseUnsupported "__builtin_bswap32: wrong argument count"
        let runAbs : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [value] => do
              let (t, n) ← asInt value
              if t != IntTy.int_ then
                refuseUnsupported "__builtin_abs: argument is not int"
              else if n == t.minVal then
                refuseValue (.signedOverflow "abs" t n)
              else
                pure (.int IntTy.int_ (if n < 0 then -n else n))
          | _ => refuseUnsupported "__builtin_abs: wrong argument count"
        let runSyncAdd8 : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [dst, value] => do
              let dp ← asPtr dst
              let (vt, y) ← asInt value
              if vt != IntTy.ulong then
                refuseUnsupported "__sync_add_and_fetch_8: argument is not unsigned long long"
              else
                let m ← get
                let ty ← match dp.obj with
                  | some o =>
                      match m.get? o with
                      | some c =>
                          match c.effTy with
                          | some t => pure t
                          | none => refuseUnsupported "__sync_add_and_fetch_8: destination has no declared type"
                      | none => refuseUnsupported "__sync_add_and_fetch_8: destination object is not live"
                  | none => refuseUnsupported "__sync_add_and_fetch_8: null destination"
                let t ← liftEval (intTyOf ty)
                if t != IntTy.ulong then
                  refuseUnsupported "__sync_add_and_fetch_8: destination is not unsigned long long"
                else do
                  let old ← liftEval (loadAt dp ty (prog.layout.size ty))
                  let (_, x) ← asInt old
                  let result := t.wrap (x + y)
                  liftEval (storeAt dp ty (.int t result))
                  pure (.int t result)
          | _ => refuseUnsupported "__sync_add_and_fetch_8: wrong argument count"
        let runArithOverflow (op : String) : List CVal → ExecM CVal := fun vs =>
          match vs with
          | [a, b, dst] => do
              let (_, x) ← asInt a
              let (_, y) ← asInt b
              let dp ← asPtr dst
              let m ← get
              let ty ← match dp.obj with
                | some o =>
                    match m.get? o with
                    | some c =>
                        match c.effTy with
                        | some t => pure t
                        | none => refuseUnsupported "__builtin_mul_overflow: destination has no declared type"
                    | none => refuseUnsupported "__builtin_mul_overflow: destination object is not live"
                | none => refuseUnsupported "__builtin_mul_overflow: null destination"
              let t ← liftEval (intTyOf ty)
              let result := if op == "add" then x + y else x * y
              let overflow := !t.inRange result
              liftEval (storeAt dp ty (.int t (t.wrap result)))
              pure (.int IntTy.int_ (if overflow then 1 else 0))
          | _ => refuseUnsupported s!"__builtin_{op}_overflow: wrong argument count"
        -- The callee's own call handler: one fuel less, so the recursion
        -- terminates on the fuel and on nothing else.
        let handler : CallHandler := fun callee vs =>
          match calleeId callee with
          | some declaration =>
            -- `abort` and `exit` are the score oracle even when clang's
            -- callee carries an external declaration ID. Resolve those two
            -- names before the ID lookup; otherwise the ID itself leaks into
            -- the refusal (`libc id24`) and the oracle arm never sees it.
            match calleeName callee with
            | some nm =>
              if nm == "__builtin_strcmp" || nm == "strcmp" then
                runStrcmp vs
              else if nm == "__builtin_sprintf" || nm == "sprintf" then
                runSprintf vs
              else if nm == "__builtin_strcpy" then
                runBuiltinStrcpy vs
              else if nm == "strlen" then
                runStrlen vs
              else if nm == "__builtin_bswap16" then
                runBswap16 vs
              else if nm == "__builtin_bswap32" then
                runBswap32 vs
              else if nm == "__builtin_abs" || nm == "abs" then
                runAbs vs
              else if nm == "__sync_add_and_fetch_8" then
                runSyncAdd8 vs
              else if nm == "printf" || nm == "__builtin_printf" then
                runPrintf vs
              else if nm == "abort" || nm == "exit" then
                throw (.libc nm)
              else match prog.findId? declaration with
                | none =>
                    if nm == "memset" || nm == "__builtin_memset" then runMemset vs
                    else if nm == "memcpy" || nm == "__builtin_memcpy" then runMemcpy vs
                    else if nm == "__builtin_strcmp" then runStrcmp vs
                    else if nm == "__builtin_memcmp" then runMemcmp vs
                    else if nm == "__builtin_strlen" then runStrlen vs
                    else if nm == "__builtin_alloca" then runAlloca vs
                    else if nm == "__builtin_ffs" then runFfs vs
                    else if nm == "__builtin_mul_overflow" then runArithOverflow "mul" vs
                    else if nm == "__builtin_add_overflow" then runArithOverflow "add" vs
                    else throw (.libc nm)
                | some g => callFn fuel prog g vs
            | none => match prog.findId? declaration with
              | none => throw (.libc declaration.value)
              | some g => callFn fuel prog g vs
          | none => match calleeName callee with
          | none =>
            -- A DeclRefExpr to a local variable is not a function call target.
            -- Do not redo clang's resolved declaration identity by its name.
            refuseUnsupported "indirect call through a non-FunctionDecl reference"
          | some nm => match prog.find? nm with
            -- One of the 27 externals: cause `libc`, which retires by
            -- widening the slice and never pools with the other two.
            | none =>
              if nm == "__builtin_strcmp" || nm == "strcmp" then runStrcmp vs
              else if nm == "__builtin_sprintf" || nm == "sprintf" then runSprintf vs
              else if nm == "__builtin_strcpy" then runBuiltinStrcpy vs
              else if nm == "strlen" then runStrlen vs
              else if nm == "printf" || nm == "__builtin_printf" then runPrintf vs
              else if nm == "memset" || nm == "__builtin_memset" then runMemset vs
              else if nm == "memcpy" || nm == "__builtin_memcpy" then runMemcpy vs
              else if nm == "__builtin_strcmp" then runStrcmp vs
              else if nm == "__builtin_memcmp" then runMemcmp vs
              else if nm == "__builtin_strlen" then runStrlen vs
              else if nm == "__builtin_bswap16" then runBswap16 vs
              else if nm == "__builtin_bswap32" then runBswap32 vs
              else if nm == "__builtin_abs" || nm == "abs" then runAbs vs
              else if nm == "__sync_add_and_fetch_8" then runSyncAdd8 vs
              else if nm == "__builtin_alloca" then runAlloca vs
              else if nm == "__builtin_ffs" then runFfs vs
              else if nm == "__builtin_mul_overflow" then runArithOverflow "mul" vs
              else if nm == "__builtin_add_overflow" then runArithOverflow "add" vs
              else throw (.libc nm)
            -- A NESTED call to a defined function. `evalArgs` has already
            -- evaluated `vs` in the CALLER's scope (§6.5.3.3p4), so this is
            -- the ordinary call, one fuel down — the recursion this whole
            -- definition is built around, and the arm that used to refuse.
            | some g => callFn fuel prog g vs
        -- §6.2.1p4: the frame starts with the file-scope objects in scope,
        -- and the parameters are bound ON TOP of them, so a parameter that
        -- shadows a global wins by being consed later.
        let ctx0 : Ctx :=
          ({ env := prog.globals, idEnv := prog.globalIds, enums := prog.enums,
             enumIds := prog.enumIds, layout := prog.layout,
             call := handler } : Ctx).withCompoundInit
        let ctx ← bindParams prog.layout ctx0 f.params args
        let flow ← execStmt fuel ctx body
        let m₁ ← get
        set (m₁.killFrom base)
        match flow with
        | .ret (some v) => pure v
        | .ret none => pure .undef
        -- §5.1.2.3.4: falling off the end of a non-void function is
        -- undefined ONLY if the caller uses the value; `main` is the
        -- exception and returns 0. Neither is decided here.
        | .normal => pure .undef
        | _ => refuseUnsupported "break, continue or goto escaped a function body"

/-- Call by NAME — the entry point a scoreboard uses. -/
def callByName (fuel : Nat) (prog : Program) (name : String) (args : List CVal) :
    ExecM CVal :=
  match prog.find? name with
  | some f =>
      -- C23 §5.1.2.2.1 permits the hosted two-parameter form of `main`.
      -- The runner starts the program with the executable name as argv[0],
      -- so argc is one.  The argv object itself is not modelled yet; passing
      -- a null pointer keeps any dereference loud through the existing
      -- provenance checks.  This exception is only for the entrypoint: an
      -- ordinary function with omitted arguments remains a refusal.
      let startupArgs :=
        if name == "main" && args.isEmpty && f.params.length == 2 then
          [.int IntTy.int_ 1, .ptr Ptr.null]
        else args
      callFn fuel prog f startupArgs
  | none => refuseUnsupported s!"no definition for '{name}'"

/-! ## `fuelMono` — still an obligation, and now with a known technique

The lemma every `∃ n, ∀ fuel ≥ n` argument rests on
(`docs/c-semantics-design.md` §4.2): more fuel never changes a decided
answer.

**NOT PROVED HERE, and the reason is worth recording rather than
apologising for.**

*The technique is no longer open.* `LeanModels/Sv/Obs.lean` already
solves this exact problem: a flat approximation order `⊑` with `timeout`
at the bottom, `fuelMono` stated as ONE CONJUNCTION over the whole mutual
block, proved by induction on fuel with a `le_bind` congruence doing the
work at each operator. **96 lines for four functions.** This lane should
LIFT that machinery, not write a second copy of it — the `⊑` order and
its bind congruence are generic in the result type, and a second
hand-rolled monotonicity order is precisely the duplication
`docs/family-architecture.md` §9.2 exists to stop.

*What makes it more than a transcription here.* This mutual block is TEN
functions, not four — `execStmt`, `execBlock`, `execLoop`, `declare`,
`initObject`, `initElems`, `initMembers`, `zeroInit`, `zeroElems`,
`zeroMembers` — so the conjunction has ten conjuncts. And where SV's
functions return a result directly, these return a MONADIC value, so
monotonicity is pointwise in the memory: `∀ m, run m (f fuel …) ⊑ run m
(f fuel' …)`. Both are mechanical against the template; neither is free.

*Why it was not attempted in this session, specifically.* Proof
iteration needs many short Lean runs, and under build-lock Amendment 11
every one of them needs a tenure — which cost this lane **88 minutes** of
FIFO queueing on its last landing. A 300-line proof developed at one
compile per tenure is not a session's work; it is a week's. **That is the
lock's real cost on PROOF work as distinct from build verification**, and
it is a different shape of problem from the starvation the ticket queue
fixed. Reported rather than worked around.

So the obligation is stated as a `Prop` below — visible, named, and
impossible to mistake for a theorem. -/

/-- More fuel never turns a decided answer into a different one.

`Loud.timeout` is the bottom: a run that exhausted its fuel may become
anything at higher fuel, and a run that DECIDED keeps its exact answer,
memory included. -/
def FuelMono : Prop :=
  ∀ (fuel : Nat) (ctx : Ctx) (s : Stmt) (m : Mem) (r : Except Refusal Flow) (m' : Mem),
    ExecM.run m (execStmt fuel ctx s) = .ok (r, m') →
    ∀ fuel' ≥ fuel, ExecM.run m (execStmt fuel' ctx s) = .ok (r, m')

end LeanModels.C.C23
