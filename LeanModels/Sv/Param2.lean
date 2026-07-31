import LeanModels.Sv.Param

/-!
# SV parametric lowering to the semantic tier (`PDesign.instantiate2`)

The `Design2` twin of `Param.lean`'s `instantiate`: substitutes concrete
parameter values into a symbolic sv-0.2 envelope and lowers the FULL
semantic-tier vocabulary — selects (constant and dynamic index, read and
write), part-selects, replication, reductions, casts/signed comparisons,
bitwise resize, `case`/`case inside`, and async active-low reset processes
— into `Sem2.lean`'s `Design2`, which runs under `run2`.

Shared with `Param.lean` (single source of truth, no second copy):
`evalInt` (the constant tier, now with `bitSel`/`partSel` constant rules),
`genvarSeq`/`stepDelta` (generate iteration), `bindLocals`/`bindEnums`,
`IEnv`, and `PDesign.crossCheck` (the load-time differential gate).

## Element widths (the T-array design, honest version)

No CV32E40P provable file uses unpacked arrays for state: `fifo.mem_q` and
`register_file.mem` are **multi-dim packed** vectors, so "array" state is
ONE `LVec` and `m[i]` reads/writes the `elemW`-bit chunk at offset
`i*elemW`. `elemW` is a per-declaration fact — the product of the widths of
every packed dimension after the first (`1` for 1-D vectors and enums) —
computed here at instantiation and stored in the select nodes, never in the
state. A part-select over a multi-dim outer dimension selects whole chunks
(`offset = lsb*elemW`, `width = (msb-lsb+1)*elemW`; with `elemW = 1` this
is the ordinary 1-D rule).

## Value-tier decisions beyond `Param.lean`'s ledger

* A select whose base is a *parameter* (fifo's `FIFO_DEPTH[ADDR_DEPTH:0]`)
  is a constant — folded by `evalInt`'s new select rules and materialized
  at context width.
* A select index that constant-evaluates (genvar arithmetic like
  `2**level-1+l`) lowers to a constant `slice`; anything else stays a
  dynamic `index` node with the pinned x/OOB semantics.
* Part-select bounds must constant-evaluate (the LRM requires constant
  bounds); a failure is loud.
* `Resize` lowers to the **instantiated context width** (the envelope's
  `width` field is defaults-elaborated metadata) — this is what makes
  width conversions correct at every family point, and why the extractor
  never folds unsigned width conversions in symbolic mode.
* `$signed`/`$unsigned` casts are width-preserving bit identities and
  vanish; signedness survives in the operator (`s<` … lower to `scmp`).
* `case` subjects give their self-determined width to every pattern
  (enum labels and `Int` patterns materialize at the subject's width).
-/

namespace LeanModels.Sv

/-! ## Element widths -/

/-- Element width of a declared type: product of the packed-dim widths
AFTER the first dimension (`1` for scalars, 1-D vectors, and enums). -/
def PType.elemWidth (env : IEnv) : PType → Except String Nat
  | .packed [] _ => .ok 1
  | .packed (_ :: rest) _ =>
      rest.foldlM (fun acc d => do pure (acc * (← d.width env))) 1
  | .typeRef .. => .ok 1
  | .unrecoverable _ => .error "unrecoverable packed dimensions"

/-- `(name, elemW)` for every declaration, in order (widths threaded like
`buildDecls` — `$bits`/`$high` in later bounds may look back). -/
def buildElems (env : IEnv) : List PDecl → Res (List (String × Nat))
  | [] => .ok []
  | pd :: rest => do
      match pd.type.width env, pd.type.elemWidth env with
      | .ok w, .ok ew => do
          let es ← buildElems { env with widths := (pd.name, w) :: env.widths } rest
          .ok ((pd.name, ew) :: es)
      | .error e, _ | _, .error e => Res.unsupported s!"decl '{pd.name}': {e}"

/-- Element width of a select *base* expression: a declared signal's
`elemW`; one level of select strips one dimension (the provable files are
at most 2-D, so a chunk's elements are bits); a part-select keeps the
element shape. `none` = outside the tier (loud at the caller). -/
def elemOf (elems : List (String × Nat)) : PExpr → Option Nat
  | .ident n => elems.lookup n
  | .bitSel .. => some 1
  | .partSel b _ _ => elemOf elems b
  | .cast _ a => elemOf elems a
  | _ => none

/-! ## Self-determined widths (full semantic-tier version) -/

mutual
/-- `selfWidth` twin that also knows the semantic-tier nodes (element
widths from `elems`). -/
def selfWidth2 (env : IEnv) (elems : List (String × Nat)) : PExpr → Option Nat
  | .lit v => some v.width
  | .ident n => env.widths.lookup n
  | .paramRef n _ => some ((env.pwidths.lookup n).getD 32)
  | .genvarRef _ | .int _ | .sysCall .. => some 32
  | .enumRef ty _ _ => env.enums.lookup ty
  | .fill _ => none
  | .unary op a =>
      match op with
      | .m0 .lnot => some 1
      | .m0 _ | .plus => selfWidth2 env elems a
      | .inc | .dec => none
  | .binary op l r =>
      match op with
      | .m0 .eq | .m0 .ne | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge
      | .slt | .sle | .sgt | .sge | .ceq | .cne | .land | .lor => some 1
      | .shl | .shr | .ashl | .ashr | .pow => selfWidth2 env elems l
      | _ =>
          match selfWidth2 env elems l, selfWidth2 env elems r with
          | some a, some b => some (max a b)
          | some a, none => some a
          | none, some b => some b
          | none, none => none
  | .ternary _ t e =>
      match selfWidth2 env elems t, selfWidth2 env elems e with
      | some a, some b => some (max a b)
      | some a, none => some a
      | none, some b => some b
      | none, none => none
  | .concat parts => selfWidthSum2 env elems parts
  | .resize w _ => some w
  | .squash2 w _ => some w
  | .bitSel base _ => elemOf elems base
  | .partSel base msb lsb =>
      match elemOf elems base, evalInt env msb, evalInt env lsb with
      | some ew, .ok m, .ok l =>
          if l ≤ m && 0 ≤ l then some (((m - l).toNat + 1) * ew) else none
      | _, _, _ => none
  | .repl count arg =>
      match evalInt env count, selfWidth2 env elems arg with
      | .ok n, some w => if 0 ≤ n then some (n.toNat * w) else none
      | _, _ => none
  | .reduce .. => some 1
  | .cast _ a => selfWidth2 env elems a
  | .unsupported .. => none

def selfWidthSum2 (env : IEnv) (elems : List (String × Nat)) : List PExpr → Option Nat
  | [] => some 0
  | p :: rest =>
      match selfWidth2 env elems p, selfWidthSum2 env elems rest with
      | some a, some b => some (a + b)
      | _, _ => none
end

/-! ## The value tier: `instExpr2` -/

private def intLit2 (ctx : Option Nat) (v : Int) : Expr2 :=
  .lit (LVec.ofInt (ctx.getD 32) v)

/-- Expressions whose instantiated width is INTRINSIC (context-independent):
declared signals, sized literals, selects, concats, replications,
reductions — plus casts of such. Everything else is context-directed
(`Int`/`Fill`/parameter literals materialize at the context width;
arithmetic/ternary propagate it). A rigid operand in a wider/narrower
operator context needs an explicit `resize` (LRM §11.8.2 zero-extension /
truncation) — the `fitExpr2` wrapper below. -/
def rigidExpr : PExpr → Bool
  | .lit _ | .ident _ | .bitSel .. | .partSel .. | .concat _
  | .repl .. | .reduce .. => true
  | .cast _ a => rigidExpr a
  | _ => false

private def maxW2 : Option Nat → Option Nat → Option Nat
  | some a, some b => some (max a b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

mutual
/-- Lower a value-position expression to `Expr2` at context width `ctx`.
Total: failures are loud `Expr2.unsupported` nodes, reached-sensitive. -/
def instExpr2 (env : IEnv) (elems : List (String × Nat)) (ctx : Option Nat) :
    PExpr → Expr2
  | .lit v => .lit v
  | .ident n => .ident n
  | .int v => intLit2 ctx v
  | .fill b =>
      match ctx with
      | some w => .lit (LVec.replicate w b)
      | none => .unsupported "Fill:width" "no context width for unbased-unsized literal"
  | .paramRef n none =>
      match env.vals.lookup n with
      | some v => intLit2 ctx v
      | none => .unsupported "ParamRef:unbound" n
  | .paramRef n (some p) => .unsupported "ParamRef:package" s!"{p}::{n}"
  | .genvarRef n =>
      match env.vals.lookup n with
      | some v => intLit2 ctx v
      | none => .unsupported "GenvarRef:unbound" n
  | .enumRef ty mem _ =>
      match env.members.lookup (ty, mem) with
      | some v => .lit v
      | none => .unsupported "EnumRef:unknown" s!"{ty}::{mem}"
  | .unary op a =>
      match op with
      | .m0 .lnot => .unary .lnot (instExpr2 env elems none a)
      | .m0 uop => .unary uop (instExpr2 env elems (maxW2 ctx (selfWidth2 env elems a)) a)
      | .plus => instExpr2 env elems ctx a
      | .inc | .dec => .unsupported "UnaryExpression:incdec" ""
  | .binary op l r =>
      match op with
      | .m0 .add | .m0 .sub | .m0 .and | .m0 .or | .m0 .xor =>
          let octx := match ctx with
            | some w => some w
            | none => maxW2 (selfWidth2 env elems l) (selfWidth2 env elems r)
          .binary (match op with | .m0 bop => bop | _ => .add)
            (fitExpr2 env elems octx l) (fitExpr2 env elems octx r)
      | .m0 .eq | .m0 .ne | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge =>
          let octx := maxW2 (selfWidth2 env elems l) (selfWidth2 env elems r)
          .binary (match op with | .m0 bop => bop | _ => .eq)
            (fitExpr2 env elems octx l) (fitExpr2 env elems octx r)
      | .slt | .sle | .sgt | .sge =>
          let octx := maxW2 (selfWidth2 env elems l) (selfWidth2 env elems r)
          .scmp (match op with
              | .slt => .lt | .sle => .le | .sgt => .gt | _ => .ge)
            (fitExpr2 env elems octx l) (fitExpr2 env elems octx r)
      | .land | .lor =>
          -- Operands are self-determined (§11.4.7), result 1 bit.
          .logical (op == .land)
            (instExpr2 env elems (selfWidth2 env elems l) l)
            (instExpr2 env elems (selfWidth2 env elems r) r)
      | _ =>
          match evalInt env (.binary op l r) with
          | .ok v => intLit2 ctx v
          | .error e => .unsupported s!"BinaryExpression:{op.sym}" e
  | .ternary c t e =>
      let actx := match ctx with
        | some w => some w
        | none => maxW2 (selfWidth2 env elems t) (selfWidth2 env elems e)
      .ternary (instExpr2 env elems none c)
        (fitExpr2 env elems actx t) (fitExpr2 env elems actx e)
  | .concat parts => .concat (instParts2 env elems parts).toArray
  | .resize w a =>
      -- Target width = the CONTEXT at the current parameters (the
      -- envelope's `w` is defaults-elaborated metadata, used only when
      -- no context width is known).
      .resize (ctx.getD w) (instExpr2 env elems (selfWidth2 env elems a) a)
  | .squash2 .. => .unsupported "Squash2" "2-state squash outside the value core"
  | .sysCall fn a =>
      match evalInt env (.sysCall fn a) with
      | .ok v => intLit2 ctx v
      | .error e => .unsupported "SysCall" e
  | .bitSel base idx =>
      match evalInt env (.bitSel base idx) with
      | .ok v => intLit2 ctx v  -- parameter-based select: a constant
      | .error _ =>
          match elemOf elems base with
          | none => .unsupported "BitSel:base" "select base outside the declared-signal tier"
          | some ew =>
              let base' := instExpr2 env elems (selfWidth2 env elems base) base
              match evalInt env idx with
              | .ok i =>
                  if 0 ≤ i then .slice base' (i.toNat * ew) ew
                  else .unsupported "BitSel:index" "negative constant index"
              | .error _ =>
                  .index base' (instExpr2 env elems (selfWidth2 env elems idx) idx) ew
  | .partSel base msb lsb =>
      match evalInt env (.partSel base msb lsb) with
      | .ok v => intLit2 ctx v  -- parameter-based part select: a constant
      | .error _ =>
          match elemOf elems base, evalInt env msb, evalInt env lsb with
          | some ew, .ok m, .ok l =>
              if 0 ≤ l && l ≤ m then
                .slice (instExpr2 env elems (selfWidth2 env elems base) base)
                  (l.toNat * ew) (((m - l).toNat + 1) * ew)
              else .unsupported "PartSel:bounds" s!"[{m}:{l}]"
          | none, _, _ => .unsupported "PartSel:base" "select base outside the declared-signal tier"
          | _, .error e, _ | _, _, .error e => .unsupported "PartSel:bounds" e
  | .repl count arg =>
      match evalInt env count with
      | .ok n =>
          if 0 ≤ n then
            .repl n.toNat (instExpr2 env elems (selfWidth2 env elems arg) arg)
          else .unsupported "Repl:count" "negative replication count"
      | .error e => .unsupported "Repl:count" e
  | .reduce op arg =>
      .reduce op (instExpr2 env elems (selfWidth2 env elems arg) arg)
  | .cast _ a => instExpr2 env elems ctx a
  | .unsupported k t => .unsupported k t

/-- Concat parts are self-determined (unsized literals in concats are
illegal SV — loud via the `Fill` arm). -/
def instParts2 (env : IEnv) (elems : List (String × Nat)) : List PExpr → List Expr2
  | [] => []
  | p :: rest =>
      instExpr2 env elems (selfWidth2 env elems p) p :: instParts2 env elems rest

/-- Instantiate an operand at context width `ctx`, wrapping RIGID
expressions whose intrinsic width differs in an explicit `resize`
(zero-extension / truncation, LRM §11.8.2) — e.g. a 4-bit counter compared
against an unsized `0` extends to the comparison width. Context-directed
expressions take `ctx` unchanged. -/
def fitExpr2 (env : IEnv) (elems : List (String × Nat)) (ctx : Option Nat)
    (e : PExpr) : Expr2 :=
  match ctx with
  | none => instExpr2 env elems none e
  | some tw =>
      if rigidExpr e then
        match selfWidth2 env elems e with
        | some sw =>
            if sw == tw then instExpr2 env elems (some sw) e
            else .resize tw (instExpr2 env elems (some sw) e)
        | none => instExpr2 env elems ctx e
      else instExpr2 env elems ctx e
end

/-! ## Targets, statements, processes -/

/-- Lower an assignment target: `(Lhs2, context width for the RHS)`.
Loud (`.error`) on non-constant part-select bounds, undeclared names, or
negative indices — the caller degrades to `Stmt2.unsupported`. -/
def instLhs2 (env : IEnv) (elems : List (String × Nat)) :
    PLhs → Except String (Lhs2 × Nat)
  | .ident n =>
      match env.widths.lookup n with
      | some w => .ok (.ident n, w)
      | none => .error s!"assignment target '{n}' undeclared"
  | .bitSel n idx =>
      match elems.lookup n with
      | none => .error s!"assignment target '{n}' undeclared"
      | some ew =>
          match evalInt env idx with
          | .ok i =>
              if 0 ≤ i then .ok (.slice n (i.toNat * ew) ew, ew)
              else .error "negative constant index"
          | .error _ =>
              .ok (.index n (instExpr2 env elems (selfWidth2 env elems idx) idx) ew, ew)
  | .partSel n msb lsb =>
      match elems.lookup n, evalInt env msb, evalInt env lsb with
      | some ew, .ok m, .ok l =>
          if 0 ≤ l && l ≤ m then
            .ok (.slice n (l.toNat * ew) (((m - l).toNat + 1) * ew),
                 ((m - l).toNat + 1) * ew)
          else .error s!"bad part-select bounds [{m}:{l}]"
      | none, _, _ => .error s!"assignment target '{n}' undeclared"
      | _, .error e, _ | _, _, .error e => .error s!"part-select bound: {e}"

mutual
/-- Lower a statement to `Stmt2`. -/
def instStmt2 (env : IEnv) (elems : List (String × Nat)) : PStmt → Stmt2
  | .blockingAssign t v =>
      .blockingAssign (.ident t) (fitExpr2 env elems (env.widths.lookup t) v)
  | .nbaAssign t v =>
      .nbaAssign (.ident t) (fitExpr2 env elems (env.widths.lookup t) v)
  | .blockingAssignL lhs v =>
      match instLhs2 env elems lhs with
      | .ok (l2, w) => .blockingAssign l2 (fitExpr2 env elems (some w) v)
      | .error e => .unsupported "AssignL" e
  | .nbaAssignL lhs v =>
      match instLhs2 env elems lhs with
      | .ok (l2, w) => .nbaAssign l2 (fitExpr2 env elems (some w) v)
      | .error e => .unsupported "AssignL" e
  | .ifStmt c th el =>
      .ifStmt (instExpr2 env elems none c) (instStmt2 env elems th)
        (match el with
         | some s => some (instStmt2 env elems s)
         | none => none)
  | .block body => .block (instStmts2 env elems body).toArray
  | .caseStmt subj items dflt inside check =>
      let sctx := selfWidth2 env elems subj
      .caseStmt (instExpr2 env elems sctx subj)
        (instItems2 env elems sctx items).toArray
        (match dflt with
         | some s => some (instStmt2 env elems s)
         | none => none)
        inside check
  | .unsupported k t => .unsupported k t

/-- Case items: patterns at the subject's width, bodies recursively. -/
def instItems2 (env : IEnv) (elems : List (String × Nat)) (sctx : Option Nat) :
    List (List PExpr × PStmt) → List CaseItem2
  | [] => []
  | (pats, body) :: rest =>
      .mk (instPats2 env elems sctx pats).toArray (instStmt2 env elems body)
        :: instItems2 env elems sctx rest

def instPats2 (env : IEnv) (elems : List (String × Nat)) (sctx : Option Nat) :
    List PExpr → List Expr2
  | [] => []
  | p :: rest => fitExpr2 env elems sctx p :: instPats2 env elems sctx rest

def instStmts2 (env : IEnv) (elems : List (String × Nat)) : List PStmt → List Stmt2
  | [] => []
  | s :: rest => instStmt2 env elems s :: instStmts2 env elems rest
end

/-- Lower a process to `Process2`. -/
def instProcess2 (env : IEnv) (elems : List (String × Nat)) : PProcess → Process2
  | .alwaysFF c b => .alwaysFF c (instStmt2 env elems b)
  | .alwaysPlain c b => .alwaysPlain c (instStmt2 env elems b)
  | .alwaysComb b => .alwaysComb (instStmt2 env elems b)
  | .alwaysFFR c rn b => .alwaysFFR c rn (instStmt2 env elems b)
  | .assign t v =>
      match env.widths.lookup t with
      | some w => .assign (.ident t) (fitExpr2 env elems (some w) v)
      | none => .unsupported "Assign" s!"assign target '{t}' undeclared"
  | .assignL lhs v =>
      match instLhs2 env elems lhs with
      | .ok (l2, w) => .assign l2 (fitExpr2 env elems (some w) v)
      | .error e => .unsupported "AssignL" e
  | .unsupported k t => .unsupported k t

/-! ## Generate expansion (Process2 mirror of `Param.lean`'s) -/

mutual
def GenItem.expand2 (env : IEnv) (elems : List (String × Nat)) (iterFuel : Nat) :
    GenItem → Res (List Process2)
  | .process p => .ok [instProcess2 env elems p]
  | .unsupported k t => .ok [.unsupported k t]
  | .genIf cond thenB elseB =>
      match evalInt env cond with
      | .error e => .unsupported s!"generate if: {e}"
      | .ok v =>
          if v != 0 then expandList2 env elems iterFuel thenB
          else expandList2 env elems iterFuel elseB
  | .genFor _label g initE bound step _rc body =>
      match evalInt env initE, stepDelta g step with
      | .ok i0, .ok δ => do
          let vs ← genvarSeq env g bound δ iterFuel i0
          expandIters2 env elems iterFuel g vs body
      | .error e, _ => .unsupported s!"generate for: {e}"
      | _, .error e => .unsupported s!"generate for: {e}"
  termination_by it => (sizeOf it, 0)
  decreasing_by all_goals (simp_wf; omega)

def expandList2 (env : IEnv) (elems : List (String × Nat)) (iterFuel : Nat) :
    List GenItem → Res (List Process2)
  | [] => .ok []
  | it :: rest => do
      let ps ← it.expand2 env elems iterFuel
      let qs ← expandList2 env elems iterFuel rest
      .ok (ps ++ qs)
  termination_by l => (sizeOf l, 0)
  decreasing_by all_goals (simp_wf; omega)

def expandIters2 (env : IEnv) (elems : List (String × Nat)) (iterFuel : Nat)
    (g : String) : List Int → List GenItem → Res (List Process2)
  | [], _ => .ok []
  | v :: vs, body => do
      let ps ← expandList2 (env.bindVal g v) elems iterFuel body
      let qs ← expandIters2 env elems iterFuel g vs body
      .ok (ps ++ qs)
  termination_by vs body => (sizeOf body, vs.length + 1)
  decreasing_by all_goals (simp_wf; omega)
end

/-! ## `instantiate2` -/

/-- The loud error design of the semantic tier. -/
def Design2.errorDesign (name msg : String) : Design2 :=
  { name, decls := #[], processes := #[.unsupported "Instantiate" msg] }

/-- Instantiate a parametric design at concrete parameter values into the
semantic tier (`Design2`). Same discipline as `PDesign.instantiate`:
loud `.unsupported` on bad parameters, `.timeout` on generate fuel; out-of-
tier constructs become in-design loud nodes, never silent. -/
def PDesign.instantiate2 (d : PDesign) (args : List Int) (iterFuel : Nat := 4096) :
    Res Design2 :=
  if args.length != d.params.length then
    .unsupported s!"parameter arity: got {args.length}, want {d.params.length}"
  else do
    let env0 : IEnv := { vals := (d.params.map (·.name)).zip args }
    let env1 ← bindLocals env0 d.localParams
    let env2 ← bindEnums env1 d.enums
    -- Declared widths of typed parameters/localparams (self-determined
    -- widths of ParamRefs in value positions; untyped = 32-bit int).
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
    let decls ← buildDecls env2 d.decls
    let elems ← buildElems env2 d.decls
    let envP := { env2 with widths := decls.map fun dc => (dc.name, dc.width) }
    let gens ← expandList2 envP elems iterFuel d.generates
    .ok { name := d.name
          decls := decls.toArray
          processes :=
            ((d.processes.map (instProcess2 envP elems)) ++ gens
              ++ d.others.map fun (k, t) => Process2.unsupported k t).toArray }

/-- Total `Design2` family (the `load_design_sv2` binder encoding's
semantic-tier twin): errors collapse to the loud error design. -/
def PDesign.instantiateD2 (d : PDesign) (args : List Int) : Design2 :=
  match d.instantiate2 args (PDesign.surfaceFuel args) with
  | .ok m => m
  | .timeout => .errorDesign d.name "generate expansion fuel exhausted"
  | .unsupported msg => .errorDesign d.name msg

/-! ## Hand-built smoke: a mini ff_one (select writes from a generate
family), a case FSM, and an async-reset register — all three semantic-tier
mechanisms end-to-end under `run2`. -/

private def wm1' : PDim := ⟨.binary (.m0 .sub) (.paramRef "W" none) (.int 1), .int 0⟩

/-- `gen_or(W)`: `assign y[j] = a[j] | a[j+1]` for j < W-1 — select reads
AND select writes with genvar-constant indices, expanded structurally. -/
private def pGenOr : PDesign :=
  { name := "gen_or"
    params := [{ name := "W", default? := some (.int 4), resolved? := some 4 }]
    localParams := []
    enums := []
    decls := [
      { name := "a", type := .packed [wm1'] (some 4), isInput := true },
      { name := "y", type := .packed [wm1'] (some 4), isOutput := true }]
    processes := []
    generates := [
      .genFor (some "g") "j" (.int 0)
        (.binary .slt (.genvarRef "j")
          (.binary (.m0 .sub) (.paramRef "W" none) (.int 1)))
        (.unary .inc (.genvarRef "j")) (some 3)
        [.process (.assignL (.bitSel "y" (.genvarRef "j"))
          (.binary (.m0 .or)
            (.bitSel (.ident "a") (.genvarRef "j"))
            (.bitSel (.ident "a") (.binary (.m0 .add) (.genvarRef "j") (.int 1)))))]]
    others := [] }

#guard pGenOr.crossCheck == []
-- W=4: y[2:0] driven, y[3] undriven (stays x): a=1000 → y=x100.
#guard (Res.toOption (run2 (pGenOr.instantiateD2 [4]) σ_src 64
        [[("a", LVec.lit "1000")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "y")
      == some ["x100"]
-- Same family at W=8, nothing re-extracted: a=00010010 → y=x0011011.
#guard (Res.toOption (run2 (pGenOr.instantiateD2 [8]) σ_src 64
        [[("a", LVec.lit "00010010")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "y")
      == some ["x0011011"]

/-- `rcase(W)`: async-reset register + plain case over a 2-bit opcode —
`alwaysFFR`, `caseStmt`, dynamic `index` write, and `Fill` reset values
in one design. -/
private def pRcase : PDesign :=
  { name := "rcase"
    params := [{ name := "W", default? := some (.int 4), resolved? := some 4 }]
    localParams := []
    enums := []
    decls := [
      { name := "clk", type := .packed [] (some 1), isInput := true },
      { name := "rst_n", type := .packed [] (some 1), isInput := true },
      { name := "op", type := .packed [⟨.int 1, .int 0⟩] (some 2), isInput := true },
      { name := "i", type := .packed [⟨.int 1, .int 0⟩] (some 2), isInput := true },
      { name := "q", type := .packed [wm1'] (some 4), isOutput := true }]
    processes := [
      .alwaysFFR "clk" "rst_n"
        (.ifStmt (.unary (.m0 .lnot) (.ident "rst_n"))
          (.nbaAssign "q" (.fill .l0))
          (some (.caseStmt (.ident "op")
            [([.lit (.ofNat 2 1)], .nbaAssignL (.bitSel "q" (.ident "i")) (.lit (.ofNat 1 1))),
             ([.lit (.ofNat 2 2)], .nbaAssign "q" (.unary (.m0 .bnot) (.ident "q")))]
            (some (.nbaAssign "q" (.ident "q"))) false .none)))]
    generates := []
    others := [] }

#guard pRcase.crossCheck == []
-- reset, then set bit 2, then set bit 0, then invert; then an x index
-- write (no-op: q holds), then reset again mid-stream.
#guard (Res.toOption (run2 (pRcase.instantiateD2 [4]) σ_src 64
        [[("rst_n", LVec.lit "0"), ("op", LVec.ofNat 2 0), ("i", LVec.ofNat 2 0)],
         [("rst_n", LVec.lit "1"), ("op", LVec.ofNat 2 1), ("i", LVec.ofNat 2 2)],
         [("i", LVec.ofNat 2 0)],
         [("op", LVec.ofNat 2 2)],
         [("op", LVec.ofNat 2 1), ("i", LVec.lit "xx")],
         [("rst_n", LVec.lit "0")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "q")
      == some ["0000", "0100", "0101", "1010", "1010", "0000"]

-- Bad parameters stay loud on the semantic tier too.
#guard (match pRcase.instantiate2 [] with
        | .unsupported msg => msg == "parameter arity: got 0, want 1"
        | _ => false)
#guard run2 (pRcase.instantiateD2 []) σ_src 64 [[]]
        == .unsupported "unsupported process 'Instantiate'"

/-- Regression (cv32e40p_fifo `empty_o`, diff rows `fifo_d8_w32`/
`fifo_d4_w8` vs Xcelium AND Icarus): a DECLARED 1-bit parameter type
(`parameter bit P`) must give ParamRefs self-determined width 1.
The envelope used to drop 2-state/signed declared parameter types to
`type: null` (indistinguishable from implicit = 32-bit int), so
`(cnt == 0) & ~(P & push)` widened `~(P & push)` to 32 bits against the
1-bit `==` — a width-mismatched `&` whose x poisoned `empty_o` on every
cycle. The extractor now emits a width-only `PackedType` for such types
(`_param_width_type`); this design replays the shape at both `P` values. -/
private def pBitParam : PDesign :=
  { name := "bp"
    params := [{ name := "P", type? := some (.packed [] (some 1)),
                 default? := some (.lit (LVec.lit "0")), resolved? := some 0 }]
    localParams := []
    enums := []
    decls := [
      { name := "cnt", type := .packed [⟨.int 3, .int 0⟩] (some 4), isInput := true },
      { name := "push", type := .packed [] (some 1), isInput := true },
      { name := "e", type := .packed [] (some 1), isOutput := true }]
    processes := [
      .assign "e" (.binary (.m0 .and)
        (.binary (.m0 .eq) (.ident "cnt") (.int 0))
        (.unary (.m0 .bnot)
          (.binary (.m0 .and) (.paramRef "P" none) (.ident "push"))))]
    generates := []
    others := [] }

#guard pBitParam.crossCheck == []
-- P=0: e = (cnt == 0) — known at every row, never x (the pinned fact).
#guard (Res.toOption (run2 (pBitParam.instantiateD2 [0]) σ_src 64
        [[("cnt", LVec.ofNat 4 0), ("push", LVec.lit "1")],
         [("cnt", LVec.ofNat 4 3), ("push", LVec.lit "1")],
         [("cnt", LVec.ofNat 4 0), ("push", LVec.lit "0")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "e")
      == some ["1", "0", "1"]
-- P=1: the push side masks the empty flag (fall-through shape).
#guard (Res.toOption (run2 (pBitParam.instantiateD2 [1]) σ_src 64
        [[("cnt", LVec.ofNat 4 0), ("push", LVec.lit "1")],
         [("cnt", LVec.ofNat 4 0), ("push", LVec.lit "0")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "e")
      == some ["0", "1"]

end LeanModels.Sv
