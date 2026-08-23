import Examples.c.sunfish.expr

/-!
# M2 inch 4, INSTANTIATED: the tier RUNS a function of the corpus

Inches 1-3 evaluated expressions. This file is the first time the C
semantics executes a **whole function body taken out of the ingested
translation unit** — `pyfloordiv`, sunfish.c L160-164:

    static int pyfloordiv(int a, int b) {
        int q = a / b, r = a % b;
        if (r != 0 && ((r < 0) != (b < 0))) q--;
        return q;
    }

Three statements: a two-declarator declaration, an `if` whose condition
is the corpus's own `&&`, and a `return`. The charter picked this
function as the tier's first for reasons that pay off here — it is the
site the ctwin README names as **the #1 place C clones silently diverge
from Python**, so what these gates check is not that the model runs, but
that it runs and *agrees with Python* where C alone would not.
-/

namespace Examples.c.sunfish.stmt

open LeanModels.C.C23
open LeanModels.C (CType Expr Stmt)

private def noSpan : LeanModels.C.CSpan := ⟨0, 0, 0, 0, none, none⟩

/-! ## The function, taken from the ingested corpus -/

private def pfd : Option LeanModels.C.FunctionDefn :=
  sunfishC.unit.functionDefns.find? (·.name == "pyfloordiv")

/-- `pyfloordiv`'s body, as ingested. -/
private def pfdBody : Stmt :=
  (pfd.bind (·.body)).getD (.unsupported "missing" "pyfloordiv" noSpan)

-- It is the three-statement compound the source writes, at L160-164.
#guard (pfd.map fun f => (f.ty, f.storage, f.span.line, f.span.endLine))
  == some ("int (int, int)", some "static", 160, 164)
#guard (match pfdBody with | .compound b _ => b.length | _ => 0) == 3

/-! ## The frame `pyfloordiv` runs in

Two `int` parameters, and a layout that knows what an `int` is. Both are
what a caller would supply; inch 5 will supply them from a call site. -/

private def intLayout : Layout where
  size := fun t => if t == "int" then some 4 else none
  fieldOff := fun _ _ => none

private def frame0 : Mem :=
  (((Mem.empty.alloc .automatic 4 (some "int")).1).alloc .automatic 4 (some "int")).1

private def ctxAB : Ctx := { env := [("a", 0), ("b", 1)], layout := intLayout }

private def setI (m : Mem) (o : ObjId) (n : Int) : Mem :=
  (Mem.storeInt m (Ptr.toObject o) IntTy.int_ n).toOption.getD m

/-- Run `pyfloordiv`'s body with the two parameters bound. -/
private def runPfd (a b : Int) : Outcome Flow :=
  ExecM.verdict (setI (setI frame0 0 a) 1 b) (execStmt 64 ctxAB pfdBody)

/-- What the function answered, if it returned one. -/
private def answer (a b : Int) : Option Int :=
  match runPfd a b with
  | .ok (.ret (some (.int _ n))) => some n
  | _ => none

/-! ## THE TIER RUNS A FUNCTION, AND IT AGREES WITH PYTHON

`pyfloordiv` exists to turn C's truncating division into Python's
flooring one. C alone would answer `-3` for `-7 / 2`; Python answers
`-4`. These gates check the corrected value, which is the whole reason
the function is in the corpus. -/

#guard answer 7 2 == some 3          -- 7 // 2   = 3    (no correction)
#guard answer 6 3 == some 2          -- 6 // 3   = 2    (r = 0, no correction)
#guard answer (-7) 2 == some (-4)    -- -7 // 2  = -4   ** C alone: -3 **
#guard answer 7 (-2) == some (-4)    -- 7 // -2  = -4   ** C alone: -3 **
#guard answer (-7) (-2) == some 3    -- -7 // -2 = 3    (signs agree)
#guard answer 1 1 == some 1
#guard answer 0 5 == some 0
#guard answer (-1) 5 == some (-1)    -- -1 // 5  = -1   ** C alone: 0 **

/-- The Python semantics this is being checked against, computed here so
the comparison is a THEOREM about two definitions rather than a table of
numbers someone typed. `Int.fdiv` floors; C's `/` truncates. -/
private def pythonFloorDiv (a b : Int) : Int := Int.fdiv a b

-- The agreement, on every pair above.
#guard [(7,2), (6,3), (-7,2), (7,-2), (-7,-2), (1,1), (0,5), (-1,5)].all
  (fun p => answer p.1 p.2 == some (pythonFloorDiv p.1 p.2))

/-! ## …and it REFUSES where C is undefined

§6.5.6p6 — a zero divisor. The refusal rides in `ExceptT` because
division by zero is UB, which is catchable-in-principle and therefore
carries its memory; contrast the out-of-tier refusals below, which do
not. -/

#guard runPfd 1 0 == .refused (.valueUB (.divideByZero "/"))
#guard (Refusal.valueUB (.divideByZero "/")).j2 == some "J.2(41)"
#guard (Outcome.refused (α := Flow) (.valueUB (.divideByZero "/"))).cause? == some (.undefined () : Cause)

/-! ## §6.8 — the statement forms, gated individually -/

private def sExpr (e : Expr) : Stmt := .expr e noSpan
private def rdA : Expr :=
  .implicitCast "LValueToRValue" (.declRef "a" "VarDecl" "int" noSpan) "int" noSpan
private def lit (n : String) : Expr := .intLit n "int" noSpan
private def run1 (m : Mem) (s : Stmt) : Outcome Flow :=
  ExecM.verdict m (execStmt 64 ctxAB s)

-- §6.8.7.4 — `return`, with and without a value.
#guard run1 frame0 (.ret none noSpan) == .ok (.ret none)
#guard run1 (setI frame0 0 9) (.ret (some rdA) noSpan) == .ok (.ret (some (.int IntTy.int_ 9)))

-- §6.8.7.3 / §6.8.7.2 — `break` and `continue` reach their enclosing loop.
#guard run1 frame0 (.breakS noSpan) == .ok .brk
#guard run1 frame0 (.continueS noSpan) == .ok .cont

-- §6.8.5.1 — the else-less `if` is the common path (51 of 253 carry an else).
#guard run1 (setI frame0 0 0) (.ifS rdA (.ret (some (lit "1")) noSpan) none noSpan)
  == .ok .normal
#guard run1 (setI frame0 0 1) (.ifS rdA (.ret (some (lit "1")) noSpan) none noSpan)
  == .ok (.ret (some (.int IntTy.int_ 1)))

-- §6.8.4 — an expression statement is run for its EFFECTS, value discarded.
#guard run1 frame0 (sExpr (.binop "=" (.declRef "a" "VarDecl" "int" noSpan)
  (lit "5") "int" noSpan)) == .ok .normal

/-! ## §6.8.6 — loops, and the detail a tidy model gets wrong

`for`'s increment runs after a `continue` too (§6.8.6.4p2). A model that
treated `continue` as `break`, or that skipped the increment, would loop
forever — so the gate is that the loop TERMINATES with the right count. -/

/-- `for (a = 0; a < 3; a++) ;` — a bare loop that must run exactly 3 times. -/
private def forLoop (body : Stmt) : Stmt :=
  .forS (some (sExpr (.binop "=" (.declRef "a" "VarDecl" "int" noSpan) (lit "0") "int" noSpan)))
        (some (.binop "<" rdA (lit "3") "int" noSpan))
        (some (.unop "++" (.declRef "a" "VarDecl" "int" noSpan) true "int" noSpan))
        body noSpan

private def afterLoop (body : Stmt) : Option Int :=
  match ExecM.run frame0 (execStmt 64 ctxAB (forLoop body)) with
  | .ok (.ok _, m) => match Mem.loadInt m (Ptr.toObject 0) IntTy.int_ with
                      | .ok (.int _ n) => some n
                      | _ => none
  | _ => none

-- The loop terminates and `a` ends at 3.
#guard afterLoop (.compound [] noSpan) == some 3
-- A `continue` in the body STILL runs the increment, so it still ends at 3.
#guard afterLoop (.continueS noSpan) == some 3
-- A `break` ends the loop immediately, with `a` still 0.
#guard afterLoop (.breakS noSpan) == some 0

/-! ## Fuel — exhaustion is a TIMEOUT, never a refusal

`docs/c23-goal.md` §3: the only exhaustion outcome, never conflated with
REFUSE. It carries no memory, because it observed nothing. -/

#guard ExecM.verdict frame0 (execStmt 0 ctxAB pfdBody) == (.timeout : Outcome Flow)
#guard (Outcome.timeout (α := Flow)).cause? == none
-- …and a timeout is NOT a refusal, which is the whole point of the split.
#guard ExecM.verdict frame0 (execStmt 0 ctxAB pfdBody)
    != Outcome.refused (α := Flow) (.valueUB (.divideByZero "/"))

/-! ## §3.4 — an out-of-tier refusal answers in `Halt`, with its snapshot

The aggregate initializer is the one inch 4 holds (34 `InitListExpr`
sites). It refuses as `unsupported` — the cause that retires by climbing
a rung — and the snapshot it carries never reaches this comparison. -/

#guard run1 frame0 (.unsupported "SwitchStmt" "switch (x) {}" noSpan)
  == .unsupported "out of tier: SwitchStmt"
#guard (Outcome.unsupported (α := Flow) "out of tier: SwitchStmt").cause?
  == some (.unsupported () : Cause)

/-! ## §6.7.11 — aggregate initialization, and the rule that fires on NOTHING

**Measured across all 75 `InitListExpr` nodes in the corpus: every one is
FULL.** No array initializer is shorter than its extent; no structure
initializer omits a member. So §6.7.11p10 — *unmentioned members are
initialized as objects with static storage duration* — **fires on zero
corpus sites**, and the corpus therefore CANNOT check it.

That is the effective-types situation again, and it gets the same
treatment: implement it correctly while nothing exercises it, and gate it
on a SYNTHETIC case, because a rule nobody ran is a rule nobody checked.
-/

/-- `Move` as the corpus declares it, with the offsets inch 2 measured on
both profile hosts, plus a 4-element `int` array and a struct carrying a
POINTER member for the zero-init gate below. -/
private def aggLayout : Layout where
  size := fun t => match t with
    | "int" => some 4 | "char" => some 1 | "Move" => some 12
    | "int[4]" => some 16 | "int[3]" => some 12
    | "struct box" => some 16 | "int *" => some 8
    | _ => none
  fieldOff := fun base f => match base, f with
    | "Move", "i" => some 0 | "Move", "j" => some 4 | "Move", "prom" => some 8
    | "struct box", "n" => some 0 | "struct box", "p" => some 8
    | _, _ => none
  elem := fun t => match t with
    | "int[4]" => some ("int", 4) | "int[3]" => some ("int", 3)
    | _ => none
  members := fun t => match t with
    | "Move" => some [("i", "int"), ("j", "int"), ("prom", "char")]
    | "struct box" => some [("n", "int"), ("p", "int *")]
    | _ => none

private def aggCtx : Ctx := { env := [], layout := aggLayout }
private def iLit (n : String) : Expr := .intLit n "int" noSpan
private def brace (es : List Expr) (ty : CType) : Expr := .initList es ty noSpan

/-- Declare one object of type `ty` with initializer `e`, then read a
member/element back as an `int`. -/
private def declThenRead (ty : CType) (e : Expr) (off : Nat) : Except Refusal CVal :=
  let st : Stmt := .compound [.decl [.var "x" ty none (some e) noSpan] noSpan] noSpan
  match ExecM.run Mem.empty (execStmt 64 aggCtx st) with
  | .ok (.ok _, m) => Mem.loadInt m (Mem.member (Ptr.toObject 0) off) IntTy.int_
  | _ => .error (.libc "did not complete")

-- A FULL structure initializer — the shape all 75 corpus sites have.
#guard declThenRead "Move" (brace [iLit "11", iLit "22", iLit "33"] "Move") 0
  == .ok (.int IntTy.int_ 11)
#guard declThenRead "Move" (brace [iLit "11", iLit "22", iLit "33"] "Move") 4
  == .ok (.int IntTy.int_ 22)

-- A FULL array initializer.
#guard declThenRead "int[3]" (brace [iLit "7", iLit "8", iLit "9"] "int[3]") 0
  == .ok (.int IntTy.int_ 7)
#guard declThenRead "int[3]" (brace [iLit "7", iLit "8", iLit "9"] "int[3]") 8
  == .ok (.int IntTy.int_ 9)

/-! ### THE SYNTHETIC PARTIAL — the only way this rule gets checked

`int a[4] = {7, 8};` appears nowhere in the corpus. §6.7.11p10 says
elements 2 and 3 are zero, and the alternative a model would otherwise
produce is that they stay INDETERMINATE and refuse on read. The gate
distinguishes those two outcomes, which is the whole point. -/

#guard declThenRead "int[4]" (brace [iLit "7", iLit "8"] "int[4]") 0
  == .ok (.int IntTy.int_ 7)
#guard declThenRead "int[4]" (brace [iLit "7", iLit "8"] "int[4]") 4
  == .ok (.int IntTy.int_ 8)
-- …and the two the list never reached are ZERO, not indeterminate.
#guard declThenRead "int[4]" (brace [iLit "7", iLit "8"] "int[4]") 8
  == .ok (.int IntTy.int_ 0)
#guard declThenRead "int[4]" (brace [iLit "7", iLit "8"] "int[4]") 12
  == .ok (.int IntTy.int_ 0)
-- The contrast: with NO initializer at all the object stays indeterminate
-- and the same read REFUSES. So the zero above came from §6.7.11p10 and
-- not from `alloc` happening to hand back zeros.
#guard declThenRead "int[4]" (brace [] "int[4]") 8 == .ok (.int IntTy.int_ 0)
#guard (match ExecM.run Mem.empty (execStmt 64 aggCtx
          (.compound [.decl [.var "x" "int[4]" none none noSpan] noSpan] noSpan)) with
        | .ok (.ok _, m) => Mem.loadInt m (Ptr.toObject 0) IntTy.int_
        | _ => .error (.libc "x"))
  == .error (.memUB (.indetAutomatic 0 0))

/-! ### Zero-initialization is TYPE-DIRECTED, not a memset

§6.7.11p10 initializes an unmentioned member *as if by `= 0`*, and for a
POINTER that is a NULL POINTER. A model that wrote zero BYTES would leave
a member that reads back as the integer 0 and makes `loadPtr` refuse — a
wrong answer wearing the shape of a right one. -/

private def boxPartial : Except Refusal Ptr :=
  let st : Stmt := .compound
    [.decl [.var "b" "struct box" none (some (brace [iLit "5"] "struct box")) noSpan] noSpan]
    noSpan
  match ExecM.run Mem.empty (execStmt 64 aggCtx st) with
  | .ok (.ok _, m) => Mem.loadPtr m (Mem.member (Ptr.toObject 0) 8)
  | _ => .error (.libc "did not complete")

-- The mentioned member holds 5…
#guard declThenRead "struct box" (brace [iLit "5"] "struct box") 0
  == .ok (.int IntTy.int_ 5)
-- …and the unmentioned POINTER member reads back as a NULL POINTER.
#guard boxPartial == .ok Ptr.null
#guard (boxPartial.toOption.map Ptr.isNull) == some true

/-! ### §6.7.11p2 is a CONSTRAINT, so too many initializers REFUSE -/

#guard (match ExecM.verdict Mem.empty (execStmt 64 aggCtx
          (.compound [.decl [.var "x" "int[3]" none
            (some (brace [iLit "1", iLit "2", iLit "3", iLit "4"] "int[3]")) noSpan] noSpan]
            noSpan)) with
        | .unsupported w => w | _ => "did not refuse")
  == "more initializers than array elements"

/-! ## §6.5.3.3 — inch 5: the tier CALLS a function by name

Everything above ran a body with its frame prepared by hand. This runs
the call itself: parameters allocated, arguments stored, the body
executed, the return value handed back — which is what a scoreboard does
to a test program's `main`. -/

/-- The corpus's functions, with a layout that knows what an `int` is. -/
private def prog : Program :=
  { fns := sunfishC.unit.functionDefns, layout := intLayout }

/-- `pyfloordiv(a, b)`, called the way C calls it. -/
private def callPfd (a b : Int) : Outcome CVal :=
  ExecM.verdict Mem.empty
    (callByName 64 prog "pyfloordiv" [.int IntTy.int_ a, .int IntTy.int_ b])

private def called (a b : Int) : Option Int :=
  match callPfd a b with
  | .ok (.int _ n) => some n
  | _ => none

-- The call agrees with Python, through the whole calling sequence.
#guard called 7 2 == some 3
#guard called (-7) 2 == some (-4)
#guard called 7 (-2) == some (-4)
#guard called (-7) (-2) == some 3
#guard called (-1) 5 == some (-1)
#guard called 0 5 == some 0

-- …and it agrees with `Int.fdiv` on every pair, as the direct run did.
#guard [(7,2), (6,3), (-7,2), (7,-2), (-7,-2), (1,1), (0,5), (-1,5)].all
  (fun q => called q.1 q.2 == some (pythonFloorDiv q.1 q.2))

-- The UB inside the callee still reaches the caller as a refusal.
#guard callPfd 1 0 == .refused (.valueUB (.divideByZero "/"))

/-! ### The calling sequence's own refusals -/

-- §6.5.3.3p2 — the argument count must match the prototype.
#guard (match ExecM.verdict Mem.empty
          (callByName 64 prog "pyfloordiv" [.int IntTy.int_ 1]) with
        | .unsupported w => w | _ => "did not refuse") == "fewer arguments than parameters"
#guard (match ExecM.verdict Mem.empty (callByName 64 prog "pyfloordiv"
          [.int IntTy.int_ 1, .int IntTy.int_ 2, .int IntTy.int_ 3]) with
        | .unsupported w => w | _ => "did not refuse") == "more arguments than parameters"

-- A name with no definition in the program refuses, and names itself.
#guard (match ExecM.verdict Mem.empty (callByName 64 prog "no_such_fn" []) with
        | .unsupported w => w | _ => "did not refuse") == "no definition for 'no_such_fn'"

-- Fuel exhaustion is a TIMEOUT, not a refusal — even at a call.
#guard ExecM.verdict Mem.empty
  (callByName 0 prog "pyfloordiv" [.int IntTy.int_ 7, .int IntTy.int_ 2])
  == (.timeout : Outcome CVal)

/-! ### The 146 libc calls refuse with cause `libc`, not `unsupported`

Nearly half of all 320 call sites leave the tier. They must NOT pool with
the out-of-tier constructs: `libc` retires by widening the slice,
`unsupported` by climbing a rung. -/

/-- A synthetic caller whose body is `return abort();` — the corpus has no
one-line libc caller, and the point is the CAUSE, not the callee. -/
private def libcCaller : LeanModels.C.FunctionDefn :=
  { name := "calls_libc", ty := "int (void)", storage := none, params := [],
    body := some (.compound
      [.ret (some (.call (.declRef "abort" "FunctionDecl" "void (void)" noSpan)
                         [] "void" noSpan)) noSpan] noSpan),
    span := noSpan }

private def progL : Program := { prog with fns := libcCaller :: prog.fns }

#guard ExecM.verdict Mem.empty (callByName 64 progL "calls_libc" [])
  == .refused (.libc "abort")
#guard (Outcome.refused (α := CVal) (.libc "abort")).cause? == some (.environment () : Cause)
-- …and `libc` is NOT the cause an out-of-tier construct gets.
#guard (Outcome.refused (α := CVal) (.libc "abort")).cause?
    != (Outcome.unsupported (α := CVal) "x").cause?
-- `libc` carries no J.2 index, because an unmodelled library call is not UB.
#guard (Refusal.libc "abort").j2 == none

/-! ## §6.5.3.3p4 — a NESTED call, and why these gates exist

Until `evalArgs` moved into the expression layer's mutual block, **every**
call whose callee was a defined function refused. The handler was given
argument EXPRESSIONS and no evaluator to reduce them, so it answered
*"nested call to '…' — argument evaluation is inch 5's open problem"*.

That is why these gates are here rather than merely implied by the ones
above: `callByName` takes ALREADY-EVALUATED arguments, so every call gate
before this point enters the tier at the top and never exercises a call
in ARGUMENT position. The whole `J.1(16)` domain — 7 sites, every one an
effectful argument that is a nested call (`docs/c23-spec-mirror.md` §5.3)
— was unreachable, and an `∀ order` theorem over it would have quantified
over refusals. **A claim that cannot fail is not a check**
(`2026-08-23-c-5`), so the domain had to be made reachable before it could
be discharged. -/

/-- An `int` literal, as clang spells one. -/
private def intE (n : Int) : Expr := .intLit (toString n) "int" noSpan

/-- The callee, as a plain `DeclRefExpr` — `calleeNameOf` peels the
conversions clang would wrap it in, and the libc gate above uses the same
bare spelling. -/
private def pfdRef : Expr :=
  .declRef "pyfloordiv" "FunctionDecl" "int (int, int)" noSpan

private def retCall (args : List Expr) (name : String) : LeanModels.C.FunctionDefn :=
  { name := name, ty := "int (void)", storage := none, params := [],
    body := some (.compound
      [.ret (some (.call pfdRef args "int" noSpan)) noSpan] noSpan),
    span := noSpan }

/-- `int c1(void) { return pyfloordiv(7, 2); }` — a call in EXPRESSION
position, with its arguments evaluated by `evalArgs`. -/
private def caller1 : LeanModels.C.FunctionDefn := retCall [intE 7, intE 2] "c1"

/-- `int c2(void) { return pyfloordiv(pyfloordiv(7, 2), 2); }` — the
`J.1(16)` SHAPE itself: two arguments, one of them a call. -/
private def caller2 : LeanModels.C.FunctionDefn :=
  retCall [.call pfdRef [intE 7, intE 2] "int" noSpan, intE 2] "c2"

private def progN : Program := { prog with fns := caller1 :: caller2 :: prog.fns }

private def runN (name : String) : Option Int :=
  match ExecM.verdict Mem.empty (callByName 64 progN name []) with
  | .ok (.int _ n) => some n
  | _ => none

-- `pyfloordiv(7, 2) = 3`, reached through an argument list rather than
-- through `callByName`'s already-evaluated one.
#guard runN "c1" == some 3

-- …and the nested one: the inner call answers 3, the outer computes
-- `pyfloordiv(3, 2) = 1`. This is the gate that would have failed before
-- the repair, with `unsupported`, not with a wrong number.
#guard runN "c2" == some 1

-- Non-vacuity, stated as the lane's law wants it: the OLD refusal message
-- is gone, and these calls do not refuse at all.
#guard (match ExecM.verdict Mem.empty (callByName 64 progN "c2" []) with
        | .ok _ => "ran" | .refused _ => "refused"
        | .unsupported w => w | .timeout => "timeout") == "ran"

-- Fuel still bounds the nesting: each call level costs one, and exhaustion
-- is a TIMEOUT rather than a refusal, at a nested call as at a top-level one.
#guard ExecM.verdict Mem.empty (callByName 1 progN "c2" [])
  == (.timeout : Outcome CVal)

end Examples.c.sunfish.stmt
