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
#guard (Outcome.refused (α := Flow) (.valueUB (.divideByZero "/"))).cause? == some Cause.ub

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
  == some Cause.unsupported

end Examples.c.sunfish.stmt
