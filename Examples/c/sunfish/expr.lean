import Examples.c.sunfish.memory

/-!
# M2 inch 3, INSTANTIATED: the evaluator runs the corpus's own expressions

`LeanModels/C/C23/Expr.lean` states §6.5. This file RUNS it — not on
expressions written here, but on **terms pulled out of the ingested
translation unit**, so what is gated is the corpus rather than a
paraphrase of it.

The centrepiece is `pyfloordiv`'s condition (sunfish.c L162):

    if (r != 0 && ((r < 0) != (b < 0))) q--;

which the charter picked as the tier's first function for reasons that
pay off again here — it is one `&&` over four comparisons and two lvalue
conversions, so a single term exercises the load-bearing implicit
(§6.3.2.1p2), the comparison rules (§6.5.9, §6.5.10) and **the drain
amendment** (§6.5.14p4) at once.
-/

namespace Examples.c.sunfish.expr

open LeanModels.C.C23
open LeanModels.C (CType Expr)

/-- A synthetic span, for the terms this file builds by hand. The ones
taken from the corpus carry their real ones. -/
private def noSpan : LeanModels.C.CSpan := ⟨0, 0, 0, 0, none, none⟩

/-! ## The term under test, taken from the ingested corpus -/

/-- `pyfloordiv`'s `if` condition, as ingested. -/
private def pfdCond : Option Expr :=
  (sunfishC.unit.functionDefns.find? (·.name == "pyfloordiv")).bind fun f =>
    f.body.bind fun b => match b with
      | .compound (_ :: .ifS c _ _ _ :: _) _ => some c
      | _ => none

-- It is the `&&` the source writes, and it is really there.
#guard (pfdCond.map fun e => match e with
  | .binop op _ _ _ sp => (op, sp.line)
  | _ => ("?", 0)) == some ("&&", 162)

/-- The condition, or a term that refuses loudly if the corpus moved. -/
private def cond : Expr := pfdCond.getD (.unsupported "missing" "pfdCond" noSpan)

/-! ## The world the expression runs in

Two automatic `int` objects, `r` and `b`, exactly as `pyfloordiv`'s frame
would hold them. -/

private def mem0 : Mem := (((Mem.empty.alloc .automatic 4 (some "int")).1).alloc
  .automatic 4 (some "int")).1

/-- `r` is object 0, `b` is object 1 — the frame's own binding order. -/
private def env0 : Env := [("r", 0), ("b", 1)]

private def ctx0 : Ctx := { env := env0 }

/-- Put a value in an object. -/
private def setInt (m : Mem) (o : ObjId) (n : Int) : Mem :=
  (Mem.storeInt m (Ptr.toObject o) IntTy.int_ n).toOption.getD m

/-- Run the condition with `r` and `b` both determinate. -/
private def runBoth (r b : Int) : Except Refusal CVal × Mem :=
  EvalM.run (setInt (setInt mem0 0 r) 1 b) (evalExpr ctx0 cond)

/-! ## The condition computes what C says it computes

`r != 0 && ((r < 0) != (b < 0))` — true exactly when the remainder is
non-zero and its sign differs from the divisor's, which is the correction
`pyfloordiv` applies to turn C's truncating division into Python's
flooring one. -/

#guard (runBoth 0 5).1 == .ok (ofBool false)      -- r == 0: no correction
#guard (runBoth 1 5).1 == .ok (ofBool false)      -- signs agree (+, +)
#guard (runBoth (-1) (-5)).1 == .ok (ofBool false) -- signs agree (-, -)
#guard (runBoth (-1) 5).1 == .ok (ofBool true)    -- signs DIFFER: correct
#guard (runBoth 1 (-5)).1 == .ok (ofBool true)    -- signs DIFFER: correct

/-! ## §6.5.14p4 — THE DRAIN AMENDMENT, executed

**The right operand of `&&` is evaluated only if the left compares
unequal to 0**, and the way to *demonstrate* that — rather than assert it
— is to make evaluating the right operand IMPOSSIBLE and then observe
that the expression still succeeds.

So `b` is left where `alloc` put it: **indeterminate**. Reading it is
`J.2(11)`, §6.2.4 — undefined behaviour this model refuses.

* With `r = 0` the left operand is false, the right is never reached, and
  the whole expression **answers 0**. The memory it answers in is the
  LEFT's out-memory; the right's never existed.
* With `r = 1` the left operand is true, the right operand runs, reads
  the indeterminate `b`, and the expression **REFUSES**.

One term, one uninitialised object, opposite outcomes — and the
difference is exactly the short-circuit. -/

/-- Only `r` is written; `b` stays indeterminate. -/
private def runIndet (r : Int) : Except Refusal CVal × Mem :=
  EvalM.run (setInt mem0 0 r) (evalExpr ctx0 cond)

-- r = 0: the right operand is NOT evaluated, so the indeterminate `b` is
-- never read and the expression succeeds.
#guard (runIndet 0).1 == .ok (ofBool false)

-- r = 1: the right operand IS evaluated, reads `b`, and refuses — J.2(11).
#guard (runIndet 1).1 == .error (.memUB (.indetAutomatic 1 0))
#guard ((runIndet 1).1.toOption).isNone

-- The refusal names its Annex J entry, and its cause never retires.
#guard (Refusal.memUB (.indetAutomatic 1 0)).j2 == some "J.2(11)"
#guard (Refusal.memUB (.indetAutomatic 1 0)).cause == Cause.ub

-- ...and the SAME term with `b` written succeeds, so the refusal above is
-- about the short circuit and not about the term being unevaluable.
#guard (runBoth 1 5).1 == .ok (ofBool false)

/-! ### The memory is RETAINED across a refusal

The monad's layer order (`ExceptT` outside `StateT`) exists for this: a
refusal that discarded its memory could not say what had happened by the
time it fired. `r` is still readable in the out-memory of a refused run. -/

#guard (Mem.loadInt (runIndet 1).2 (Ptr.toObject 0) IntTy.int_)
  == .ok (.int IntTy.int_ 1)

/-! ## §6.5.6p6 — division by zero, from the same function

`pyfloordiv`'s first statement is `int q = a / b, r = a % b;`, and the
charter chose it partly because two of the eleven armed UB classes live
in three statements. Here is the division one, evaluated. -/

private def divExpr (l r : Expr) : Expr := .binop "/" l r "int" noSpan
private def modExpr (l r : Expr) : Expr := .binop "%" l r "int" noSpan

/-- `r` read as an int — the lvalue conversion clang inserts. -/
private def readInt (name : String) : Expr :=
  .implicitCast "LValueToRValue" (.declRef name "VarDecl" "int" noSpan) "int" noSpan

private def lit (n : String) : Expr := .intLit n "int" noSpan

private def runE (r b : Int) (e : Expr) : Except Refusal CVal :=
  (EvalM.run (setInt (setInt mem0 0 r) 1 b) (evalExpr ctx0 e)).1

-- C truncates toward zero, and Lean's `/` on `Int` would floor to -4.
#guard runE (-7) 2 (divExpr (readInt "r") (readInt "b")) == .ok (.int IntTy.int_ (-3))
#guard runE (-7) 2 (modExpr (readInt "r") (readInt "b")) == .ok (.int IntTy.int_ (-1))

-- §6.5.6p6 — a zero divisor is undefined: J.2(41).
#guard runE 1 0 (divExpr (readInt "r") (readInt "b"))
  == .error (.valueUB (.divideByZero "/"))
#guard (Refusal.valueUB (.divideByZero "/")).j2 == some "J.2(41)"

-- §6.5.1p5 — `INT_MIN / -1` is not representable: J.2(35).
#guard runE (-2147483648) (-1) (divExpr (readInt "r") (readInt "b"))
  == .error (.valueUB .divideOverflow)

-- §6.5.1p5 — signed overflow in `+`, refused rather than wrapped.
#guard runE 2147483647 1 (.binop "+" (readInt "r") (readInt "b") "int" noSpan)
  == .error (.valueUB (.signedOverflow "+" IntTy.int_ 2147483648))

/-! ## §6.3.2.1p3 + §6.5.3.2 — decay and subscript, the common path

**405 decay sites and 328 subscripts**, which is why they are gated
before `&` and `*`. The object is the `Pos` board from inch 2's fixture,
and the layout is the same measured one. -/

/-- The layout inch 2 measured with `_Static_assert` on both profile
hosts, which agree. `Pos` is 144 bytes with `score` at 120. -/
private def posLayout : Layout where
  size := fun t => match t with
    | "char" => some 1
    | "int" => some 4
    | "uint64_t" => some 8
    | "Pos" => some 144
    | "char[120]" => some 120
    | _ => none
  fieldOff := fun base f => match base, f with
    | "Pos", "b" | "const Pos *", "b" | "Pos *", "b" => some 0
    | "Pos", "score" | "const Pos *", "score" | "Pos *", "score" => some 120
    | "Pos", "ep" | "const Pos *", "ep" | "Pos *", "ep" => some 128
    | "Pos", "kp" | "const Pos *", "kp" | "Pos *", "kp" => some 132
    | "Pos", "h" | "const Pos *", "h" | "Pos *", "h" => some 136
    | _, _ => none

/-- One `Pos` object, its 120 board bytes written and the rest left
indeterminate — inch 2's `memcpy(p.b, board, 120)` scenario exactly. -/
private def posMem : Mem :=
  let (m, o) := Mem.empty.alloc .automatic 144 (some "Pos")
  (Mem.storeBytes m (Ptr.toObject o) (List.replicate 120 (CByte.conc 46))).toOption.getD m

private def posCtx : Ctx := { env := [("p", 0)], layout := posLayout }

/-- `p.b[3]` — a dot member, then a DECAY of the array, then a subscript,
then the lvalue conversion. Four of the five rules in one term. -/
private def boardAt (i : String) : Expr :=
  .implicitCast "LValueToRValue"
    (.index
      (.implicitCast "ArrayToPointerDecay"
        (.member (.declRef "p" "VarDecl" "Pos" noSpan) "b" false "char[120]" noSpan)
        "char *" noSpan)
      (lit i) "char" noSpan)
    "char" noSpan

#guard (EvalM.run posMem (evalExpr posCtx (boardAt "0"))).1 == .ok (.int IntTy.char_ 46)
#guard (EvalM.run posMem (evalExpr posCtx (boardAt "119"))).1 == .ok (.int IntTy.char_ 46)

-- One past the board is still INSIDE the object (it is `score`'s first
-- byte), and that byte is indeterminate — so this refuses for the right
-- reason: J.2(11), not an out-of-bounds.
#guard (EvalM.run posMem (evalExpr posCtx (boardAt "120"))).1
  == .error (.memUB (.indetAutomatic 0 120))

-- ...and past the OBJECT it is the structural refusal instead: J.2(46).
#guard (EvalM.run posMem (evalExpr posCtx (boardAt "144"))).1
  == .error (.memUB (.outOfBounds 0 144 1 144))

/-! ## §6.5.3.4 — `p->f`, the 226-site path

`p->f` is DEFINED as `(*p).f` (§6.5.3.4p4), so the model has one rule
with two spellings. Here the base is a genuine `Pos *`. -/

private def ptrMem : Mem :=
  let m := posMem
  let (m2, po) := m.alloc .automatic 8 (some "Pos *")
  (Mem.storePtr m2 (Ptr.toObject po) (Ptr.toObject 0)).toOption.getD m2

private def ptrCtx : Ctx := { env := [("pp", 1)], layout := posLayout }

/-- `pp->score`, with `pp` a `Pos *` pointing at the board object. -/
private def arrowScore : Expr :=
  .implicitCast "LValueToRValue"
    (.member (.implicitCast "LValueToRValue"
               (.declRef "pp" "VarDecl" "Pos *" noSpan) "Pos *" noSpan)
             "score" true "int" noSpan)
    "int" noSpan

-- `score` was never written, so the arrow path reaches an indeterminate
-- read — which is the RIGHT answer, and proves the offset arithmetic ran.
#guard (EvalM.run ptrMem (evalExpr ptrCtx arrowScore)).1
  == .error (.memUB (.indetAutomatic 0 120))

-- Write it, and the same term reads it back through the pointer.
#guard (EvalM.run
  ((Mem.storeInt ptrMem (Mem.member (Ptr.toObject 0) 120) IntTy.int_ 42).toOption.getD ptrMem)
  (evalExpr ptrCtx arrowScore)).1 == .ok (.int IntTy.int_ 42)

/-! ## §6.5.17.2 / §6.5.3.5 — assignment and the all-postfix increment

Measured: **every one of the corpus's 63 increment sites is postfix.**
Postfix yields the value BEFORE the update, which is the difference a
model gets wrong by being tidy. -/

private def incr (name : String) : Expr :=
  .unop "++" (.declRef name "VarDecl" "int" noSpan) true "int" noSpan

private def decr (name : String) : Expr :=
  .unop "--" (.declRef name "VarDecl" "int" noSpan) true "int" noSpan

-- `r++` ANSWERS 5 and LEAVES 6.
#guard (let (a, m) := EvalM.run (setInt mem0 0 5) (evalExpr ctx0 (incr "r"))
        (a, Mem.loadInt m (Ptr.toObject 0) IntTy.int_))
  == (.ok (.int IntTy.int_ 5), .ok (.int IntTy.int_ 6))

-- `q--` — `pyfloordiv`'s own correction, and at `INT_MIN` it OVERFLOWS.
#guard (EvalM.run (setInt mem0 0 (-2147483648)) (evalExpr ctx0 (decr "r"))).1
  == .error (.valueUB (.signedOverflow "-" IntTy.int_ (-2147483649)))

-- §6.5.17.2 — assignment answers the value it stored, and stores it.
#guard (let e : Expr := .binop "=" (.declRef "r" "VarDecl" "int" noSpan)
                         (lit "7") "int" noSpan
        let (a, m) := EvalM.run mem0 (evalExpr ctx0 e)
        (a, Mem.loadInt m (Ptr.toObject 0) IntTy.int_))
  == (.ok (.int IntTy.int_ 7), .ok (.int IntTy.int_ 7))

/-! ## The type-spelling trap the census found

19 binary-operator sites in the corpus have operands whose type SPELLINGS
differ while the types do not (`uint64_t` vs `unsigned long long`). A
model that compared spellings would see a conversion that is not there,
so the evaluator RESOLVES instead. -/

#guard intTyOf? "uint64_t" == intTyOf? "unsigned long long"
#guard intTyOf? "uint32_t" == intTyOf? "unsigned int"
#guard intTyOf? "const int" == intTyOf? "int"
#guard intTyOf? "int" == some IntTy.int_
-- ...and a spelling outside the measured table is a REFUSAL, not a guess.
#guard intTyOf? "struct Pos" == none
#guard intTyOf? "double" == none

/-! ## The three refusal causes stay unpooled through the evaluator -/

#guard (EvalM.run mem0 (evalExpr ctx0 (.floatLit "1.0" "double" noSpan))).1.toOption == none
#guard (EvalM.run mem0 (evalExpr ctx0 (.strLit "hi" "char[3]" noSpan))).1.toOption == none

-- A call refuses as `unsupported` — the cause that retires by climbing a
-- rung — and names the callee so a human can act on it.
#guard (EvalM.run mem0 (evalExpr ctx0
  (.call (.declRef "abort" "FunctionDecl" "void (void)" noSpan) [] "void" noSpan))).1
  == .error (.unsupported "call to 'abort' — the call semantics is inch 5")

end Examples.c.sunfish.expr
