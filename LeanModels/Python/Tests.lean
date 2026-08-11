import LeanModels.Python.Semantics
import LeanModels.Python.Json
import LeanModels.Python.Logic

/-!
# Interpreter smoke tests (`LeanModels.Python.Tests`)

`#guard` tests for every row of DESIGN.md's "Semantic decisions" table
(AST literals, checked against CPython 3.9 behavior), plus end-to-end
`#eval`-time checks that read the extractor-generated envelopes in
`Examples/python/<name>/<name>.json`, parse them with `Json.lean`, and run
`callFunction` on the result (loud `IO.userError` on any mismatch, so
`lake build` fails if anything regresses).
-/

namespace LeanModels.Python.Tests

/-! ## Builders and fixtures -/

private def sp : Span := default

private def iL (n : Int) : Expr := .constant (.int n) sp
private def bL (b : Bool) : Expr := .constant (.bool b) sp
private def sL (s : String) : Expr := .constant (.str s) sp
private def noneL : Expr := .constant .none sp
private def nm (id : String) : Expr := .name id sp
private def bo (l : Expr) (op : BinOp) (r : Expr) : Expr := .binOp l op r sp
private def cmp1 (l : Expr) (op : CmpOp) (r : Expr) : Expr := .compare l #[op] #[r] sp
/-- `1 // 0`: an expression that raises `ZeroDivisionError` when evaluated. -/
private def boom : Expr := bo (iL 1) .floorDiv (iL 0)

/-- Empty module: expression-level tests. -/
private def M0 : Module := { functions := #[], topLevel := #[] }

private def fnIdent : FunctionDefn :=
  { name := "ident", params := #[⟨"x", sp, Option.none⟩], argsOk := true,
    body := #[.ret (some (nm "x")) sp], span := sp }
private def fnLoopForever : FunctionDefn :=
  { name := "loopForever", params := #[], argsOk := true,
    body := #[.whileLoop (bL true) #[.pass sp] #[] sp], span := sp }
private def fnBadArgs : FunctionDefn :=
  { name := "badArgs", params := #[], argsOk := false, body := #[], span := sp }
private def fnFallOff : FunctionDefn :=
  { name := "fallOff", params := #[], argsOk := true, body := #[.pass sp], span := sp }
private def fnBareRet : FunctionDefn :=
  { name := "bareRet", params := #[], argsOk := true,
    body := #[.ret Option.none sp], span := sp }
/-- `def cd(n): if n <= 0: return 0 \n return cd(n - 1)` — recursion depth n. -/
private def fnCountdown : FunctionDefn :=
  { name := "cd", params := #[⟨"n", sp, Option.none⟩], argsOk := true,
    body := #[.ifStmt (cmp1 (nm "n") .ltE (iL 0)) #[.ret (some (iL 0)) sp] #[] sp,
              .ret (some (.call (nm "cd") #[bo (nm "n") .sub (iL 1)] #[] Option.none sp)) sp],
    span := sp }
/-- `def opt(x, d=10, h=None): if h is None: h = 0 \n return x + d + h` —
F1 (int and None literal defaults) + F2 (`is None`) in one body. -/
private def fnOpt : FunctionDefn :=
  { name := "opt",
    params := #[⟨"x", sp, Option.none⟩, ⟨"d", sp, some (.int 10)⟩,
                ⟨"h", sp, some .none⟩],
    argsOk := true,
    body := #[.ifStmt (cmp1 (nm "h") .is noneL)
                #[.assign #[nm "h"] (iL 0) sp] #[] sp,
              .ret (some (bo (bo (nm "x") .add (nm "d")) .add (nm "h"))) sp],
    span := sp }

private def M1 : Module :=
  { functions := #[fnIdent, fnLoopForever, fnBadArgs, fnFallOff, fnBareRet,
                   fnCountdown, fnOpt],
    topLevel := #[] }

/-- `def sorted(xs): return 99` — a module-level definition that must SHADOW
the builtin (`findFunction` is consulted before the builtin branch, exactly
as CPython's module globals shadow builtins). -/
private def fnSortedShadow : FunctionDefn :=
  { name := "sorted", params := #[⟨"xs", sp, Option.none⟩], argsOk := true,
    body := #[.ret (some (iL 99)) sp], span := sp }

private def M2 : Module := { functions := #[fnSortedShadow], topLevel := #[] }

private def w0 : World := ⟨#[], [], [], []⟩

/-- Forget the (stage-1, always-`w0`) state of an expression run — the
projection that keeps the value-level guards below verbatim. -/
private def proj : Run FrameState RVal → Res RVal
  | .ok _ v => .ok v
  | .exn _ er => .exn er
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

private def evIn (m : Module) (fuel : Nat) (env : Env) (e : Expr) : Res RVal :=
  proj (evalExpr m fuel ⟨w0, env⟩ e)

private def ev (e : Expr) (env : Env := []) (fuel : Nat := 100) : Res RVal :=
  evIn M0 fuel env e

/-- Value-level projection through the heap (H2): freeze the resulting
runtime value against the run's final heap, so list-producing expression
guards stay value-readable (`Val.list` snapshots). -/
private def evF (e : Expr) (env : Env := []) (fuel : Nat := 100) : Res Val :=
  match evalExpr M0 fuel ⟨w0, env⟩ e with
  | .ok st v => RVal.freezeH st.world.heap fuel [] v
  | .exn _ er => .exn er
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

private def run (ss : List Stmt) (env : Env := []) (fuel : Nat := 1000) :
    Res (Env × RFlow) :=
  match execStmts M0 fuel ⟨w0, env⟩ ss with
  | .ok st f => .ok (st.locals, f)
  | .exn _ er => .exn er
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

private def isTypeError : Res α → Bool
  | .exn (.typeError _) => true | _ => false
private def isValueError : Res α → Bool
  | .exn (.valueError _) => true | _ => false
private def isUnsupported : Res α → Bool
  | .unsupported _ => true | _ => false

/-! ## `//` and `%`: Python flooring (`Int.fdiv` / `Int.fmod`), CPython-checked:
`7 // 2 = 3`, `-7 // 2 = -4`, `7 // -2 = -4`, `-7 // -2 = 3`;
`7 % 2 = 1`, `-7 % 2 = 1`, `7 % -2 = -1`, `-7 % -2 = -1` -/

#guard evalBinOp .floorDiv (.int 7) (.int 2) == .ok (.int 3)
#guard evalBinOp .floorDiv (.int (-7)) (.int 2) == .ok (.int (-4))
#guard evalBinOp .floorDiv (.int 7) (.int (-2)) == .ok (.int (-4))
#guard evalBinOp .floorDiv (.int (-7)) (.int (-2)) == .ok (.int 3)
#guard evalBinOp .mod (.int 7) (.int 2) == .ok (.int 1)
#guard evalBinOp .mod (.int (-7)) (.int 2) == .ok (.int 1)
#guard evalBinOp .mod (.int 7) (.int (-2)) == .ok (.int (-1))
#guard evalBinOp .mod (.int (-7)) (.int (-2)) == .ok (.int (-1))
-- Same through the interpreter, negatives spelled as CPython does (USub):
#guard ev (bo (.unaryOp .usub (iL 7) sp) .floorDiv (iL 2)) == .ok (.int (-4))
#guard ev (bo (iL 7) .mod (.unaryOp .usub (iL 2) sp)) == .ok (.int (-1))
-- Divisor 0:
#guard ev (bo (iL 1) .floorDiv (iL 0)) == .exn .zeroDivisionError
#guard ev (bo (iL 1) .mod (iL 0)) == .exn .zeroDivisionError

/-! ## `**`, arithmetic, bool→int coercion -/

#guard ev (bo (iL 2) .pow (iL 10)) == .ok (.int 1024)
#guard ev (bo (iL 0) .pow (iL 0)) == .ok (.int 1)
#guard ev (bo (.unaryOp .usub (iL 2) sp) .pow (iL 3)) == .ok (.int (-8))
#guard isUnsupported (ev (bo (iL 2) .pow (.unaryOp .usub (iL 1) sp)))
#guard ev (bo (iL 0) .pow (iL (-1))) == .exn .zeroDivisionError  -- CPython: raises, no float involved
-- bool is an int subtype: True + 1 = 2, True * 3 = 3, -True = -1; results are int.
#guard ev (bo (bL true) .add (iL 1)) == .ok (.int 2)
#guard ev (bo (bL true) .mult (iL 3)) == .ok (.int 3)
#guard ev (bo (bL true) .add (bL false)) == .ok (.int 1)
#guard ev (.unaryOp .usub (bL true) sp) == .ok (.int (-1))
-- True division is a float: the extractor ships `BinOp:Div` as Unsupported.
#guard isUnsupported (ev (.unsupported "BinOp:Div" "a / b" sp))

/-! ## `+` type rules -/

#guard ev (bo (sL "ab") .add (sL "cd")) == .ok (.str "abcd")
-- H2: `+` on heap lists (allocating concat) is deliberately deferred — it
-- would evict every BinOp from the heap-free fragment; loud, never wrong.
#guard isUnsupported (ev (bo (.list #[iL 1] sp) .add (.list #[iL 2] sp)))
#guard ev (bo (.tuple #[iL 1] sp) .add (.tuple #[iL 2] sp)) == .ok (.tuple #[.int 1, .int 2])
#guard isTypeError (ev (bo (sL "a") .add (iL 1)))
#guard isUnsupported (ev (bo (.list #[iL 1] sp) .add (.tuple #[iL 2] sp))) -- H2: with `+`-concat
#guard isTypeError (ev (bo noneL .add (iL 1)))
#guard isTypeError (ev (bo (sL "a") .sub (sL "a")))
-- Python-valid but out of tier: sequence repetition, `%` formatting.
#guard isUnsupported (ev (bo (sL "ab") .mult (iL 3)))
#guard isUnsupported (ev (bo (iL 3) .mult (.list #[iL 1] sp)))
#guard isUnsupported (ev (bo (sL "%d") .mod (iL 3)))

/-! ## `==` / `!=` never raise; bool→int; structural; cross-type is False -/

#guard ev (cmp1 (bL true) .eq (iL 1)) == .ok (.bool true)
#guard ev (cmp1 (iL 1) .eq (sL "1")) == .ok (.bool false)
#guard ev (cmp1 noneL .eq noneL) == .ok (.bool true)
#guard ev (cmp1 (iL 1) .eq noneL) == .ok (.bool false)
#guard ev (cmp1 (iL 1) .notEq (sL "1")) == .ok (.bool true)
#guard ev (cmp1 (.list #[bL true] sp) .eq (.list #[iL 1] sp)) == .ok (.bool true)
#guard ev (cmp1 (.list #[iL 1] sp) .eq (.tuple #[iL 1] sp)) == .ok (.bool false)
#guard valEq (.listV #[.int 1, .listV #[.int 2, .bool true]])
             (.listV #[.int 1, .listV #[.int 2, .int 1]]) == .ok true
#guard valEq (.listV #[.int 1]) (.listV #[.int 1, .int 2]) == .ok false
#guard valEq (.str "1") (.int 1) == .ok false
-- since H1: '==' on a heap ref is loudly outside the stage-1 tier
#guard match valEq (.ref 0) (.int 1) with | .unsupported _ => true | _ => false

/-! ## Ordering comparisons -/

#guard ev (cmp1 (bL true) .lt (iL 2)) == .ok (.bool true)   -- True < 2
#guard ev (cmp1 (bL true) .gt (bL true)) == .ok (.bool false)
#guard ev (cmp1 (iL (-3)) .ltE (iL (-3))) == .ok (.bool true)
#guard ev (cmp1 (sL "ab") .lt (sL "b")) == .ok (.bool true)
#guard ev (cmp1 (sL "ab") .ltE (sL "ab")) == .ok (.bool true)
#guard ev (cmp1 (sL "b") .lt (sL "ab")) == .ok (.bool false)
#guard ev (cmp1 (sL "b") .gtE (sL "ab")) == .ok (.bool true)
#guard isUnsupported (ev (cmp1 (sL "a") .lt (iL 1)))
#guard isUnsupported (ev (cmp1 (.list #[] sp) .lt (.list #[] sp)))

/-! ## `is` / `is not` (F2): value-determined ONLY against `None`
CPython-checked: `None is None` → True; `0 is None` / `False is None` /
`"" is None` / `[] is None` → False (falsiness ≠ None-ness); identity
between non-None values is implementation-defined → loud. -/

#guard ev (cmp1 noneL .is noneL) == .ok (.bool true)
#guard ev (cmp1 (iL 0) .is noneL) == .ok (.bool false)
#guard ev (cmp1 noneL .is (iL 0)) == .ok (.bool false)     -- None on the left
#guard ev (cmp1 (bL false) .is noneL) == .ok (.bool false)
#guard ev (cmp1 (sL "") .is noneL) == .ok (.bool false)
#guard ev (cmp1 (.list #[] sp) .is noneL) == .ok (.bool false)
#guard ev (cmp1 (iL 0) .isNot noneL) == .ok (.bool true)
#guard ev (cmp1 noneL .isNot noneL) == .ok (.bool false)
#guard ev (cmp1 noneL .isNot (iL 3)) == .ok (.bool true)
#guard isUnsupported (ev (cmp1 (iL 1) .is (iL 1)))          -- small-int identity
#guard isUnsupported (ev (cmp1 (sL "a") .isNot (sL "a")))   -- str interning
-- Left operand evaluation order still applies (errors before the identity):
#guard ev (cmp1 boom .is noneL) == .exn .zeroDivisionError

/-! ## Chained comparison: once each, left to right, short-circuit -/

-- 1 < 5 > 0 < 99 → True (CPython-checked)
#guard ev (.compare (iL 1) #[.lt, .gt, .lt] #[iL 5, iL 0, iL 99] sp) == .ok (.bool true)
-- 3 < 2 < (1//0) → False: short-circuits, the raising comparator is never evaluated
#guard ev (.compare (iL 3) #[.lt, .lt] #[iL 2, boom] sp) == .ok (.bool false)
-- 1 < 2 < (1//0) → the third operand IS evaluated → ZeroDivisionError
#guard ev (.compare (iL 1) #[.lt, .lt] #[iL 2, boom] sp) == .exn .zeroDivisionError

/-! ## `and`/`or`: short-circuit, return the operand value -/

#guard ev (.boolOp .or #[iL 0, sL "x"] sp) == .ok (.str "x")
#guard ev (.boolOp .and #[iL 0, sL "x"] sp) == .ok (.int 0)
#guard ev (.boolOp .and #[iL 1, sL "x"] sp) == .ok (.str "x")
#guard ev (.boolOp .or #[sL "", iL 0] sp) == .ok (.int 0)     -- last value even if falsy
#guard evF (.boolOp .or #[iL 0, sL "", .list #[] sp] sp) == .ok (.list #[])
#guard ev (.boolOp .or #[iL 2, boom] sp) == .ok (.int 2)      -- short-circuit skips 1//0
#guard ev (.boolOp .and #[iL 0, boom] sp) == .ok (.int 0)
#guard ev (.boolOp .and #[iL 1, boom] sp) == .exn .zeroDivisionError

/-! ## Truthiness and `not` -/

#guard ev (.unaryOp .not (iL 0) sp) == .ok (.bool true)
#guard ev (.unaryOp .not (sL "a") sp) == .ok (.bool false)
#guard ev (.unaryOp .not noneL sp) == .ok (.bool true)
#guard ev (.unaryOp .not (.tuple #[iL 0] sp) sp) == .ok (.bool false)
#guard isTypeError (ev (.unaryOp .usub (sL "a") sp))
#guard truthy (.listV #[]) == .ok false
#guard truthy (.str " ") == .ok true
#guard truthy (.int (-1)) == .ok true
-- since H1: a heap ref's truthiness lives in the heap — loud
#guard match truthy (.ref 0) with | .unsupported _ => true | _ => false

/-! ## Name resolution: local env → function table → `len` → NameError -/

#guard ev (nm "zzz") == .exn (.nameError "zzz")
#guard ev (nm "x") (env := [("x", .int 5)]) == .ok (.int 5)
#guard Env.lookup ([("x", .int 1), ("x", .int 2)] : Env) "x" == some (.int 1)  -- first match wins
#guard isUnsupported (evIn M1 100 [] (nm "ident"))       -- function as a value
#guard isUnsupported (ev (nm "len"))                          -- builtin as a value
-- Local binding shadows the function table (shadowed value is not callable):
#guard evIn M1 100 [("ident", .int 3)] (nm "ident") == .ok (.int 3)
#guard isTypeError (evIn M1 100 [("ident", .int 3)] (.call (nm "ident") #[] #[] Option.none sp))

/-! ## `Env.set`: replace in place, else append -/

#guard Env.set ([] : Env) "x" (.int 1) == [("x", .int 1)]
#guard Env.set ([("x", .int 1), ("y", .int 2)] : Env) "x" (.int 3) == [("x", .int 3), ("y", .int 2)]
#guard Env.set ([("x", .int 1)] : Env) "y" (.int 2) == [("x", .int 1), ("y", .int 2)]

/-! ## Indexing: negative Python-style, bool index coerces, errors -/

private def L123 : Expr := .list #[iL 10, iL 20, iL 30] sp

#guard ev (.subscript L123 (iL 0) sp) == .ok (.int 10)
#guard ev (.subscript L123 (iL (-1)) sp) == .ok (.int 30)
#guard ev (.subscript L123 (iL (-3)) sp) == .ok (.int 10)
#guard ev (.subscript L123 (iL 3) sp) == .exn .indexError
#guard ev (.subscript L123 (iL (-4)) sp) == .exn .indexError
#guard ev (.subscript (.tuple #[iL 1, iL 2] sp) (iL 1) sp) == .ok (.int 2)
#guard ev (.subscript (sL "hello") (iL (-1)) sp) == .ok (.str "o")
#guard ev (.subscript (sL "hello") (iL 0) sp) == .ok (.str "h")
#guard ev (.subscript (sL "ab") (bL true) sp) == .ok (.str "b")   -- "ab"[True] == "b"
#guard isTypeError (ev (.subscript L123 (sL "a") sp))
#guard isTypeError (ev (.subscript (iL 5) (iL 0) sp))
#guard ev (.subscript (sL "hé") (iL 1) sp) == .ok (.str "é")      -- code points, not bytes

/-! ## `len` -/

#guard ev (.call (nm "len") #[sL "abc"] #[] Option.none sp) == .ok (.int 3)
#guard ev (.call (nm "len") #[.list #[] sp] #[] Option.none sp) == .ok (.int 0)
#guard ev (.call (nm "len") #[.tuple #[iL 1, iL 2] sp] #[] Option.none sp) == .ok (.int 2)
#guard ev (.call (nm "len") #[sL "hé"] #[] Option.none sp) == .ok (.int 2)
#guard isTypeError (ev (.call (nm "len") #[iL 5] #[] Option.none sp))
#guard isTypeError (ev (.call (nm "len") #[sL "a", sL "b"] #[] Option.none sp))

/-! ## `sorted` (v0: NEW ascending list from an all-int list argument;
CPython-3.9.25-checked ground truth — the same probe table is pinned as
`#py_check` rows in `Examples/python/bench_statistics/spec.lean`). A new
list is returned by construction (pure value semantics), so the CPython
`sorted(xs) is not xs` probe has no v0 counterpart to test. -/

private def sortedC (args : Array Expr) : Expr := .call (nm "sorted") args #[] Option.none sp

#guard evF (sortedC #[.list #[iL 5, iL 1, iL 3] sp]) == .ok (.list #[.int 1, .int 3, .int 5])
#guard evF (sortedC #[.list #[iL 1, iL 3, iL 5] sp]) == .ok (.list #[.int 1, .int 3, .int 5])
#guard evF (sortedC #[.list #[iL 7, iL 1, iL 5, iL 3] sp])
    == .ok (.list #[.int 1, .int 3, .int 5, .int 7])
#guard evF (sortedC #[.list #[iL 2, iL 2, iL 1, iL 3] sp])
    == .ok (.list #[.int 1, .int 2, .int 2, .int 3])                       -- duplicates stay
#guard evF (sortedC #[.list #[iL (-5), iL 3, iL (-1), iL 0] sp])
    == .ok (.list #[.int (-5), .int (-1), .int 0, .int 3])                 -- negatives
#guard evF (sortedC #[.list #[iL 42] sp]) == .ok (.list #[.int 42])        -- singleton
#guard evF (sortedC #[.list #[] sp]) == .ok (.list #[])                    -- empty
#guard evF (sortedC #[.list #[iL 0, iL 0, iL 0, iL 0] sp])
    == .ok (.list #[.int 0, .int 0, .int 0, .int 0])                       -- all equal
-- H2: `sorted` returns a FRESH heap list — the CPython `sorted(xs) is not
-- xs` probe is finally expressible (distinct addresses):
#guard (match evalExpr M0 100 ⟨w0, []⟩ (sortedC #[.list #[iL 2, iL 1] sp]) with
        | .ok st (.ref r) => r != 0 && st.world.heap.size == 2
        | _ => false)
-- Arity (CPython 3.9: "sorted expected 1 argument, got 0/2") and not-iterable:
#guard ev (sortedC #[]) == .exn (.typeError "sorted expected 1 argument, got 0")
#guard ev (sortedC #[.list #[iL 1] sp, .list #[iL 2] sp])
    == .exn (.typeError "sorted expected 1 argument, got 2")
#guard ev (sortedC #[iL 5]) == .exn (.typeError "'int' object is not iterable")
#guard ev (sortedC #[bL true]) == .exn (.typeError "'bool' object is not iterable")
#guard ev (sortedC #[noneL]) == .exn (.typeError "'NoneType' object is not iterable")
-- H6 general-order tier: all four sort exactly as CPython (bool IDENTITY
-- preserved — `sorted([True, 0, 2])` keeps the `True` object):
#guard ev (sortedC #[sL "cba"]) == .ok (.listV #[.str "a", .str "b", .str "c"])
#guard ev (sortedC #[.tuple #[iL 3, iL 1] sp]) == .ok (.listV #[.int 1, .int 3])
#guard evF (sortedC #[.list #[bL true, iL 0, iL 2] sp])
    == .ok (.list #[.int 0, .bool true, .int 2])
#guard evF (sortedC #[.list #[sL "b", sL "a"] sp])
    == .ok (.list #[.str "a", .str "b"])
-- Mixed int/str raises in CPython too, but the class match is a guess v0
-- does not make — refuse loudly instead:
#guard isUnsupported (ev (sortedC #[.list #[iL 1, sL "a"] sp]))
-- Builtin as a value, and `key=`/`reverse=` (keyword-only ⇒ the extractor
-- ships `call_unsupported: "keywords"`, refused before argument evaluation):
#guard isUnsupported (ev (nm "sorted"))
#guard isUnsupported (ev (.call (nm "sorted") #[.list #[] sp] #[] (some "keywords") sp))
-- Argument errors propagate before the sort happens (evaluation order):
#guard ev (sortedC #[boom]) == .exn .zeroDivisionError
-- A module-level `def sorted` SHADOWS the builtin (findFunction first):
#guard evIn M2 100 [] (sortedC #[.list #[iL 3, iL 1] sp]) == .ok (.int 99)
-- ... and a local binding shadows both (args still evaluated, then TypeError):
#guard isTypeError (evIn M2 100 [("sorted", .int 3)] (sortedC #[.list #[] sp]))
-- The pure helpers themselves:
#guard sortInts [5, 1, 3] == [1, 3, 5]
#guard sortInts [] == []
#guard insertLe 2 [1, 3] == [1, 2, 3]
#guard asIntList [.int 1, .int 2] == some [1, 2]
#guard asIntList [.int 1, .bool true] == Option.none
#guard sortedVal (.listV #[.int 9, .int (-9)]) == .ok (.listV #[.int (-9), .int 9])

/-! ## Left-to-right, once-only evaluation (observable via error order) -/

#guard ev (bo boom .add (nm "zzz")) == .exn .zeroDivisionError    -- left first
#guard ev (bo (nm "zzz") .add boom) == .exn (.nameError "zzz")
-- Callee name resolves before arguments are evaluated (CPython order):
#guard ev (.call (nm "zzz") #[boom] #[] Option.none sp) == .exn (.nameError "zzz")
-- Arguments are evaluated before the call happens:
#guard evIn M1 100 [] (.call (nm "ident") #[boom] #[] Option.none sp) == .exn .zeroDivisionError
-- List/tuple literals evaluate elements left to right:
#guard evF (.list #[iL 1, bo (iL 1) .add (iL 1)] sp) == .ok (.list #[.int 1, .int 2])
#guard ev (.tuple #[boom, nm "zzz"] sp) == .exn .zeroDivisionError

/-! ## Calls: keywords/starargs flag, non-name callee, arity, argsOk -/

#guard isUnsupported (evIn M1 100 [] (.call (nm "ident") #[iL 1] #[] (some "keywords") sp))
#guard isUnsupported (ev (.call (iL 5) #[] #[] Option.none sp))
#guard callFunction M1 "ident" #[.int 7] 100 == .ok (.int 7)
#guard isTypeError (callFunction M1 "ident" #[] 100)               -- arity mismatch
#guard isTypeError (callFunction M1 "ident" #[.int 1, .int 2] 100)
#guard isUnsupported (callFunction M1 "badArgs" #[] 100)           -- argsOk = false
#guard callFunction M1 "nosuch" #[] 100 == .exn (.nameError "nosuch")
#guard callFunction M1 "fallOff" #[] 100 == .ok .none              -- fall off the end
#guard callFunction M1 "bareRet" #[] 100 == .ok .none              -- bare `return`
#guard callFunction M1 "cd" #[.int 5] 200 == .ok (.int 0)          -- recursion
#guard callFunction M1 "cd" #[.int 1000] 100 == .timeout           -- fuel bounds depth

/-! ## Literal parameter defaults (F1): fill window, both defaults, arity -/

#guard callFunction M1 "opt" #[.int 1] 100 == .ok (.int 11)         -- d=10, h=None→0
#guard callFunction M1 "opt" #[.int 1, .int 2] 100 == .ok (.int 3)  -- h=None→0
#guard callFunction M1 "opt" #[.int 1, .int 2, .int 4] 100 == .ok (.int 7)
#guard isTypeError (callFunction M1 "opt" #[] 100)                  -- x has no default
#guard isTypeError (callFunction M1 "opt" #[.int 1, .int 2, .int 3, .int 4] 100)
-- The env-shape helpers themselves:
#guard arityOk #[⟨"x", sp, Option.none⟩, ⟨"d", sp, some (.int 10)⟩] 1 == true
#guard arityOk #[⟨"x", sp, Option.none⟩, ⟨"d", sp, some (.int 10)⟩] 0 == false
#guard arityOk #[⟨"x", sp, Option.none⟩, ⟨"d", sp, some (.int 10)⟩] 3 == false
#guard mkCallEnv #[⟨"x", sp, Option.none⟩, ⟨"d", sp, some (.int 10)⟩] #[.int 1]
    == [("x", .int 1), ("d", .int 10)]
#guard mkCallEnv #[⟨"x", sp, Option.none⟩, ⟨"d", sp, some (.int 10)⟩] #[.int 1, .int 2]
    == [("x", .int 1), ("d", .int 2)]

/-! ## Timeout / fuel discipline -/

#guard evIn M0 0 [] (iL 1) == (.timeout : Res RVal)
#guard execStmt M0 0 ⟨w0, []⟩ (.pass sp) == (.timeout : Run FrameState RFlow)
#guard execStmts M0 0 ⟨w0, []⟩ [] == (.timeout : Run FrameState RFlow)
#guard callFunction M1 "ident" #[.int 1] 0 == (.timeout : Res Val)
-- Fuel is a depth bound: fuel 2 cannot evaluate a depth-3 expression.
#guard evIn M0 2 [] (bo (bo (iL 1) .add (iL 1)) .add (iL 1)) == .timeout
-- Infinite loop times out with small fuel.
#guard callFunction M1 "loopForever" #[] 50 == .timeout

/-! ## Statements: assignment and tuple unpacking -/

#guard run [.assign #[nm "x"] (iL 1) sp] == .ok ([("x", .int 1)], .next)
#guard run [.assign #[.tuple #[nm "a", nm "b"] sp] (.tuple #[iL 1, iL 2] sp) sp]
    == .ok ([("a", .int 1), ("b", .int 2)], .next)
#guard run [.assign #[.list #[nm "a", nm "b"] sp] (.tuple #[iL 1, iL 2] sp) sp]
    == .ok ([("a", .int 1), ("b", .int 2)], .next)
#guard run [.assign #[.tuple #[nm "a", nm "b"] sp] (.list #[iL 1, iL 2] sp) sp]
    == .ok ([("a", .int 1), ("b", .int 2)], .next)
-- a, b = b, a  (swap: RHS evaluated before stores)
#guard run [.assign #[.tuple #[nm "a", nm "b"] sp] (.tuple #[nm "b", nm "a"] sp) sp]
        (env := [("a", .int 1), ("b", .int 2)])
    == .ok ([("a", .int 2), ("b", .int 1)], .next)
#guard isValueError (run [.assign #[.tuple #[nm "a", nm "b"] sp] (.list #[iL 1, iL 2, iL 3] sp) sp])
#guard isValueError (run [.assign #[.tuple #[nm "a", nm "b"] sp] (.list #[iL 1] sp) sp])
#guard isTypeError (run [.assign #[.tuple #[nm "a", nm "b"] sp] (iL 5) sp])
#guard isUnsupported (run [.assign #[.tuple #[nm "a", nm "b"] sp] (sL "xy") sp])
#guard isUnsupported (run [.assign #[nm "a", nm "b"] (iL 1) sp])   -- chained a = b = 1
#guard isUnsupported (run [.assign #[.subscript (nm "xs") (iL 0) sp] (iL 1) sp]
        (env := [("xs", .listV #[.int 0])]))
-- Value is evaluated before the (unsupported) store, CPython error order:
#guard run [.assign #[.subscript (nm "xs") (iL 0) sp] boom sp]
        (env := [("xs", .listV #[.int 0])]) == .exn .zeroDivisionError
-- Nested unpacking targets are out of tier:
#guard isUnsupported (run [.assign #[.tuple #[nm "a", .tuple #[nm "b", nm "c"] sp] sp]
        (.tuple #[iL 1, .tuple #[iL 2, iL 3] sp] sp) sp])

/-! ## AugAssign -/

#guard run [.augAssign (nm "x") .add (iL 2) sp] (env := [("x", .int 5)])
    == .ok ([("x", .int 7)], .next)
#guard run [.augAssign (nm "x") .add (iL 2) sp] == .exn (.nameError "x")
-- Target is loaded before the value is evaluated (UnboundLocalError order):
#guard run [.augAssign (nm "x") .add boom sp] == .exn (.nameError "x")
#guard run [.augAssign (nm "x") .add boom sp] (env := [("x", .int 5)])
    == .exn .zeroDivisionError
#guard isUnsupported (run [.augAssign (.subscript (nm "xs") (iL 0) sp) .add (iL 1) sp]
        (env := [("xs", .listV #[.int 0])]))

/-! ## If / truthiness, Expr statements, Pass -/

#guard run [.ifStmt (.list #[] sp) #[.assign #[nm "r"] (iL 1) sp]
                                   #[.assign #[nm "r"] (iL 2) sp] sp]
    == .ok ([("r", .int 2)], .next)
#guard run [.ifStmt (sL "a") #[.assign #[nm "r"] (iL 1) sp] #[] sp]
    == .ok ([("r", .int 1)], .next)
#guard run [.pass sp] == .ok ([], .next)
#guard run [.exprStmt (iL 42) sp] == .ok ([], .next)     -- evaluate, discard
#guard run [.exprStmt boom sp] == .exn .zeroDivisionError -- ... but errors propagate
#guard run [.ret (some (iL 3)) sp, .assign #[nm "x"] (iL 1) sp]
    == .ok ([], .ret (.int 3))                            -- return stops the block

/-! ## While / orelse / break / continue -/

-- i = 0; while i < 3: i += 1; else: r = 99  → orelse runs on normal exit
#guard run [.assign #[nm "i"] (iL 0) sp,
            .whileLoop (cmp1 (nm "i") .lt (iL 3))
              #[.augAssign (nm "i") .add (iL 1) sp]
              #[.assign #[nm "r"] (iL 99) sp] sp]
    == .ok ([("i", .int 3), ("r", .int 99)], .next)
-- i = 0; while True: i += 1; if i == 2: break; else: r = 99  → break skips orelse
#guard run [.assign #[nm "i"] (iL 0) sp,
            .whileLoop (bL true)
              #[.augAssign (nm "i") .add (iL 1) sp,
                .ifStmt (cmp1 (nm "i") .eq (iL 2)) #[.brk sp] #[] sp]
              #[.assign #[nm "r"] (iL 99) sp] sp]
    == .ok ([("i", .int 2)], .next)
-- continue: total = sum of odd i in 1..4 → i=4, total=1+3=4
#guard run [.assign #[nm "i"] (iL 0) sp,
            .assign #[nm "total"] (iL 0) sp,
            .whileLoop (cmp1 (nm "i") .lt (iL 4))
              #[.augAssign (nm "i") .add (iL 1) sp,
                .ifStmt (cmp1 (bo (nm "i") .mod (iL 2)) .eq (iL 0)) #[.cont sp] #[] sp,
                .augAssign (nm "total") .add (nm "i") sp]
              #[] sp]
    == .ok ([("i", .int 4), ("total", .int 4)], .next)
-- break/continue outside any loop surface as flow to the caller of execStmts
#guard run [.brk sp] == .ok ([], .brk)
#guard run [.cont sp] == .ok ([], .cont)

/-! ## Unsupported constructs are loud -/

#guard execStmt M0 10 ⟨w0, []⟩ (.unsupported "For" "for i in range(3):\n    pass" sp)
    == .unsupported "unsupported statement 'For'"
#guard execStmt M0 10 ⟨w0, []⟩ (.unsupported "Try" "try: ..." sp)
    == .unsupported "unsupported statement 'Try'"
#guard ev (.unsupported "Lambda" "lambda x: x" sp) == .unsupported "unsupported expression 'Lambda'"
#guard ev (.unsupported "Constant:float" "1.5" sp) == .unsupported "unsupported expression 'Constant:float'"
-- Unsupported inside dead code is never reached:
#guard run [.ifStmt (bL false) #[.unsupported "For" "for ..." sp] #[] sp] == .ok ([], .next)

/-! ## End-to-end: extractor envelopes → Json.lean → interpreter

Read at `#eval` time (cwd = package root under `lake build`); any parse
failure or wrong result throws, failing the build loudly. -/

private def loadModule (path : System.FilePath) : IO Module := do
  let txt ← IO.FS.readFile path
  match parseEnvelopeString txt with
  | .error e => throw (IO.userError s!"{path}: envelope parse error: {e}")
  | .ok env => return env.module

private def checkCall (path : System.FilePath) (fn : String) (args : Array Val)
    (fuel : Nat) (expected : Res Val) : IO Unit := do
  let m ← loadModule path
  let got := callFunction m fn args fuel
  unless got == expected do
    throw (IO.userError
      s!"{path}: {fn} {repr args} (fuel {fuel}) = {repr got}, expected {repr expected}")

#eval checkCall "Examples/python/tri/tri.json" "tri" #[.int 10] 1000 (.ok (.int 55))
#eval checkCall "Examples/python/tri/tri.json" "tri" #[.int 0] 1000 (.ok (.int 0))
#eval checkCall "Examples/python/tri/tri.json" "tri" #[.int (-3)] 1000 (.ok (.int 0))
#eval checkCall "Examples/python/tri/tri.json" "tri" #[.int 10] 5 .timeout
#eval checkCall "Examples/python/fib/fib.json" "fib" #[.int 10] 1000 (.ok (.int 55))
#eval checkCall "Examples/python/fib/fib.json" "fib" #[.int 1] 1000 (.ok (.int 1))
#eval checkCall "Examples/python/fib/fib.json" "fib" #[.int (-5)] 1000 (.ok (.int (-5)))
#eval checkCall "Examples/python/add/add.json" "add" #[.int 2, .int 3] 1000 (.ok (.int 5))
#eval checkCall "Examples/python/add/add.json" "add" #[.int (-2), .int 3] 1000 (.ok (.int 1))
#eval checkCall "Examples/python/add/add.json" "add" #[.str "ab", .str "cd"] 1000 (.ok (.str "abcd"))
#eval checkCall "Examples/python/add/add.json" "add" #[.str "ab", .int 1] 1000
        (.exn (.typeError "unsupported operand type(s) for +: 'str' and 'int'"))
#eval checkCall "Examples/python/add/add.json" "nosuch" #[] 1000 (.exn (.nameError "nosuch"))
-- F1/F2 end-to-end (extractor emits param defaults + Is/IsNot; parser and
-- interpreter consume them):
#eval checkCall "Examples/python/opt_args/opt_args.json" "clamp" #[.int 5] 1000 (.ok (.int 5))
#eval checkCall "Examples/python/opt_args/opt_args.json" "clamp" #[.int 150] 1000 (.ok (.int 100))
#eval checkCall "Examples/python/opt_args/opt_args.json" "clamp" #[.int 5, .int 2, .int 3] 1000
        (.ok (.int 3))
#eval checkCall "Examples/python/opt_args/opt_args.json" "clamp" #[] 1000
        (.exn (.typeError "clamp() takes 3 positional arguments but 0 were given"))
#eval checkCall "Examples/python/opt_args/opt_args.json" "is_none" #[.none] 1000
        (.ok (.bool true))
#eval checkCall "Examples/python/opt_args/opt_args.json" "latest" #[.int 3] 1000 (.ok (.int 3))
#eval checkCall "Examples/python/opt_args/opt_args.json" "latest" #[.int 3, .int 5] 1000
        (.ok (.int 5))
#eval checkCall "Examples/python/opt_args/opt_args.json" "pad" #[.int 5, .int 3, .bool true] 1000
        (.ok (.tuple #[.int 8, .str ""]))
#eval checkCall "Examples/python/opt_args/opt_args.json" "none_is_none" #[] 1000
        (.ok (.bool true))
-- call:sorted end-to-end (the vendored CPython statistics medians run from
-- their envelope; expected values are CPython 3.9.25 ground truth):
#eval checkCall "Examples/python/bench_statistics/bench_statistics.json" "median_low"
        #[.list #[.int 7, .int 1, .int 5, .int 3]] 1000 (.ok (.int 3))
#eval checkCall "Examples/python/bench_statistics/bench_statistics.json" "median_high"
        #[.list #[.int 7, .int 1, .int 5, .int 3]] 1000 (.ok (.int 5))
#eval checkCall "Examples/python/bench_statistics/bench_statistics.json" "median_low"
        #[.list #[.int 5, .int 1, .int 3]] 1000 (.ok (.int 3))
#eval checkCall "Examples/python/bench_statistics/bench_statistics.json" "median_high"
        #[.list #[.int 5, .int 1, .int 3]] 1000 (.ok (.int 3))
#eval checkCall "Examples/python/bench_statistics/bench_statistics.json" "median_low"
        #[.int 3] 1000 (.exn (.typeError "'int' object is not iterable"))

/-! ## Spec layer end-to-end: `load_program` → literal `Module` → proofs

`load_program` runs at *elaboration* time: it reads the extractor-generated
envelope, parses it with `Json.lean`, and quotes the result via the `ToExpr`
instances into a **literal** `Module` constant. The `#guard` below therefore
exercises the whole pipeline (extractor JSON → parser → `ToExpr` literal →
compiled interpreter); the `example` confirms the literal also unfolds for
*proofs*, by plain kernel reduction (`rfl` — no `native_decide`). -/

load_program add from "Examples/python/add/add.json"

#guard callFunction add "add" #[.int 2, .int 3] 100 == .ok (.int 5)

-- The loaded constant is first-order data: kernel reduction and simp-unfolding
-- both work, so partial-correctness proofs can treat `add` as a literal.
example : CallsTo add "add" #[.int 2, .int 3] (.int 5) := ⟨100, by rfl⟩
example : CallsTo add "add" #[.int 2, .int 3] (.int 5) := ⟨100, rfl⟩
example : add.functions.size = 1 := by simp [add]
example : (add.functions[0]!).name = "add" := by simp [add]

-- `@[spec]` (core Lean's mvcgen spec attribute on this toolchain — see
-- `Logic.lean`) accepts simp-shaped registered lemmas; smoke-test it compiles.
@[spec] theorem callFunction_zero_timeout (m : Module) (f : String)
    (args : Array Val) : callFunction m f args 0 = .timeout := rfl

-- `#print_program add` is available interactively to inspect a loaded module's
-- `Repr`; not invoked here — it would log its full dump on every build.

end LeanModels.Python.Tests
