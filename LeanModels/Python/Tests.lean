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
  { name := "ident", params := #[⟨"x", sp⟩], argsOk := true,
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
  { name := "cd", params := #[⟨"n", sp⟩], argsOk := true,
    body := #[.ifStmt (cmp1 (nm "n") .ltE (iL 0)) #[.ret (some (iL 0)) sp] #[] sp,
              .ret (some (.call (nm "cd") #[bo (nm "n") .sub (iL 1)] Option.none sp)) sp],
    span := sp }

private def M1 : Module :=
  { functions := #[fnIdent, fnLoopForever, fnBadArgs, fnFallOff, fnBareRet, fnCountdown],
    topLevel := #[] }

private def ev (e : Expr) (env : Env := []) (fuel : Nat := 100) : Res Val :=
  evalExpr M0 fuel env e
private def run (ss : List Stmt) (env : Env := []) (fuel : Nat := 1000) :
    Res (Env × Flow) :=
  execStmts M0 fuel env ss

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
#guard ev (bo (.list #[iL 1] sp) .add (.list #[iL 2] sp)) == .ok (.list #[.int 1, .int 2])
#guard ev (bo (.tuple #[iL 1] sp) .add (.tuple #[iL 2] sp)) == .ok (.tuple #[.int 1, .int 2])
#guard isTypeError (ev (bo (sL "a") .add (iL 1)))
#guard isTypeError (ev (bo (.list #[iL 1] sp) .add (.tuple #[iL 2] sp)))
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
#guard valEq (.list #[.int 1, .list #[.int 2, .bool true]])
             (.list #[.int 1, .list #[.int 2, .int 1]])
#guard !valEq (.list #[.int 1]) (.list #[.int 1, .int 2])
#guard !valEq (.str "1") (.int 1)

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
#guard ev (.boolOp .or #[iL 0, sL "", .list #[] sp] sp) == .ok (.list #[])
#guard ev (.boolOp .or #[iL 2, boom] sp) == .ok (.int 2)      -- short-circuit skips 1//0
#guard ev (.boolOp .and #[iL 0, boom] sp) == .ok (.int 0)
#guard ev (.boolOp .and #[iL 1, boom] sp) == .exn .zeroDivisionError

/-! ## Truthiness and `not` -/

#guard ev (.unaryOp .not (iL 0) sp) == .ok (.bool true)
#guard ev (.unaryOp .not (sL "a") sp) == .ok (.bool false)
#guard ev (.unaryOp .not noneL sp) == .ok (.bool true)
#guard ev (.unaryOp .not (.tuple #[iL 0] sp) sp) == .ok (.bool false)
#guard isTypeError (ev (.unaryOp .usub (sL "a") sp))
#guard truthy (.list #[]) == false
#guard truthy (.str " ") == true
#guard truthy (.int (-1)) == true

/-! ## Name resolution: local env → function table → `len` → NameError -/

#guard ev (nm "zzz") == .exn (.nameError "zzz")
#guard ev (nm "x") (env := [("x", .int 5)]) == .ok (.int 5)
#guard Env.lookup [("x", .int 1), ("x", .int 2)] "x" == some (.int 1)  -- first match wins
#guard isUnsupported (evalExpr M1 100 [] (nm "ident"))       -- function as a value
#guard isUnsupported (ev (nm "len"))                          -- builtin as a value
-- Local binding shadows the function table (shadowed value is not callable):
#guard evalExpr M1 100 [("ident", .int 3)] (nm "ident") == .ok (.int 3)
#guard isTypeError (evalExpr M1 100 [("ident", .int 3)] (.call (nm "ident") #[] Option.none sp))

/-! ## `Env.set`: replace in place, else append -/

#guard Env.set [] "x" (.int 1) == [("x", .int 1)]
#guard Env.set [("x", .int 1), ("y", .int 2)] "x" (.int 3) == [("x", .int 3), ("y", .int 2)]
#guard Env.set [("x", .int 1)] "y" (.int 2) == [("x", .int 1), ("y", .int 2)]

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

#guard ev (.call (nm "len") #[sL "abc"] Option.none sp) == .ok (.int 3)
#guard ev (.call (nm "len") #[.list #[] sp] Option.none sp) == .ok (.int 0)
#guard ev (.call (nm "len") #[.tuple #[iL 1, iL 2] sp] Option.none sp) == .ok (.int 2)
#guard ev (.call (nm "len") #[sL "hé"] Option.none sp) == .ok (.int 2)
#guard isTypeError (ev (.call (nm "len") #[iL 5] Option.none sp))
#guard isTypeError (ev (.call (nm "len") #[sL "a", sL "b"] Option.none sp))

/-! ## Left-to-right, once-only evaluation (observable via error order) -/

#guard ev (bo boom .add (nm "zzz")) == .exn .zeroDivisionError    -- left first
#guard ev (bo (nm "zzz") .add boom) == .exn (.nameError "zzz")
-- Callee name resolves before arguments are evaluated (CPython order):
#guard ev (.call (nm "zzz") #[boom] Option.none sp) == .exn (.nameError "zzz")
-- Arguments are evaluated before the call happens:
#guard evalExpr M1 100 [] (.call (nm "ident") #[boom] Option.none sp) == .exn .zeroDivisionError
-- List/tuple literals evaluate elements left to right:
#guard ev (.list #[iL 1, bo (iL 1) .add (iL 1)] sp) == .ok (.list #[.int 1, .int 2])
#guard ev (.tuple #[boom, nm "zzz"] sp) == .exn .zeroDivisionError

/-! ## Calls: keywords/starargs flag, non-name callee, arity, argsOk -/

#guard isUnsupported (evalExpr M1 100 [] (.call (nm "ident") #[iL 1] (some "keywords") sp))
#guard isUnsupported (ev (.call (iL 5) #[] Option.none sp))
#guard callFunction M1 "ident" #[.int 7] 100 == .ok (.int 7)
#guard isTypeError (callFunction M1 "ident" #[] 100)               -- arity mismatch
#guard isTypeError (callFunction M1 "ident" #[.int 1, .int 2] 100)
#guard isUnsupported (callFunction M1 "badArgs" #[] 100)           -- argsOk = false
#guard callFunction M1 "nosuch" #[] 100 == .exn (.nameError "nosuch")
#guard callFunction M1 "fallOff" #[] 100 == .ok .none              -- fall off the end
#guard callFunction M1 "bareRet" #[] 100 == .ok .none              -- bare `return`
#guard callFunction M1 "cd" #[.int 5] 200 == .ok (.int 0)          -- recursion
#guard callFunction M1 "cd" #[.int 1000] 100 == .timeout           -- fuel bounds depth

/-! ## Timeout / fuel discipline -/

#guard evalExpr M0 0 [] (iL 1) == (.timeout : Res Val)
#guard execStmt M0 0 [] (.pass sp) == (.timeout : Res (Env × Flow))
#guard execStmts M0 0 [] [] == (.timeout : Res (Env × Flow))
#guard callFunction M1 "ident" #[.int 1] 0 == (.timeout : Res Val)
-- Fuel is a depth bound: fuel 2 cannot evaluate a depth-3 expression.
#guard evalExpr M0 2 [] (bo (bo (iL 1) .add (iL 1)) .add (iL 1)) == .timeout
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
        (env := [("xs", .list #[.int 0])]))
-- Value is evaluated before the (unsupported) store, CPython error order:
#guard run [.assign #[.subscript (nm "xs") (iL 0) sp] boom sp]
        (env := [("xs", .list #[.int 0])]) == .exn .zeroDivisionError
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
        (env := [("xs", .list #[.int 0])]))

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

#guard execStmt M0 10 [] (.unsupported "For" "for i in range(3):\n    pass" sp)
    == .unsupported "unsupported statement 'For'"
#guard execStmt M0 10 [] (.unsupported "Try" "try: ..." sp)
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
