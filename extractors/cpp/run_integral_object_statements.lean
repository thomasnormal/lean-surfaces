import LeanModels.Cpp.IntegralObjectStatements

open LeanModels.Cpp

private def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩

private def statementFor (mode : String) (access : IntegralObjectRef) (delta : Int) :
    Except String IntegralObjectStatement :=
  let addition := .binary .add (.read access) (.literal (signed delta))
  let assignment := .assign access (.builtin .int) addition
  match mode with
  | "add" => .ok assignment
  | "branch" =>
      .ok (.conditional (.read access)
        (.assign access (.builtin .int) (.literal (signed delta)))
        (.assign access (.builtin .int) (.literal (signed (delta + 1)))))
  | "loop" =>
      .ok (.whileLoop
        (.binary .greater (.read access) (.literal (signed 0)))
        (.assign access (.builtin .int)
          (.binary .subtract (.read access) (.literal (signed 1)))))
  | "for" =>
      .ok (.forLoop
        (.assign access (.builtin .int) (.literal (signed delta)))
        (.binary .greater (.read access) (.literal (signed 0)))
        (.assign access (.builtin .int)
          (.binary .subtract (.read access) (.literal (signed 1))))
        (.expression (.read access)))
  | "break" =>
      .ok (.whileLoop
        (.binary .greater (.read access) (.literal (signed 0)))
        (.sequence
          (.assign access (.builtin .int)
            (.binary .subtract (.read access) (.literal (signed 1))))
          .break_))
  | "continue" =>
      .ok (.whileLoop
        (.binary .greater (.read access) (.literal (signed 0)))
        (.sequence
          (.assign access (.builtin .int)
            (.binary .subtract (.read access) (.literal (signed 1))))
          .continue_))
  | "for_continue" =>
      .ok (.forLoop
        (.assign access (.builtin .int) (.literal (signed 3)))
        (.binary .greater (.read access) (.literal (signed 0)))
        (.assign access (.builtin .int)
          (.binary .subtract (.read access) (.literal (signed 1))))
        (.sequence
          (.assign access (.builtin .int)
            (.binary .subtract (.read access) (.literal (signed 1))))
          .continue_))
  | "sequence" =>
      .ok (.sequence assignment
        (.assign access (.builtin .int) (.unary .negate (.read access))))
  | _ => .error "unknown integral object statement mode"

private def evaluate (line : String) : Except String IntegralValue := do
  let [mode, initialText, deltaText] := line.splitOn "\t"
    | .error "expected three tab-separated fields"
  let some initial := initialText.toInt? | .error "invalid initial integer"
  let some delta := deltaText.toInt? | .error "invalid delta integer"
  let store ← (IntegralObjectStore.empty .lp64).mapError reprStr
  let (store, object) ← (store.allocate .automatic (.builtin .int)).mapError reprStr
  let store ← (store.initializeValue object (signed initial)).mapError reprStr
  let access ← (store.borrow object).mapError reprStr
  let statement ← statementFor mode access delta
  let store ← (executeIntegralObjectStatement 64 store statement).mapError reprStr
  (store.read access).mapError reprStr

def main : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then return 0
    match evaluate line.trimAscii.toString with
    | .ok value => output.putStrLn s!"s32 {value.value}"
    | .error message => IO.eprintln message; return 1
  return 0
