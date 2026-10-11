import LeanModels.Cpp.IntegralObjects

open LeanModels.Cpp

private def trace (type : CppTypeEvidence) (initial replacement : IntegralValue) :
    Except IntegralObjectError (List IntegralValue) := do
  let store ← IntegralObjectStore.empty .lp64
  let (store, first) ← store.allocate .automatic type
  let store ← store.defaultInitialize first
  let access ← store.borrow first
  let store ← store.assign access initial
  let readOnly ← store.borrow first true
  let (store, distinct) ← store.allocate .automatic (.qualified true false type)
  let store ← store.initializeValue distinct initial
  let distinctAccess ← store.borrow distinct
  let before ← store.read access
  let store ← store.assign access replacement
  let after ← store.read readOnly
  let untouched ← store.read distinctAccess
  let (store, dynamic) ← store.allocate .dynamic type
  let store ← store.initializeValue dynamic initial
  let dynamicAccess ← store.borrow dynamic
  let store ← store.assign dynamicAccess replacement
  let dynamicValue ← store.read dynamicAccess
  let store ← store.endLifetime dynamic
  let _ ← store.releaseStorage dynamic
  pure [before, after, untouched, dynamicValue]

private def parseType : String → Except String (CppTypeEvidence × IntegralFormat)
  | "b" => .ok (.builtin .boolean, .boolean)
  | "s8" => .ok (.builtin .signedChar, .signed 8)
  | "u8" => .ok (.builtin .unsignedChar, .unsigned 8)
  | "s16" => .ok (.builtin .short, .signed 16)
  | "u16" => .ok (.builtin .unsignedShort, .unsigned 16)
  | "s32" => .ok (.builtin .int, .signed 32)
  | "u32" => .ok (.builtin .unsignedInt, .unsigned 32)
  | "s64" => .ok (.builtin .longLong, .signed 64)
  | "u64" => .ok (.builtin .unsignedLongLong, .unsigned 64)
  | _ => .error "unknown integral object format"

private def evaluate (line : String) : Except String (List IntegralValue) := do
  let [format, initialText, replacementText] := line.splitOn "\t"
    | .error "expected three tab-separated fields"
  let (type, format) ← parseType format
  let some initial := initialText.toInt? | .error "invalid initial integer"
  let some replacement := replacementText.toInt? | .error "invalid replacement integer"
  (trace type ⟨format, initial⟩ ⟨format, replacement⟩).mapError reprStr

private def renderFormat : IntegralFormat → String
  | .boolean => "b"
  | .signed width => s!"s{width}"
  | .unsigned width => s!"u{width}"

def main : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then return 0
    match evaluate line.trimAscii.toString with
    | .ok values =>
        output.putStrLn (String.intercalate " "
          (values.map fun value => s!"{renderFormat value.format} {value.value}"))
    | .error message => IO.eprintln message; return 1
  return 0
