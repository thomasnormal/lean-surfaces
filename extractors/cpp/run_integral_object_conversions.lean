import LeanModels.Cpp.IntegralObjects

open LeanModels.Cpp

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

private def evaluate (line : String) : Except String IntegralValue := do
  let [destinationText, sourceText, initialText, replacementText] := line.splitOn "\t"
    | .error "expected four tab-separated fields"
  let (destinationType, _) ← parseType destinationText
  let (sourceType, sourceFormat) ← parseType sourceText
  let some initial := initialText.toInt? | .error "invalid initial integer"
  let some replacement := replacementText.toInt? | .error "invalid replacement integer"
  let store ← (IntegralObjectStore.empty .lp64).mapError reprStr
  let (store, object) ← (store.allocate .automatic destinationType).mapError reprStr
  let store ← (store.initializeConverted object sourceType ⟨sourceFormat, initial⟩).mapError reprStr
  let access ← (store.borrow object).mapError reprStr
  let store ← (store.assignConverted access sourceType ⟨sourceFormat, replacement⟩).mapError reprStr
  (store.read access).mapError reprStr

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
    | .ok value => output.putStrLn s!"{renderFormat value.format} {value.value}"
    | .error message => IO.eprintln message; return 1
  return 0
