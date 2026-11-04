import LeanModels.Cpp.Integral

open LeanModels.Cpp

private def parseFormat (text : String) : Except String IntegralFormat :=
  if text == "b" then .ok .boolean
  else match text.toList with
    | 's' :: digits =>
        match (String.ofList digits).toNat? with
        | some width => .ok (.signed width)
        | none => .error "invalid signed width"
    | 'u' :: digits =>
        match (String.ofList digits).toNat? with
        | some width => .ok (.unsigned width)
        | none => .error "invalid unsigned width"
    | _ => .error "invalid format"

private def parseBinary : String → Except String IntegralBinary
  | "add" => .ok .add
  | "sub" => .ok .subtract
  | "mul" => .ok .multiply
  | "div" => .ok .divide
  | "rem" => .ok .remainder
  | "shl" => .ok .shiftLeft
  | "shr" => .ok .shiftRight
  | "and" => .ok .bitAnd
  | "or" => .ok .bitOr
  | "xor" => .ok .bitXor
  | "eq" => .ok .equal
  | "ne" => .ok .notEqual
  | "lt" => .ok .less
  | "le" => .ok .lessEqual
  | "gt" => .ok .greater
  | "ge" => .ok .greaterEqual
  | _ => .error "unknown operation"

private def parseValue (format value : String) : Except String IntegralValue := do
  let format ← parseFormat format
  let some value := value.toInt? | .error "invalid integer"
  .ok ⟨format, value⟩

private def evaluate (line : String) : Except String (IntegralResult IntegralValue) := do
  let [operation, leftFormat, leftValue, rightFormat, rightValue] := line.splitOn "\t"
    | .error "expected five tab-separated fields"
  let left ← parseValue leftFormat leftValue
  match operation with
  | "convert" => return integralConvert (← parseFormat rightFormat) left
  | "plus" => return integralUnary .plus left
  | "neg" => return integralUnary .negate left
  | "not" => return integralUnary .logicalNot left
  | "compl" => return integralUnary .complement left
  | _ => return integralBinary (← parseBinary operation) left (← parseValue rightFormat rightValue)

private def renderFormat : IntegralFormat → String
  | .boolean => "b"
  | .signed width => s!"s{width}"
  | .unsigned width => s!"u{width}"

private def render : IntegralResult IntegralValue → String
  | .ok value => s!"ok {renderFormat value.format} {value.value}"
  | .invalid _ => "invalid"
  | .undefined _ => "ub"
  | .unsupported _ => "unsupported"

def main : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then return 0
    match evaluate line.trimAscii.toString with
    | .ok result => output.putStrLn (render result)
    | .error message => IO.eprintln message; return 1
  return 0
