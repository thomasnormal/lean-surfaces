import LeanModels.Python.Float64
import Lean

open Lean LeanModels.Python

def naturalField (input : Json) (name : String) : Except String Nat := do
  let text ← input.getObjValAs? String name
  match text.toNat? with
  | some value => return value
  | none => throw s!"invalid natural field {name}"

def integerField (input : Json) (name : String) : Except String Int := do
  let text ← input.getObjValAs? String name
  match text.toInt? with
  | some value => return value
  | none => throw s!"invalid integer field {name}"

def floatField (input : Json) (name : String) : Except String Float64 := do
  let bits ← naturalField input name
  unless bits < 2 ^ 64 do throw "bits exceed binary64 width"
  return Float64.ofBits bits

def numberJson (number : Float64) : Json := Json.mkObj [
  ("bits", .str (toString number.bits.toNat)),
  ("repr", match number.repr with | some text => .str text | none => .null)]

def comparisonJson (equal less greater : Bool) : Json := Json.mkObj [
  ("equal", .bool equal), ("less", .bool less), ("greater", .bool greater)]

def floatDivisionJson (result : Except Float64.FloatDivisionError Float64) : Except String Json :=
  match result with
  | .ok value => .ok (numberJson value)
  | .error .zeroDivision => .ok (Json.mkObj [
      ("error", .str "ZeroDivisionError"), ("message", .str "float division by zero")])
  | .error .conversionOverflow => .ok (Json.mkObj [
      ("error", .str "OverflowError"), ("message", .str "int too large to convert to float")])
  | .error .nonFinite => .error "non-finite float division remains unmodelled"

def arithmeticOperator (input : Json) : Except String Float64.ArithmeticOp := do
  match ← input.getObjValAs? String "operator" with
  | "add" => return .add
  | "sub" => return .sub
  | "mult" => return .mult
  | _ => throw "unknown float arithmetic operator"

def arithmeticJson (result : Except Float64.ArithmeticError Float64) : Json :=
  match result with
  | .ok value => numberJson value
  | .error .conversionOverflow => Json.mkObj [
      ("error", .str "OverflowError"), ("message", .str "int too large to convert to float")]
  | .error .nanPayload => Json.mkObj [("refused", .str "nan-payload")]

def checkRow (input : Json) : Except String Json := do
  let kind ← input.getObjValAs? String "kind"
  if kind == "neg" then
    return numberJson (← floatField input "bits").neg
  if kind == "float_arithmetic" then
    let operator ← arithmeticOperator input
    let left ← floatField input "left"
    let right ← floatField input "right"
    return arithmeticJson (Float64.arithmetic operator left right)
  if kind == "int_float_arithmetic" then
    let operator ← arithmeticOperator input
    let left ← integerField input "left"
    let right ← floatField input "right"
    return arithmeticJson (Float64.arithmeticIntFloat operator left right)
  if kind == "float_int_arithmetic" then
    let operator ← arithmeticOperator input
    let left ← floatField input "left"
    let right ← integerField input "right"
    return arithmeticJson (Float64.arithmeticFloatInt operator left right)
  if kind == "integer_conversion" then
    let value ← floatField input "bits"
    let integerJson (integer : Option Int) : Json :=
      match integer with | some result => .str (toString result) | none => .null
    return Json.mkObj [
      ("integer", integerJson value.toInt),
      ("integral", integerJson value.toIntegralInt)]
  if kind == "float_compare" then
    let left ← floatField input "left"
    let right ← floatField input "right"
    return comparisonJson (left.eqv right) (left.lt right) (right.lt left)
  if kind == "int_compare" then
    let left ← floatField input "left"
    let right ← integerField input "right"
    return comparisonJson (left.eqInt right) (left.ltInt right) (Float64.intLt right left)
  if kind == "conversion" then
    let integer ← integerField input "integer"
    match Float64.fromInt integer with
    | some number => return numberJson number
    | none => return Json.mkObj [
        ("error", .str "OverflowError"), ("message", .str "int too large to convert to float")]
  if kind == "float_division" then
    let left ← floatField input "left"
    let right ← floatField input "right"
    return ← floatDivisionJson (Float64.divideFinite left right)
  if kind == "int_float_division" then
    let left ← integerField input "left"
    let right ← floatField input "right"
    return ← floatDivisionJson (Float64.divideIntFloat left right)
  if kind == "float_int_division" then
    let left ← floatField input "left"
    let right ← integerField input "right"
    return ← floatDivisionJson (Float64.divideFloatInt left right)
  if kind == "division" then
    let left ← integerField input "left"
    let right ← integerField input "right"
    match Float64.divideInt left right with
    | .error .zeroDivision => return Json.mkObj [
        ("error", .str "ZeroDivisionError"), ("message", .str "division by zero")]
    | .error .overflow => return Json.mkObj [
        ("error", .str "OverflowError"),
        ("message", .str "integer division result too large for a float")]
    | .ok number => return numberJson number
  let value ← if kind == "repr" then do
    pure (some (← floatField input "bits"))
  else if kind == "ratio" then do
    let negative ← input.getObjValAs? Bool "negative"
    let numerator ← naturalField input "numerator"
    let denominator ← naturalField input "denominator"
    pure (Float64.fromRatio negative numerator denominator)
  else throw "unknown float check kind"
  match value with
  | none => return Json.mkObj [("bits", .null), ("repr", .null)]
  | some number => return numberJson number

def main (arguments : List String) : IO UInt32 := do
  let [filename] := arguments | throw (IO.userError "expected input JSON filename")
  let contents ← IO.FS.readFile filename
  let input ← match Json.parse contents with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  let rows ← match input.getArr? with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  for row in rows do
    match checkRow row with
    | .ok output => IO.println output.compress
    | .error message => throw (IO.userError message)
  return 0
