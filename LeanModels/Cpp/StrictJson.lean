import LeanModels.Cpp.Ast
import Std.Internal.Parsec

namespace LeanModels.Cpp

open Std.Internal.Parsec Std.Internal.Parsec.String

namespace StrictJson

private def hexValue : Parser UInt32 := do
  let character ← any
  if '0' ≤ character && character ≤ '9' then
    return character.val - '0'.val
  else if 'a' ≤ character && character ≤ 'f' then
    return character.val - 'a'.val + 10
  else if 'A' ≤ character && character ≤ 'F' then
    return character.val - 'A'.val + 10
  else
    fail "invalid Unicode escape digit"

private def codeUnit : Parser UInt32 := do
  let first ← hexValue
  let second ← hexValue
  let third ← hexValue
  let fourth ← hexValue
  return first * 4096 + second * 256 + third * 16 + fourth

private def scalar (value : UInt32) : Parser Char := do
  if valid : value.isValidChar then
    return ⟨value, valid⟩
  else
    fail "invalid Unicode scalar"

private def unicodeEscape : Parser Char := do
  let value ← codeUnit
  if 0xD800 ≤ value && value ≤ 0xDBFF then
    skipString "\\u"
    let low ← codeUnit
    if low < 0xDC00 || 0xDFFF < low then
      fail "expected low Unicode surrogate"
    else
      scalar (0x10000 + (value - 0xD800) * 1024 + low - 0xDC00)
  else if 0xDC00 ≤ value && value ≤ 0xDFFF then
    fail "lone low Unicode surrogate"
  else
    scalar value

private def escapedCharacter : Parser Char := do
  match ← any with
  | '"' => return '"'
  | '\\' => return '\\'
  | '/' => return '/'
  | 'b' => return '\x08'
  | 'f' => return '\x0c'
  | 'n' => return '\n'
  | 'r' => return '\r'
  | 't' => return '\t'
  | 'u' => unicodeEscape
  | _ => fail "invalid JSON string escape"

private partial def stringBody (accumulator : String) : Parser String := do
  let character ← any
  if character == '"' then
    return accumulator
  else if character == '\\' then
    stringBody (accumulator.push (← escapedCharacter))
  else if character.val < 0x20 then
    fail "unescaped control character in JSON string"
  else
    stringBody (accumulator.push character)

private def stringValue : Parser String := do
  skipChar '"'
  stringBody ""

private def isDigit (character : Char) : Bool :=
  '0' ≤ character && character ≤ '9'

private partial def integerDigits (accumulator : String) : Parser String := do
  match ← peek? with
  | some character =>
    if isDigit character then
      skip
      integerDigits (accumulator.push character)
    else
      return accumulator
  | none => return accumulator

private def integerValue : Parser Raw := do
  let sign ← if (← peek!) == '-' then skip *> pure "-" else pure ""
  let first ← any
  if !isDigit first then fail "expected JSON integer digit"
  let token ← if first == '0' then pure (sign.push first)
    else integerDigits (sign.push first)
  match ← peek? with
  | some character =>
    if isDigit character || character == '.' || character == 'e' || character == 'E' then
      fail "only JSON integer tokens are supported"
    else
      return .number token
  | none => return .number token

private def requiredDigits (accumulator : String) : Parser String := do
  let first ← any
  if !isDigit first then fail "expected JSON number digit"
  integerDigits (accumulator.push first)

private def captureInteger : Parser String := do
  let sign ← if (← peek!) == '-' then skip *> pure "-" else pure ""
  let first ← any
  if !isDigit first then fail "expected JSON number digit"
  if first == '0' then
    if (← peek?).any isDigit then fail "leading zero in JSON number"
    return sign.push first
  else
    integerDigits (sign.push first)

private def captureFraction (token : String) : Parser String := do
  if (← peek?) == some '.' then
    skip
    requiredDigits (token.push '.')
  else
    return token

private def captureExponent (token : String) : Parser String := do
  match ← peek? with
  | some marker =>
    if marker == 'e' || marker == 'E' then
      skip
      let exponentToken := token.push marker
      let signed ← match ← peek? with
        | some sign =>
          if sign == '+' || sign == '-' then skip *> pure (exponentToken.push sign)
          else pure exponentToken
        | none => pure exponentToken
      requiredDigits signed
    else
      return token
  | none => return token

private def captureNumber : Parser Raw := do
  let integer ← captureInteger
  let fraction ← captureFraction integer
  return .number (← captureExponent fraction)

mutual
  private partial def value (numberParser : Parser Raw) : Parser Raw := do
    let result ← match ← peek! with
      | '"' => Raw.string <$> stringValue
      | '[' => arrayValue numberParser
      | '{' => objectValue numberParser
      | 't' => skipString "true" *> pure (.bool true)
      | 'f' => skipString "false" *> pure (.bool false)
      | 'n' => skipString "null" *> pure .null
      | _ => numberParser
    ws
    return result

  private partial def arrayBody (numberParser : Parser Raw)
      (accumulator : List Raw) : Parser Raw := do
    let item ← value numberParser
    let delimiter ← any
    if delimiter == ']' then
      return .array (item :: accumulator).reverse
    else if delimiter == ',' then
      ws
      arrayBody numberParser (item :: accumulator)
    else
      fail "expected comma or closing JSON array bracket"

  private partial def arrayValue (numberParser : Parser Raw) : Parser Raw := do
    skipChar '['
    ws
    if (← peek!) == ']' then
      skip
      return .array []
    else
      arrayBody numberParser []

  private partial def objectBody (numberParser : Parser Raw)
      (accumulator : List (String × Raw))
      (keys : Std.HashSet String) : Parser Raw := do
    let key ← stringValue
    if keys.contains key then fail s!"duplicate JSON object key: {key}"
    ws
    skipChar ':'
    ws
    let item ← value numberParser
    let delimiter ← any
    if delimiter == '}' then
      return .object ((key, item) :: accumulator).reverse
    else if delimiter == ',' then
      ws
      objectBody numberParser ((key, item) :: accumulator) (keys.insert key)
    else
      fail "expected comma or closing JSON object brace"

  private partial def objectValue (numberParser : Parser Raw) : Parser Raw := do
    skipChar '{'
    ws
    if (← peek!) == '}' then
      skip
      return .object []
    else
      objectBody numberParser [] ∅
end

private def document (numberParser : Parser Raw) : Parser Raw := do
  ws
  let result ← value numberParser
  eof
  return result

end StrictJson

def parseStrictRawString (contents : String) : Except String Raw :=
  (StrictJson.document StrictJson.integerValue).run contents

def parseCaptureRawString (contents : String) : Except String Raw :=
  (StrictJson.document StrictJson.captureNumber).run contents

private def validateIntegerToken (token : String) : Except String Unit := do
  let _ ← (StrictJson.integerValue <* eof).run token
  return ()

private def validateCaptureToken (token : String) : Except String Unit := do
  let _ ← (StrictJson.captureNumber <* eof).run token
  return ()

mutual
  private def validateRaw (validateNumber : String → Except String Unit)
      (raw : Raw) : Except String Unit :=
    match raw with
    | .number token => validateNumber token
    | .array values => validateValues validateNumber values
    | .object fields => validateFields validateNumber fields ∅
    | _ => .ok ()

  private def validateValues (validateNumber : String → Except String Unit)
      (values : List Raw) : Except String Unit :=
    match values with
    | [] => .ok ()
    | item :: rest => do
      validateRaw validateNumber item
      validateValues validateNumber rest

  private def validateFields (validateNumber : String → Except String Unit)
      (fields : List (String × Raw))
      (keys : Std.HashSet String) : Except String Unit :=
    match fields with
    | [] => .ok ()
    | (key, item) :: rest => do
      if keys.contains key then throw s!"duplicate JSON object key: {key}"
      validateRaw validateNumber item
      validateFields validateNumber rest (keys.insert key)
end

def validateStrictRaw (raw : Raw) : Except String Unit :=
  validateRaw validateIntegerToken raw

def validateCaptureRaw (raw : Raw) : Except String Unit :=
  validateRaw validateCaptureToken raw

end LeanModels.Cpp
