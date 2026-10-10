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

mutual
  private partial def value : Parser Raw := do
    let result ← match ← peek! with
      | '"' => Raw.string <$> stringValue
      | '[' => arrayValue
      | '{' => objectValue
      | 't' => skipString "true" *> pure (.bool true)
      | 'f' => skipString "false" *> pure (.bool false)
      | 'n' => skipString "null" *> pure .null
      | _ => integerValue
    ws
    return result

  private partial def arrayBody (accumulator : List Raw) : Parser Raw := do
    let item ← value
    let delimiter ← any
    if delimiter == ']' then
      return .array (item :: accumulator).reverse
    else if delimiter == ',' then
      ws
      arrayBody (item :: accumulator)
    else
      fail "expected comma or closing JSON array bracket"

  private partial def arrayValue : Parser Raw := do
    skipChar '['
    ws
    if (← peek!) == ']' then
      skip
      return .array []
    else
      arrayBody []

  private partial def objectBody (accumulator : List (String × Raw))
      (keys : Std.HashSet String) : Parser Raw := do
    let key ← stringValue
    if keys.contains key then fail s!"duplicate JSON object key: {key}"
    ws
    skipChar ':'
    ws
    let item ← value
    let delimiter ← any
    if delimiter == '}' then
      return .object ((key, item) :: accumulator).reverse
    else if delimiter == ',' then
      ws
      objectBody ((key, item) :: accumulator) (keys.insert key)
    else
      fail "expected comma or closing JSON object brace"

  private partial def objectValue : Parser Raw := do
    skipChar '{'
    ws
    if (← peek!) == '}' then
      skip
      return .object []
    else
      objectBody [] ∅
end

private def document : Parser Raw := do
  ws
  let result ← value
  eof
  return result

end StrictJson

def parseStrictRawString (contents : String) : Except String Raw :=
  StrictJson.document.run contents

private def validateIntegerToken (token : String) : Except String Unit := do
  let _ ← (StrictJson.integerValue <* eof).run token
  return ()

mutual
  def validateStrictRaw (raw : Raw) : Except String Unit :=
    match raw with
    | .number token => validateIntegerToken token
    | .array values => validateStrictValues values
    | .object fields => validateStrictFields fields ∅
    | _ => .ok ()

  private def validateStrictValues (values : List Raw) : Except String Unit :=
    match values with
    | [] => .ok ()
    | item :: rest => do
      validateStrictRaw item
      validateStrictValues rest

  private def validateStrictFields (fields : List (String × Raw))
      (keys : Std.HashSet String) : Except String Unit :=
    match fields with
    | [] => .ok ()
    | (key, item) :: rest => do
      if keys.contains key then throw s!"duplicate JSON object key: {key}"
      validateStrictRaw item
      validateStrictFields rest (keys.insert key)
end

end LeanModels.Cpp
