import LeanModels.Sv.Basic

/-! Pure integral formatted input, IEEE 1800-2023 §21.3.4.3.
The caller supplies captured destination widths and performs copyback.
Unsupported diagnostics are errors here, never invented output text. -/

namespace LeanModels.Sv.FormattedInput

inductive Token where
  | whitespace
  | literal (character : Char)
  | conversion (suppressed : Bool) (limit : Option Nat) (code : Char)
deriving Repr, BEq, Inhabited

def space (character : Char) : Bool :=
  character == '\x00' || character == ' ' || character == '\t' ||
  character == '\n' || character == '\r' || character == '\x0b' || character == '\x0c'

def decimalDigit (character : Char) : Bool := '0' ≤ character && character ≤ '9'

def parseSpec (characters : List Char) : Except String (Token × List Char) := do
  let (suppressed, characters) := match characters with
    | '*' :: rest => (true, rest)
    | rest => (false, rest)
  let (digits, remaining) := characters.span decimalDigit
  let width := digits.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0
  if !digits.isEmpty && width == 0 then throw "Scanf: zero field width"
  let code :: rest := remaining | throw "Scanf: incomplete conversion"
  let code := code.toLower
  if !(['b', 'o', 'h', 'x', 'd', 's', 'c', 'v'].contains code) then
    throw "Scanf: unsupported conversion"
  return (.conversion suppressed (if digits.isEmpty then none else some width) code, rest)

def parseAux (fuel : Nat) (characters : List Char) : Except String (List Token) := do
  match fuel, characters with
  | _, [] => return []
  | 0, _ => throw "Scanf: format parser exhausted fuel"
  | fuel + 1, '%' :: '%' :: rest =>
      return .literal '%' :: (← parseAux fuel rest)
  | fuel + 1, '%' :: rest =>
      let (conversion, remaining) ← parseSpec rest
      return conversion :: (← parseAux fuel remaining)
  | fuel + 1, character :: rest =>
      if character == '\x00' then throw "Scanf: embedded NUL in format"
      if character.toNat > 127 then throw "Scanf: non-ASCII format"
      return (if space character then .whitespace else .literal character) ::
        (← parseAux fuel rest)

def parse (format : String) : Except String (List Token) :=
  parseAux (format.length + 1) format.toList

def destinations (format : List Token) : Nat :=
  format.foldl (fun n token => match token with
    | .conversion false _ _ => n + 1
    | _ => n) 0

def packedCharacters (value : LVec) : Except String (List Char) := do
  let some number := value.toNat? | throw "Scanf: unknown packed input requires diagnostics"
  let bytes := ((List.range ((value.width + 7) / 8)).reverse.map fun index =>
    Char.ofNat ((number / 2 ^ (8 * index)) % 256))
  return bytes.map fun character => if character == '\x00' then ' ' else character

def digit (base : Nat) (character : Char) : Option Nat :=
  let code := character.toLower.toNat
  let value := if code ≥ 'a'.toNat then code - 'a'.toNat + 10 else code - '0'.toNat
  if (decimalDigit character || ('a' ≤ character.toLower && character.toLower ≤ 'f')) &&
      value < base then some value else none

def unknown (character : Char) : Option Logic :=
  if character.toLower == 'x' then some .lx
  else if character.toLower == 'z' || character == '?' then some .lz
  else none

def numericCharacter (base : Nat) (character : Char) : Bool :=
  character == '_' || (digit base character).isSome || (unknown character).isSome

def signedValue (width : Nat) (negative : Bool) (number : Nat) : LVec :=
  .ofNat width (if negative then (2 ^ width - number % 2 ^ width) % 2 ^ width else number)

def basedValue (width group : Nat) (characters : List Char) : LVec :=
  let parts := characters.map fun character => match unknown character with
    | some bit => LVec.replicate group bit
    | none => LVec.ofNat group ((digit (2 ^ group) character).getD 0)
  let value := LVec.concatMany parts.toArray
  let fill := match characters.head? with
    | some character => (unknown character).getD .l0
    | none => .l0
  ⟨Array.ofFn (n := width) fun index => value.bits[index.val]?.getD fill⟩

def bytesValue (width : Nat) (characters : List Char) : LVec :=
  .ofNat width (characters.foldl (fun value character => value * 256 + character.toNat) 0)

/-- Separators do not consume the field width of a based conversion. -/
def basedField (remaining : Nat) : List Char → List Char
  | [] => []
  | character :: rest =>
      if remaining == 0 then []
      else character :: basedField (if character == '_' then remaining else remaining - 1) rest

/-- A matched conversion, its value, and the unconsumed input. -/
def convert (width : Nat) (limit : Option Nat) (code : Char) (input : List Char) :
    Except String (Option (LVec × List Char)) := do
  let input := if code == 'c' then input else input.dropWhile space
  let field := input.take (limit.getD (if code == 'c' then 1 else input.length))
  if field.isEmpty then return none
  if code == 'c' || code == 's' then
    let characters := if code == 's' then field.takeWhile (fun c => !space c) else field
    if characters.isEmpty then return none
    return some (bytesValue width characters, input.drop characters.length)
  if code == 'v' then
    -- Strength input always consumes three characters, independently of width.
    let _ :: _ :: scalar :: _ := input | return none
    let value ← match scalar.toLower with
      | '0' => pure (LVec.ofNat width 0)
      | '1' => pure (LVec.ofNat width 1)
      | 'x' => pure ⟨Array.ofFn (n := width) fun i => if i.val == 0 then .lx else .l0⟩
      | 'z' => pure ⟨Array.ofFn (n := width) fun i => if i.val == 0 then .lz else .l0⟩
      | _ => throw "Scanf: invalid strength scalar requires diagnostics"
    return some (value, input.drop 3)
  if code == 'd' then
    -- A leading sign is consumed separately from the numeric field width.
    let field := match input with
      | '+' :: _ | '-' :: _ => input.take (limit.getD input.length + 1)
      | _ => field
    match field with
    | character :: _ =>
      if let some bit := unknown character then
        return some (⟨Array.ofFn (n := width) fun i => if i.val == 0 then bit else .l0⟩,
                     input.drop 1)
      let (negative, sign, rest) := match field with
        | '-' :: rest => (true, 1, rest)
        | '+' :: rest => (false, 1, rest)
        | rest => (false, 0, rest)
      let characters := rest.takeWhile (fun c => decimalDigit c || c == '_')
      let digits := characters.filter decimalDigit
      if digits.isEmpty then return none
      let number := digits.foldl (fun n c => n * 10 + c.toNat - '0'.toNat) 0
      return some (signedValue width negative number, input.drop (sign + characters.length))
    | [] => return none
  let group := if code == 'b' then 1 else if code == 'o' then 3 else 4
  let field := basedField (limit.getD input.length) input
  let characters := field.takeWhile (numericCharacter (2 ^ group))
  let digits := characters.filter (· != '_')
  if digits.isEmpty then return none
  return some (basedValue width group digits, input.drop characters.length)

def walk : List Token → List Nat → List Char → Nat → List LVec →
    Except String (Nat × List LVec)
  | [], _, _, count, values => .ok (count, values)
  | .whitespace :: rest, widths, input, count, values =>
      walk rest widths (input.dropWhile space) count values
  | .literal expected :: rest, widths, input, count, values => do
      let actual :: remaining := input | throw "Scanf: literal mismatch requires diagnostics"
      if actual != expected then throw "Scanf: literal mismatch requires diagnostics"
      walk rest widths remaining count values
  | .conversion suppressed limit code :: rest, widths, input, count, values => do
      let width ← if suppressed then pure 1 else match widths with
        | width :: _ => pure width
        | [] => throw "Scanf: missing output requires diagnostics"
      match ← convert width limit code input with
      | none => return (count, values)
      | some (value, remaining) =>
          if suppressed then walk rest widths remaining count values
          else walk rest widths.tail remaining (count + 1) (values ++ [value])

def scan (input : LVec) (format : List Token) (widths : List Nat) :
    Except String (Nat × List LVec) := do
  if destinations format != widths.length then
    throw "Scanf: output arity requires diagnostics"
  walk format widths (← packedCharacters input) 0 []

end LeanModels.Sv.FormattedInput
