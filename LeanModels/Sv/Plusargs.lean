import LeanModels.Sv.FormattedInput

/-! Immutable command-line input, IEEE 1800-2023 §21.6.
Inputs are ordered plusarg contents, with the command-line `+` removed.
The host supplies this list explicitly; no ambient process arguments are read.
Only complete integral conversions are admitted. Malformed values remain loud
because their diagnostic observations are outside this tier. -/

namespace LeanModels.Sv.Plusargs

set_option autoImplicit false

open FormattedInput

structure Format where
  pattern : String
  code : Char
  deriving Repr, BEq

def ascii (text : String) : Bool :=
  text.toList.all fun c => c.toNat > 0 && c.toNat < 128

def parse (text : String) : Except String Format := do
  unless ascii text do throw "Plusargs: non-ASCII or NUL format"
  let (pattern, rest) := text.toList.span (· != '%')
  let '%' :: rest := rest | throw "Plusargs: missing integral conversion"
  let rest := match rest with | '0' :: tail => tail | tail => tail
  let [code] := rest | throw "Plusargs: expected one final integral conversion"
  unless ['b', 'o', 'd', 'h', 'x'].contains code.toLower do
    throw "Plusargs: unsupported conversion"
  return ⟨String.ofList pattern, code.toLower⟩

/-- Matching is case-sensitive and preserves command-line order. -/
def first (inputs : List String) (pattern : String) : Option String :=
  inputs.find? (fun input => pattern.toList.isPrefixOf input.toList)

def test (inputs : List String) (pattern : String) : Bool :=
  (first inputs pattern).isSome

/-- Convert the entire suffix, rather than a scanner's numeric pattern. -/
def integral (width : Nat) (code : Char) (text : String) : Except String LVec := do
  unless ['b', 'o', 'd', 'h', 'x'].contains code do
    throw "Plusargs: unsupported integral conversion"
  unless ascii text do throw "Plusargs: non-ASCII or NUL value"
  let characters := text.toList
  if characters.isEmpty then throw "Plusargs: empty numeric value requires diagnostics"
  if code == 'd' then
    let (negative, digits) := match characters with
      | '-' :: rest => (true, rest)
      | '+' :: rest => (false, rest)
      | rest => (false, rest)
    -- Decimal x/z spellings and whitespace are separate conversion corners.
    unless !digits.isEmpty && digits.any decimalDigit &&
        digits.all (fun c => decimalDigit c || c == '_') do
      throw "Plusargs: malformed or unsupported decimal value requires diagnostics"
    let number := (digits.filter decimalDigit).foldl
      (fun n c => n * 10 + c.toNat - '0'.toNat) 0
    return signedValue width negative number
  let group := if code == 'b' then 1 else if code == 'o' then 3 else 4
  unless characters.any (· != '_') && characters.all (numericCharacter (2 ^ group)) do
    throw "Plusargs: malformed based value requires diagnostics"
  if characters.contains '?' ||
      (group != 1 && characters.any (fun c => (unknown c).isSome)) then
    throw "Plusargs: unknown octal/hex digits or question mark require diagnostics"
  if (unknown ((characters.filter (· != '_')).headD '_')).isSome then
    throw "Plusargs: leading unknown based digit requires diagnostics"
  return basedValue width group (characters.filter (· != '_'))

/-- A missing match performs no conversion and requires no destination write. -/
def value (inputs : List String) (format : Format) (width : Nat) :
    Except String (Option LVec) := do
  match first inputs format.pattern with
  | none => return none
  | some input =>
      return some (← integral width format.code
        (String.ofList (input.toList.drop format.pattern.length)))

/-- Appending later inputs cannot change an already selected first match. -/
theorem first_cons_hit (input : String) (rest : List String) (pattern : String)
    (hit : pattern.toList.isPrefixOf input.toList = true) :
    first (input :: rest) pattern = some input := by
  simp [first, List.find?, hit]

/-- Absence cannot fabricate a destination value, for any destination width. -/
theorem value_absent (inputs : List String) (format : Format) (width : Nat)
    (absent : first inputs format.pattern = none) :
    value inputs format width = .ok none := by
  unfold value
  rw [absent]
  rfl

end LeanModels.Sv.Plusargs
