/-!
# Exact source numeric literals

SPICE and Verilog-A frontends share exact decimal/scientific/engineering
literal parsing. Decimal source text is converted directly to `Rat`; no
floating-point value enters elaboration.
-/

namespace LeanModels.Circuit.ExactLiteral

private def pow10 : Nat → Nat
  | 0 => 1
  | n + 1 => 10 * pow10 n

private def parseUnsignedDecimal (text : String) : Option Rat := do
  match text.splitOn "." with
  | [whole] =>
      let value ← whole.toNat?
      pure value
  | [whole, fractional] =>
      let wholeValue ← if whole.isEmpty then some 0 else whole.toNat?
      let fractionalValue ←
        if fractional.isEmpty then some 0 else fractional.toNat?
      let denominator := pow10 fractional.length
      pure ((wholeValue * denominator + fractionalValue : Nat) / denominator)
  | _ => none

private def parseDecimal (text : String) : Option Rat :=
  match text.toList with
  | '-' :: rest => (parseUnsignedDecimal (String.ofList rest)).map (-·)
  | '+' :: rest => parseUnsignedDecimal (String.ofList rest)
  | _ => parseUnsignedDecimal text

private def parseScientific (text : String) : Option Rat := do
  match text.toLower.splitOn "e" with
  | [mantissa] => parseDecimal mantissa
  | [mantissa, exponent] =>
      let base ← parseDecimal mantissa
      let exponent ← exponent.toInt?
      if exponent < 0 then
        pure (base / pow10 (-exponent).toNat)
      else
        pure (base * pow10 exponent.toNat)
  | _ => none

private def suffixMultiplier (suffix : String) : Option Rat :=
  match suffix with
    | "" | "v" | "a" | "ohm" | "h" => some 1
    | "k" | "kohm" => some 1000
    | "meg" | "megohm" => some 1000000
    | "m" => some (1 / 1000)
    | "u" => some (1 / 1000000)
    | "n" => some (1 / 1000000000)
    | "p" => some (1 / 1000000000000)
    | "f" | "fem" => some (1 / 1000000000000000)
    | _ => none

private def parseAt (chars : List Char) : Nat → Option Rat
  | 0 => none
  | cut + 1 =>
      let numeric := String.ofList (chars.take (cut + 1))
      let suffix := String.ofList (chars.drop (cut + 1))
      match parseScientific numeric, suffixMultiplier suffix with
      | some base, some multiplier => some (base * multiplier)
      | _, _ => parseAt chars cut

def parse (token : String) : Option Rat :=
  let chars := token.toLower.toList
  parseAt chars chars.length

#guard parse "1.5" == some (3 / 2)
#guard parse "2.5e-3" == some (1 / 400)
#guard parse "470u" == some (47 / 100000)

end LeanModels.Circuit.ExactLiteral
