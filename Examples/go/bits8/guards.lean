import Examples.go.bitlen.guards

/-!
# The rung-4 acceptance case: `math/bits.Len8` and `Reverse8`

`docs/backlog/go.md` §G14 censused this rung and found the premise wrong:
`math/bits`' tables are not arrays, they are **untyped string constants**,
and the functions that read them need **string indexing** plus a **type
conversion** — not arrays or slices. This file is that rung's acceptance
case, and the two functions are vendored verbatim:

    func Len8(x uint8) int       { return int(len8tab[x]) }
    func Reverse8(x uint8) uint8 { return rev8tab[x] }

from `src/math/bits/bits.go` (Go 1.25.6), BSD-3-Clause, "Copyright 2009
The Go Authors" — `docs/go-charter.md` §1.4's ruling on the in-tree
copies.

## Why `Reverse8` is here and not deferred

`Len8`'s table holds only values 0..8, so it would fit any string
representation. **`rev8tab` holds 128 bytes ≥ 0x80 of its 256**, and a
Lean `Char` at code point 200 is TWO bytes in UTF-8 — measured. So
`Reverse8` is the function that forces Go strings to be modelled as byte
sequences rather than as Lean `String`s, and taking it now is what stops
the value model from being rebuilt after this rung is built on.

## The two standards

`Len8` is checked against **`bitLenSpec`**, which §G13 PROVED brackets the
bit length. That is a genuinely independent standard: one side is a table
lookup, the other a proved recursive specification, and they were derived
by different routes. `Reverse8` has no proved spec, so its standard is
what `gc` printed.

Both are checked **exhaustively over all 256 inputs**, in one guard each —
a table function's whole domain is small enough that sampling would be a
choice to explain rather than a necessity.
-/

namespace Examples.go.bits8

open LeanModels LeanModels.Go Examples.go.bitlen

def len8tab : List UInt8 :=
  [0, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 
   5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 
   6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 
   6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 
   7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 
   7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 
   7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 
   7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8]
def rev8tab : List UInt8 :=
  [0, 128, 64, 192, 32, 160, 96, 224, 16, 144, 80, 208, 48, 176, 112, 240, 
   8, 136, 72, 200, 40, 168, 104, 232, 24, 152, 88, 216, 56, 184, 120, 248, 
   4, 132, 68, 196, 36, 164, 100, 228, 20, 148, 84, 212, 52, 180, 116, 244, 
   12, 140, 76, 204, 44, 172, 108, 236, 28, 156, 92, 220, 60, 188, 124, 252, 
   2, 130, 66, 194, 34, 162, 98, 226, 18, 146, 82, 210, 50, 178, 114, 242, 
   10, 138, 74, 202, 42, 170, 106, 234, 26, 154, 90, 218, 58, 186, 122, 250, 
   6, 134, 70, 198, 38, 166, 102, 230, 22, 150, 86, 214, 54, 182, 118, 246, 
   14, 142, 78, 206, 46, 174, 110, 238, 30, 158, 94, 222, 62, 190, 126, 254, 
   1, 129, 65, 193, 33, 161, 97, 225, 17, 145, 81, 209, 49, 177, 113, 241, 
   9, 137, 73, 201, 41, 169, 105, 233, 25, 153, 89, 217, 57, 185, 121, 249, 
   5, 133, 69, 197, 37, 165, 101, 229, 21, 149, 85, 213, 53, 181, 117, 245, 
   13, 141, 77, 205, 45, 173, 109, 237, 29, 157, 93, 221, 61, 189, 125, 253, 
   3, 131, 67, 195, 35, 163, 99, 227, 19, 147, 83, 211, 51, 179, 115, 243, 
   11, 139, 75, 203, 43, 171, 107, 235, 27, 155, 91, 219, 59, 187, 123, 251, 
   7, 135, 71, 199, 39, 167, 103, 231, 23, 151, 87, 215, 55, 183, 119, 247, 
   15, 143, 79, 207, 47, 175, 111, 239, 31, 159, 95, 223, 63, 191, 127, 255]
def len8expected : List UInt8 :=
  [0, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 
   5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 
   6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 
   6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 
   7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 
   7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 
   7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 
   7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 
   8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8]
def rev8expected : List UInt8 :=
  [0, 128, 64, 192, 32, 160, 96, 224, 16, 144, 80, 208, 48, 176, 112, 240, 
   8, 136, 72, 200, 40, 168, 104, 232, 24, 152, 88, 216, 56, 184, 120, 248, 
   4, 132, 68, 196, 36, 164, 100, 228, 20, 148, 84, 212, 52, 180, 116, 244, 
   12, 140, 76, 204, 44, 172, 108, 236, 28, 156, 92, 220, 60, 188, 124, 252, 
   2, 130, 66, 194, 34, 162, 98, 226, 18, 146, 82, 210, 50, 178, 114, 242, 
   10, 138, 74, 202, 42, 170, 106, 234, 26, 154, 90, 218, 58, 186, 122, 250, 
   6, 134, 70, 198, 38, 166, 102, 230, 22, 150, 86, 214, 54, 182, 118, 246, 
   14, 142, 78, 206, 46, 174, 110, 238, 30, 158, 94, 222, 62, 190, 126, 254, 
   1, 129, 65, 193, 33, 161, 97, 225, 17, 145, 81, 209, 49, 177, 113, 241, 
   9, 137, 73, 201, 41, 169, 105, 233, 25, 153, 89, 217, 57, 185, 121, 249, 
   5, 133, 69, 197, 37, 165, 101, 229, 21, 149, 85, 213, 53, 181, 117, 245, 
   13, 141, 77, 205, 45, 173, 109, 237, 29, 157, 93, 221, 61, 189, 125, 253, 
   3, 131, 67, 195, 35, 163, 99, 227, 19, 147, 83, 211, 51, 179, 115, 243, 
   11, 139, 75, 203, 43, 171, 107, 235, 27, 155, 91, 219, 59, 187, 123, 251, 
   7, 135, 71, 199, 39, 167, 103, 231, 23, 151, 87, 215, 55, 183, 119, 247, 
   15, 143, 79, 207, 47, 175, 111, 239, 31, 159, 95, 223, 63, 191, 127, 255]

/-- The two functions, transcribed. -/
def prog8 : FuncTable :=
  [ ("Len8", ["x"],
      -- `int(len8tab[x])` — a CONVERSION of a string INDEX, which is
      -- exactly the two constructs this rung added.
      [.ret [(.convert "int" (.index (.lit (.stringV len8tab)) (.ident "x")))]]),
    ("Reverse8", ["x"],
      [.ret [(.index (.lit (.stringV rev8tab)) (.ident "x"))]]) ]

/-- Run one of them on a concrete byte. -/
def run8 (name : String) (x : Nat) : Option Int :=
  match (callFunction prog8 64 name [GoVal.mkInt IntKind.uint8 (x : Int)]) ({} : GoWorld) with
  | .ok (.ok (.intV _ r), _) => some r
  | _ => none

/-! ## `Len8` against the PROVED specification, all 256 inputs -/

#guard (List.range 256).all (fun x => run8 "Len8" x == some ((bitLenSpec x : Nat) : Int))

/-! ## `Reverse8` against what `gc` printed, all 256 inputs -/

#guard (List.range 256).all
  (fun x => run8 "Reverse8" x == some ((rev8expected[x]!.toNat : Nat) : Int))

/-! ## The high bytes are the point

128 of `rev8tab`'s 256 entries are ≥ 0x80. These name three of them, so a
representation that lost the high bit would fail here and not only in the
sweep above. -/

#guard run8 "Reverse8" 1 == some 128
#guard run8 "Reverse8" 255 == some 255
#guard run8 "Reverse8" 129 == some 129

/-! ## Non-vacuity — the runner can fail -/

#guard (run8 "Len8" 0).isSome
#guard (run8 "NotAFunction" 0).isNone
#guard (run8 "Len8" 300).isSome   -- wraps into uint8 first, per the type

end Examples.go.bits8
