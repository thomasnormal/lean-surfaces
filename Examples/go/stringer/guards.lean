import LeanModels.Go

/-!
# The §G28 bundle: the generated `stringer` method, end to end

§G27 censused `strconv` and found its reach is **+0 alone**: all 26 files
are `go:generate stringer` output, and every one needs a **method**, a
**string concatenation** and `strconv.FormatInt` together. Building it
turned up a FOURTH member the census missed — **slicing a string** — for
the same reason the other three were missed: one `go/ast` node covering
two operations the walker prices differently. `SliceExpr` is that node
for the fourth time, after `ArrayType` (§G20), `SelectorExpr` (§G21) and
`FuncDecl` (§G27).

Vendored verbatim — the shape `stringer` emits, here as
`go/constant/kind_string.go` writes it:

    func (i Kind) String() string {
        if i < 0 || i >= Kind(len(_Kind_index)-1) {
            return "Kind(" + strconv.FormatInt(int64(i), 10) + ")"
        }
        return _Kind_name[_Kind_index[i]:_Kind_index[i+1]]
    }

## The method is the EXTRACTOR's problem, not the walker's

`FuncTable` maps a plain name to a body and has nowhere for a receiver.
Rather than widen it, the extractor mangles a method to `Type.Method`
with the receiver as its first parameter — §G22's division of labour
again, and it is gated by `census.sh --resolve` (pointer and value
receivers key the same; generics key on the bare type).

That models the DECLARATION. Calling one needs `x.M()` dispatch, a value
selector, which is still rung E3 — and these files only declare.

## What each row separates

| row | what a wrong model does |
| --- | --- |
| `Kind(0)` = `"bool"` | slices the table wrong, or cannot slice a string at all |
| `Kind(3)` = `"Kind(3)"` | takes the in-range branch and returns a table entry |
| `Kind(-1)` = `"Kind(-1)"` | drops the sign, giving `"Kind(1)"` |
| `FormatInt(MinInt64)` | overflows negating it — Go's own `int64` would |

Every expected value was printed by the compiled program and pasted, never
typed (§G13):

    $ cd <scratch>/g28 && go build -o g28r rows.go && ./g28r

with `go version go1.25.6 darwin/arm64`.
-/

namespace Examples.go.stringer

open LeanModels LeanModels.Go

private def i64 (n : Int) : Expr := .lit (GoVal.mkInt IntKind.int64 n)
private def byt (n : Int) : GoVal := GoVal.mkInt IntKind.uint8 n
private def str (s : String) : GoVal := GoVal.ofString s

/-! ## `Kind.String`, transcribed — the extractor's mangled name, with the
receiver `i` as the first parameter. -/

def kindStringBody : List Stmt :=
  [ .ifS (.binary .lor
            (.binary .lt (.ident "i") (i64 0))
            (.binary .ge (.ident "i")
              (.binary .sub (.builtin1 "len" (.ident "_Kind_index")) (i64 1))))
      [ .ret [ .binary .add
                 (.binary .add (.lit (str "Kind("))
                   (.callPkg "strconv" "FormatInt"
                     [.convert "int64" (.ident "i"), i64 10]))
                 (.lit (str ")")) ] ]
      [],
    .ret [ .slice (.ident "_Kind_name")
             (some (.index (.ident "_Kind_index") (.ident "i")))
             (some (.index (.ident "_Kind_index")
                     (.binary .add (.ident "i") (i64 1)))) ] ]

def prog : FuncTable := [("Kind.String", ⟨["i"], false, kindStringBody⟩)]

/-- the package-level table the generated file declares -/
def tableW : GoWorld :=
  { store := [ (0, str "boolstringint")
             , (1, .arrayV [byt 0, byt 4, byt 10, byt 13]) ],
    nextAddr := 2,
    locals := [("_Kind_name", 0), ("_Kind_index", 1)] }

private def runKind (k : Int) : Option (List Nat) :=
  match (evalExpr prog 512 (.call "Kind.String" [i64 k])) tableW with
  | .ok (.ok (.stringV bs), _) => some (bs.map UInt8.toNat)
  | _ => none

private def fmtInt (n : Int) : Option (List Nat) :=
  match pkgCall "strconv" "FormatInt"
          [GoVal.mkInt IntKind.int64 n, GoVal.mkInt IntKind.int64 10] with
  | .values [.stringV bs] => some (bs.map UInt8.toNat)
  | _ => none

/-! ## The in-range branch — a STRING SLICE of the table -/

#guard runKind (0) == some [98, 111, 111, 108]                     -- "bool"
#guard runKind (1) == some [115, 116, 114, 105, 110, 103]           -- "string"
#guard runKind (2) == some [105, 110, 116]                          -- "int"

/-! ## The out-of-range branch — CONCATENATION around `FormatInt` -/

#guard runKind (3) == some [75, 105, 110, 100, 40, 51, 41]          -- "Kind(3)"
#guard runKind (7) == some [75, 105, 110, 100, 40, 55, 41]          -- "Kind(7)"
#guard runKind (-1) == some [75, 105, 110, 100, 40, 45, 49, 41]     -- "Kind(-1)"

/-! ## `FormatInt` alone, including the negation trap.

`MinInt64` has no positive counterpart in `int64`, so Go's own
implementation special-cases it. Lean's `Int` is unbounded, so the model
gets it without a guard — but the row is here because a model that
mirrored Go's `int64` arithmetic would overflow exactly here. -/

#guard fmtInt 0 == some [48]
#guard fmtInt 7 == some [55]
#guard fmtInt (-1) == some [45, 49]
#guard fmtInt (-42) == some [45, 52, 50]
#guard fmtInt 9223372036854775807
        == some [57, 50, 50, 51, 51, 55, 50, 48, 51, 54, 56, 53, 52, 55, 55, 53, 56, 48, 55]
#guard fmtInt (-9223372036854775808)
        == some [45, 57, 50, 50, 51, 51, 55, 50, 48, 51, 54, 56, 53, 52, 55, 55, 53, 56, 48, 56]

/-! ## String concatenation is BYTE concatenation, high bytes included.

§G15 made a Go string a `List UInt8` so `rev8tab` could be represented.
The payoff shows up here: `"\xff\xfe" + "!"` keeps 255 and 254, where a
`String`-based model would have re-encoded them as two bytes each. -/

#guard (match (evalExpr prog 64
                (.binary .add (.lit (.stringV [255, 254])) (.lit (.stringV [33]))))
               tableW with
        | .ok (.ok (.stringV bs), _) => bs.map UInt8.toNat == [255, 254, 33]
        | _ => false) == true

/-! ## Slicing a string yields a STRING, not a header. -/

#guard (match (evalExpr prog 64
                (.slice (.ident "_Kind_name") (some (i64 4)) (some (i64 10)))) tableW with
        | .ok (.ok (.stringV bs), _) => bs.map UInt8.toNat == [115, 116, 114, 105, 110, 103]
        | _ => false) == true

/-! ...and an out-of-range string slice PANICS — defined, never
`undefined`. -/

#guard (match (evalExpr prog 64
                (.slice (.ident "_Kind_name") (some (i64 4)) (some (i64 99)))) tableW with
        | .ok (.error p, _) =>
            match p.value with
            | .runtimeErrorV m => m == "runtime error: slice bounds out of range"
            | _ => false
        | _ => false) == true

/-! ## Non-vacuity — these assert NEGATIVES. -/

#guard (runKind 0).isSome
#guard (runKind 3 != runKind 2)                       -- the branch MATTERS
#guard (runKind (-1) != some [75, 105, 110, 100, 40, 49, 41])   -- NOT "Kind(1)": the sign survives
#guard (fmtInt (-42) != some [52, 50])                -- NOT "42"

end Examples.go.stringer
