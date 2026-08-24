import LeanModels.Go

/-!
# The slice rung's acceptance case: `runtime.itoa` on a MIDDLE slice

`docs/backlog/go.md` §G17 censused for a vendored function exercising
both slice ALIASING and the len/cap distinction, found that none small
enough exercises both, and concluded that **the discriminator can live in
the CALL**: the vendored function plus a chosen argument has the property
the function alone does not.

Vendored verbatim from `src/runtime/error.go` (Go 1.25.6), BSD-3-Clause,
"Copyright 2009 The Go Authors" (`docs/go-charter.md` §1.4):

    func itoa(buf []byte, val uint64) []byte {
        i := len(buf) - 1
        for val >= 10 {
            buf[i] = byte(val%10 + '0')
            i--
            val /= 10
        }
        buf[i] = byte(val + '0')
        return buf[i:]
    }

## The four rows, and what each one kills

Every expected value below was printed by the compiled function
(`go build && ./al2`), not derived here.

| row | a list-copy model |
| --- | --- |
| the RETURN value `"42"` | **PASSES** — this is the trap |
| the caller's array shows the writes | fails |
| a write through the returned view is visible in the original | fails |
| `out[:cap(out)]` reaches PAST the argument's end | **cannot be expressed** |

The last one is the point: a wrong model does not fail that row, it
cannot state it — a copy has no capacity beyond its own length.
-/

namespace Examples.go.itoa

open LeanModels LeanModels.Go

private def i64 (n : Int) : Expr := .lit (GoVal.mkInt IntKind.int64 n)
private def u64 (n : Int) : Expr := .lit (GoVal.mkInt IntKind.uint64 n)

/-- `itoa`, transcribed statement for statement. -/
def itoaBody : List Stmt :=
  [ .declare "i" (.binary .sub (.builtin1 "len" (.ident "buf")) (i64 1)),
    .forS none (some (.binary .ge (.ident "val") (u64 10))) none
      [ .assignIndex (.ident "buf") (.ident "i")
          (.convert "byte" (.binary .add (.binary .rem (.ident "val") (u64 10)) (u64 48))),
        .incDec "i" false,
        .assignOp .quo "val" (u64 10) ],
    .assignIndex (.ident "buf") (.ident "i")
      (.convert "byte" (.binary .add (.ident "val") (u64 48))),
    .ret [(.slice (.ident "buf") (some (.ident "i")) none)] ]

def prog : FuncTable := [("itoa", ["buf", "val"], itoaBody)]

private def byt (n : Nat) : GoVal := GoVal.mkInt IntKind.uint8 (n : Int)

/-- The caller's world: an 8-byte backing array of `'.'` at address 0. -/
def base0 : GoWorld :=
  { store := [(0, .arrayV (List.replicate 8 (byt 46)))], nextAddr := 1, locals := [] }

/-- `mid := base[2:6]` — len 4, cap 6. **This argument is the
discriminator**: cap reaches two past len. -/
def mid : GoVal := .sliceV 0 2 4 6

/-- Run `itoa(mid, val)` and hand back both the result and the world, so
the caller's array can be inspected — which is what the aliasing rows
require. -/
def runItoa (val : Nat) : Option (GoVal × GoWorld) :=
  match (callFunction prog 512 "itoa" [mid, GoVal.mkInt IntKind.uint64 (val : Int)]) base0 with
  | .ok (.ok v, w) => some (v, w)
  | _ => none

/-- The backing array's bytes, as the caller would see them. -/
def baseBytes (w : GoWorld) : Option (List Nat) :=
  match w.store.find? (fun p => p.1 == 0) with
  | some (_, GoVal.arrayV es) =>
      some (es.map (fun v => match v with | .intV _ n => n.toNat | _ => 0))
  | _ => none

/-! ## ROW 1 — the return value. A copy model PASSES this. -/

#guard (match runItoa 42 with
        | some (.sliceV _ off l c, _) => (off, l, c) == (4, 2, 4)
        | _ => false) == true

/-! ## ROW 2 — the CALLER's array shows the writes. A copy model fails. -/

#guard (match runItoa 42 with
        | some (_, w) => baseBytes w == some [46, 46, 46, 46, 52, 50, 46, 46]
        | _ => false) == true

/-! ## ROW 3 — ALIASING: a write through the returned view is visible in
the original. This is the decisive row. -/

#guard (match runItoa 42 with
        | some (out, w) =>
            match (execStmt prog 64
                    (.assignIndex (.lit out) (i64 0) (.lit (byt 88)))) w with
            | .ok (.ok _, w') => baseBytes w' == some [46, 46, 46, 46, 88, 50, 46, 46]
            | _ => false
        | _ => false) == true

/-! ## ROW 4 — `out[:cap(out)]` reaches PAST the argument's end.

A copy model cannot state this row at all: it has no capacity beyond its
length, so `out[:cap(out)]` is not a value it can produce. -/

#guard (match runItoa 42 with
        | some (out, w) =>
            match (evalExpr prog 64
                    (.slice (.lit out) none (some (.builtin1 "cap" (.lit out))))) w with
            | .ok (.ok (.sliceV _ off l c), _) => (off, l, c) == (4, 4, 4)
            | _ => false
        | _ => false) == true

/-! ## The argument itself — len and cap genuinely apart -/

#guard (match (evalExpr prog 8 (.builtin1 "len" (.lit mid))) base0 with
        | .ok (.ok (.intV _ n), _) => n == 4 | _ => false) == true
#guard (match (evalExpr prog 8 (.builtin1 "cap" (.lit mid))) base0 with
        | .ok (.ok (.intV _ n), _) => n == 6 | _ => false) == true

/-! ## Non-vacuity — the harness can fail -/

#guard (runItoa 42).isSome
#guard (match runItoa 42 with
        | some (_, w) => baseBytes w != some [46, 46, 46, 46, 46, 46, 46, 46]
        | _ => false) == true

/-! ## An out-of-range index PANICS — a defined outcome, never `undefined` -/

#guard (match (execStmt prog 64
                (.assignIndex (.lit mid) (i64 9) (.lit (byt 1)))) base0 with
        | .ok (.error p, _) =>
            match p.value with
            | .runtimeErrorV m => m == "runtime error: index out of range"
            | _ => false
        | _ => false) == true

end Examples.go.itoa
