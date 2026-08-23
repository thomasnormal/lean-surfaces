import LeanModels.Go

/-!
# The fixed-array rung: `runtime.printuint`, and the pair a header model
  cannot pass

## The value model, and why it needed NO new constructor

A `[N]T` is a VALUE: assignment, argument passing and return all COPY it,
where a slice aliases. That is the semantic difference this rung is
about, and the obvious way to get it wrong is to reuse `sliceV` — a
header — for arrays, at which point `b := a` aliases and Go says it must
not.

The model did not need a new constructor, because `bindLocal` already
stores a local's value AT ITS OWN ADDRESS. Two consequences fall out:

* `b := a` evaluates `a` to an `arrayV` VALUE and binds it at a FRESH
  address — a deep copy, for free, with no copy code to get wrong;
* `a[:]` needs the ADDRESS the array lives at, which is precisely Go's
  rule that only an ADDRESSABLE array may be sliced.

So addressability is not a special case bolted on; it is how the arm is
written (`docs/backlog/go.md` §G20). An array reached by value rather
than by name is refused, which is also what `gc` does.

## Vendored, verbatim (Go 1.25.6, BSD-3-Clause, "Copyright 2009 The Go
Authors", `docs/go-charter.md` §1.4) — `src/runtime/print.go`:

    func printuint(v uint64) {
        var buf [100]byte
        i := len(buf)
        for i--; i > 0; i-- {
            buf[i] = byte(v%10 + '0')
            if v < 10 {
                break
            }
            v /= 10
        }
        gwrite(buf[i:])
    }

`gwrite` is the one thing not modelled, so the transcription RETURNS
`buf[i:]` instead of writing it. Nothing else is changed: the array, the
`len(buf)` seed, the decrementing three-clause loop, the indexed write
and the slice-of-array are all as vendored. It is the direct sibling of
§G18's `runtime.itoa`, which is why the walker needed only `[N]T` itself
to reach it.

`printuint` makes the FIXED SIZE load-bearing in a way a buffer usually
does not: `i` is seeded from `len(buf)`, so `N` decides where the digits
land, and the returned slice's `cap` is `N - i`.

## The discriminating pair

`printuint` alone cannot separate a value model from a header model —
its array never escapes and is never copied. So, per §G17's ratified
precedent, the discriminator lives in a CALL, and it is one array with
two operations:

    var a [4]byte ; a = "wxyz"
    b := a        // COPY
    s := a[:]     // ALIAS
    b[0] = 'B'    // must NOT reach a
    s[1] = 'S'    // MUST reach a

| model | `a` afterwards |
| --- | --- |
| `gc` | `"wSyz"` |
| arrays-are-headers | `"BSyz"` — the copy leaked |
| slices-are-copies | `"wxyz"` — the alias did not land |

Both wrong models fail, in OPPOSITE directions, on the same row. That is
the property `Reverse8` had in §G15.

Every expected value below was printed by the compiled program, never
typed here:

    $ cd <scratch>/fagen && go build -o fagen main.go && ./fagen
    ⟨0, [48], 1, 1⟩, ⟨7, [55], 1, 1⟩, ⟨42, [52, 50], 2, 2⟩,
    ⟨100, [49, 48, 48], 3, 3⟩, ⟨9999, [57, 57, 57, 57], 4, 4⟩
    a := [119, 83, 121, 122]   -- "wSyz"
    b := [66, 120, 121, 122]   -- "Bxyz"
    len(a)=4 cap(a[:])=4 ; a[1:3] len=2 cap=3

with `go version go1.25.6 darwin/arm64`.
-/

namespace Examples.go.fixedarray

open LeanModels LeanModels.Go

private def i64 (n : Int) : Expr := .lit (GoVal.mkInt IntKind.int64 n)
private def u64 (n : Int) : Expr := .lit (GoVal.mkInt IntKind.uint64 n)
private def byt (n : Int) : GoVal := GoVal.mkInt IntKind.uint8 n

/-! ## `printuint`, transcribed statement for statement -/

def printuintBody : List Stmt :=
  [ .declare "buf" (.arrayLit 100 (.lit (byt 0))),
    .declare "i" (.builtin1 "len" (.ident "buf")),
    .forS (some (.incDec "i" false))
          (some (.binary .gt (.ident "i") (i64 0)))
          (some (.incDec "i" false))
      [ .assignIndex (.ident "buf") (.ident "i")
          (.convert "byte" (.binary .add (.binary .rem (.ident "v") (u64 10)) (u64 48))),
        .ifS (.binary .lt (.ident "v") (u64 10)) [ .branch .break_ none ] [],
        .assignOp .quo "v" (u64 10) ],
    .ret (some (.slice (.ident "buf") (some (.ident "i")) none)) ]

def prog : FuncTable := [("printuint", ⟨["v"], printuintBody⟩)]

private def emptyW : GoWorld := { store := [], nextAddr := 0, locals := [] }

private def runPU (v : Int) : Option (List Int × Nat × Nat) :=
  match (callFunction prog 4096 "printuint" [GoVal.mkInt IntKind.uint64 v]) emptyW with
  | .ok (.ok (.sliceV b off l c), w) =>
      match w.store.find? (fun p => p.1 == b) with
      | some (_, .arrayV es) =>
          some ((List.range l).filterMap (fun k =>
                  match es[off + k]? with
                  | some (.intV _ n) => some n
                  | _ => none), l, c)
      | _ => none
  | _ => none

/-! ## ROWS 1-5 — `printuint` against `gc`, contents AND len AND cap.

`cap` is `N - i`, so these rows read the fixed size 100 through the
returned header. -/

#guard runPU 0    == some ([48], 1, 1)
#guard runPU 7    == some ([55], 1, 1)
#guard runPU 42   == some ([52, 50], 2, 2)
#guard runPU 100  == some ([49, 48, 48], 3, 3)
#guard runPU 9999 == some ([57, 57, 57, 57], 4, 4)

/-! ## THE DISCRIMINATING PAIR — copy and alias on ONE array -/

def pairBody : List Stmt :=
  [ .declare "a" (.arrayLit 4 (.lit (byt 0))),
    .assignIndex (.ident "a") (i64 0) (.lit (byt 119)),   -- 'w'
    .assignIndex (.ident "a") (i64 1) (.lit (byt 120)),   -- 'x'
    .assignIndex (.ident "a") (i64 2) (.lit (byt 121)),   -- 'y'
    .assignIndex (.ident "a") (i64 3) (.lit (byt 122)),   -- 'z'
    .declare "b" (.ident "a"),                            -- COPY
    .declare "s" (.slice (.ident "a") none none),         -- ALIAS
    .assignIndex (.ident "b") (i64 0) (.lit (byt 66)),    -- 'B'
    .assignIndex (.ident "s") (i64 1) (.lit (byt 83)) ]   -- 'S'

private def readArr (name : String) (w : GoWorld) : Option (List Int) :=
  match w.locals.find? (fun p => p.1 == name) with
  | some (_, a) =>
      match w.store.find? (fun p => p.1 == a) with
      | some (_, .arrayV es) =>
          some (es.map (fun v => match v with | .intV _ n => n | _ => -1))
      | _ => none
  | _ => none

private def pairW : Option GoWorld :=
  match (execSeq prog 512 pairBody) emptyW with
  | .ok (.ok _, w) => some w
  | _ => none

/-! `a` = "wSyz" — the ALIAS write landed and the COPY write did not.
An arrays-are-headers model gives "BSyz"; a slices-are-copies model gives
"wxyz". Both wrong models fail this one row, in opposite directions. -/

#guard (match pairW with
        | some w => readArr "a" w == some [119, 83, 121, 122]
        | none => false) == true

/-! `b` = "Bxyz" — the copy moved alone, and kept the ORIGINAL 'x' at
index 1 that the alias write later changed in `a`. -/

#guard (match pairW with
        | some w => readArr "b" w == some [66, 120, 121, 122]
        | none => false) == true

/-! ## `len` and `cap` of an array, and of a slice cut from its middle.

`a[1:3]` has len 2 and **cap 3**: capacity runs to the ARRAY's end, so
this row reads `N` through the header. A model that lost the size gives
cap 2. -/

#guard (match (evalExpr prog 64 (.builtin1 "len" (.ident "a"))) (pairW.getD emptyW) with
        | .ok (.ok (.intV _ n), _) => n == 4 | _ => false) == true
#guard (match (evalExpr prog 64 (.slice (.ident "a") (some (i64 1)) (some (i64 3))))
               (pairW.getD emptyW) with
        | .ok (.ok (.sliceV _ off l c), _) => (off, l, c) == (1, 2, 3)
        | _ => false) == true

/-! ## Non-vacuity — these assert NEGATIVES, so a harness that checked
nothing would fail them. -/

#guard (runPU 42).isSome
#guard (pairW.isSome)
#guard (match pairW with
        | some w =>
            -- NOT the header answer, and NOT the copy-everything answer
            readArr "a" w != some [66, 83, 121, 122]
              && readArr "a" w != some [119, 120, 121, 122]
              && readArr "a" w != readArr "b" w
        | none => false) == true

/-! ## An out-of-range write into an ARRAY panics — defined, never
`undefined`. -/

#guard (match (execStmt prog 64 (.assignIndex (.ident "a") (i64 9) (.lit (byt 1))))
               (pairW.getD emptyW) with
        | .ok (.error p, _) =>
            match p.value with
            | .runtimeErrorV m => m == "runtime error: index out of range"
            | _ => false
        | _ => false) == true

end Examples.go.fixedarray
