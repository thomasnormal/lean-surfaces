import LeanModels.Go

/-!
# The variadic rung: packing allocates, spreading does not

`docs/backlog/go.md` §G25's census priced this rung at **+52 files** and
`fmt` — the package that motivated looking at variadics at all — at **+3
on top**. Variadics are worth seventeen times what `fmt` adds, and `fmt`
cannot come first: every one of its entry points is variadic.

## The acceptance is (function, argument) in its purest form so far

ONE callee, TWO call forms, and they disagree about aliasing. Measured
against `gc` with a callee that writes `xs[0] = 'Z'`:

| call | the CALLER's slice afterwards |
| --- | --- |
| `clobber(s...)` | **`"Zbc"`** — the callee aliased it |
| `clobber(a, b, c)` | **`"abc"`** — packing gave it a fresh array |

The function is identical; only the call form differs. A model with one
code path for both gets one of these rows wrong whichever way it
chooses — it cannot pass both, which is the property §G20's array rows
had and the reason this pair is the acceptance.

`clobber()` returns **0**, not an error: a variadic parameter with no
arguments is a slice of length zero, and it always exists.

Every expected value was printed by the compiled program, never typed:

    $ cd <scratch>/vgen && go build -o vgen main.go && ./vgen

with `go version go1.25.6 darwin/arm64`.
-/

namespace Examples.go.variadic

open LeanModels LeanModels.Go

private def i64 (n : Int) : Expr := .lit (GoVal.mkInt IntKind.int64 n)
private def byt (n : Int) : GoVal := GoVal.mkInt IntKind.uint8 n

/-! ## The two callees -/

/-- `func clobber(xs ...byte) int { if len(xs) > 0 { xs[0] = 'Z' }; return len(xs) }` -/
def clobberBody : List Stmt :=
  [ .ifS (.binary .gt (.builtin1 "len" (.ident "xs")) (i64 0))
      [ .assignIndex (.ident "xs") (i64 0) (.lit (byt 90)) ] [],
    .ret [.builtin1 "len" (.ident "xs")] ]

/-- `func sum(base int, xs ...int) int` — fixed AND variadic parameters. -/
def sumBody : List Stmt :=
  [ .declare "t" (.ident "base"),
    .rangeS none (some "x") (.ident "xs") [ .assignOp .add "t" (.ident "x") ],
    .ret [.ident "t"] ]

def prog : FuncTable :=
  [ ("clobber", ⟨["xs"], true, clobberBody⟩),
    ("sum",     ⟨["base", "xs"], true, sumBody⟩),
    ("fixed",   ⟨["a"], false, [.ret [.ident "a"]]⟩) ]

/-- a caller holding `s := []byte{'a','b','c'}` at address 0 -/
def callerW : GoWorld :=
  { store := [(0, .arrayV [byt 97, byt 98, byt 99]), (1, .sliceV 0 0 3 3)],
    nextAddr := 2, locals := [("s", 1)] }

private def backing (w : GoWorld) : Option (List Int) :=
  match w.store.find? (fun p => p.1 == 0) with
  | some (_, .arrayV es) => some (es.map (fun v => match v with | .intV _ n => n | _ => -1))
  | _ => none

private def runE (e : Expr) : Option (Int × List Int) :=
  match (evalExpr prog 256 e) callerW with
  | .ok (.ok (.intV _ n), w) => match backing w with
                                | some bs => some (n, bs)
                                | none => none
  | _ => none

/-! ## THE PAIR. Same callee; only the call form differs. -/

/-! `clobber(s...)` — the callee ALIASES the caller's slice: `"Zbc"`. -/
#guard runE (.callDots "clobber" [] (.ident "s")) == some (3, [90, 98, 99])

/-! `clobber(s[0], s[1], s[2])` — packing gives a FRESH array, so the
caller's is untouched: `"abc"`. -/
#guard runE (.call "clobber"
              [ .index (.ident "s") (i64 0),
                .index (.ident "s") (i64 1),
                .index (.ident "s") (i64 2) ]) == some (3, [97, 98, 99])

/-! ## Zero variadic arguments — a slice of length 0, and it EXISTS. -/

#guard runE (.call "clobber" []) == some (0, [97, 98, 99])

/-! ## Spreading an EMPTY slice is also 0, and touches nothing. -/

#guard (match (evalExpr prog 256
                (.callDots "clobber" [] (.lit (.sliceV 0 0 0 0)))) callerW with
        | .ok (.ok (.intV _ n), w) => n == 0 && backing w == some [97, 98, 99]
        | _ => false) == true

/-! ## Fixed AND variadic parameters together -/

#guard (match (evalExpr prog 512 (.call "sum" [i64 10])) callerW with
        | .ok (.ok (.intV _ n), _) => n == 10 | _ => false) == true
#guard (match (evalExpr prog 512
                (.call "sum" [i64 10, i64 1, i64 2, i64 3])) callerW with
        | .ok (.ok (.intV _ n), _) => n == 16 | _ => false) == true

/-! `sum(10, q...)` where `q = []int{4,5}` is 19 — the spread supplies the
variadic parameter while `base` still takes its own argument. -/

/-- the caller also holds `q := []int{4,5}` at address 2 -/
def callerQ : GoWorld :=
  { callerW with
    store := (2, .arrayV [GoVal.mkInt IntKind.int64 4, GoVal.mkInt IntKind.int64 5])
               :: callerW.store,
    nextAddr := 3 }

#guard (match (evalExpr prog 512
                (.callDots "sum" [i64 10] (.lit (.sliceV 2 0 2 2)))) callerQ with
        | .ok (.ok (.intV _ n), _) => n == 19 | _ => false) == true

/-! ## A spread call on a NON-variadic function refuses.

`fixed(xs...)` does not compile in Go, so the model must not accept it. -/

#guard (match (evalExpr prog 64 (.callDots "fixed" [] (.ident "s"))) callerW with
        | .error (.unsupported _ m _) =>
            m == "fixed: spread call on a non-variadic function"
        | _ => false) == true

/-! ## Spreading a non-slice refuses. -/

#guard (match (evalExpr prog 64 (.callDots "clobber" [] (i64 7))) callerW with
        | .error (.unsupported _ m _) => m == "clobber: spread of a non-slice"
        | _ => false) == true

/-! ## Arity still binds on the FIXED parameters of a variadic signature. -/

#guard (match (evalExpr prog 64 (.call "sum" [])) callerW with
        | .error (.unsupported _ m _) => m == "sum: wrong argument count"
        | _ => false) == true

/-! ## Non-vacuity — these assert NEGATIVES. -/

#guard (runE (.callDots "clobber" [] (.ident "s"))).isSome
#guard (runE (.callDots "clobber" [] (.ident "s"))
          != runE (.call "clobber" [ .index (.ident "s") (i64 0),
                                     .index (.ident "s") (i64 1),
                                     .index (.ident "s") (i64 2) ]))
#guard (runE (.call "clobber" [ .index (.ident "s") (i64 0),
                                .index (.ident "s") (i64 1),
                                .index (.ident "s") (i64 2) ])
          != some (3, [90, 98, 99]))   -- packing must NOT alias

end Examples.go.variadic
