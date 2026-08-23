import LeanModels.Go

/-!
# The range rung's acceptance: `strconv.digitZero` and `net.allFF`
  over a MIDDLE slice

`range` is not a second loop in this model. `Stmt.rangeS` **desugars to
`Stmt.forS`** and calls `execStmt` on the result, so every iteration runs
through the same `execLoop` the `bitLen` induction (§G15) is proved
about. There is no second loop implementation, and — because the range
variable IS the desugared init statement's variable — no second go1.22
per-iteration-scoping branch either. That reuse is the rung's claim, and
these guards are what make it a claim about `gc`'s behaviour rather than
about my desugaring.

## Why a MIDDLE slice

Ranging over `s` iterates `len(s)` times and touches `s[0] … s[len-1]`,
which are the BACKING array's cells `off … off+len-1`. Both halves of
that sentence are header facts, and on a slice whose header is the
identity (`off = 0`, `len = cap = len(backing)`) both are invisible. So
the acceptance case is again **(function, argument)**: the vendored
functions are ordinary, and the middle slice is what makes them
discriminating.

A third row is a CONSTRUCTED probe, not a vendored function: the
desugaring's counter must be hidden from the body, and no vendored
candidate exercises that. See the clobbered-range-variable section below.

Two functions, because the desugaring has TWO arms:

| form | vendored from | what its arm does |
| --- | --- | --- |
| `for i := range s` | `strconv.digitZero` | index only — desugars bare |
| `for _, v := range s` | `net.allFF` | prepends the element binding |

An arm without an acceptance case is an untested arm, so each gets one.

## What each row kills

| row | ranges over the BACKING array | ignores `off` |
| --- | --- | --- |
| `digitZero` returns 4 | fails (8) | passes |
| `base` = `"..0000.."` | fails (`"00000000"`) | fails (`"0000...."`) |
| `allFF(b[2:6])` = true | fails (sees `b[6]=0`) | fails |
| `allFF(b[4:8])` = false | passes | fails (window misplaced) |

The `allFF` pair is one function at two arguments whose ONLY difference
is the header, and the two answers disagree. No model that drops the
header can produce both.

Vendored verbatim (Go 1.25.6, BSD-3-Clause, "Copyright 2009 The Go
Authors", `docs/go-charter.md` §1.4):

    func digitZero(dst []byte) int {        // src/strconv/decimal.go
        for i := range dst {
            dst[i] = '0'
        }
        return len(dst)
    }

    func allFF(b []byte) bool {             // src/net/ip.go
        for _, c := range b {
            if c != 0xff {
                return false
            }
        }
        return true
    }

Every expected value below was printed by those two functions compiled by
`gc` and never typed by hand:

    $ cd <scratch>/rgen && go build -o rgen main.go && ./rgen
    -- gc: digitZero(base[2:6]) = 4 ; base = "..0000.."
    -- gc: allFF(b[2:6]) = true ; allFF(b[4:8]) = false

with `go version go1.25.6 darwin/arm64`.
-/

namespace Examples.go.rangeslice

open LeanModels LeanModels.Go

private def i64 (n : Int) : Expr := .lit (GoVal.mkInt IntKind.int64 n)
private def byt (n : Int) : GoVal := GoVal.mkInt IntKind.uint8 n

/-! ## The two functions, transcribed statement for statement -/

/-- `for i := range dst { dst[i] = '0' }; return len(dst)` -/
def digitZeroBody : List Stmt :=
  [ .rangeS (some "i") none (.ident "dst")
      [ .assignIndex (.ident "dst") (.ident "i") (.lit (byt 48)) ],
    .ret (some (.builtin1 "len" (.ident "dst"))) ]

/-- `for _, c := range b { if c != 0xff { return false } }; return true` -/
def allFFBody : List Stmt :=
  [ .rangeS none (some "c") (.ident "b")
      [ .ifS (.binary .ne (.ident "c") (.lit (byt 255)))
             [ .ret (some (.lit (.boolV false))) ] [] ],
    .ret (some (.lit (.boolV true))) ]

def prog : FuncTable :=
  [ ("digitZero", ⟨["dst"], digitZeroBody⟩),
    ("allFF",     ⟨["b"], allFFBody⟩) ]

/-! ## The worlds. One backing array each; the argument is a WINDOW. -/

/-- eight `'.'` bytes at address 0 -/
def dotBase : GoWorld :=
  { store := [(0, .arrayV (List.replicate 8 (byt 46)))], nextAddr := 1, locals := [] }

/-- `base[2:6]` — len 4, cap 6. Neither equals the backing length. -/
def mid : GoVal := .sliceV 0 2 4 6

/-- `0xff` everywhere EXCEPT cell 6, which is `0x00`. -/
def ffBase : GoWorld :=
  { store := [(0, .arrayV ((List.replicate 6 (byt 255)) ++ [byt 0, byt 255]))],
    nextAddr := 1, locals := [] }

def win26 : GoVal := .sliceV 0 2 4 6   -- cells 2,3,4,5 — the 0x00 is OUTSIDE
def win48 : GoVal := .sliceV 0 4 4 4   -- cells 4,5,6,7 — the 0x00 is INSIDE

private def baseBytes (w : GoWorld) : Option (List Int) :=
  match w.store.find? (fun p => p.1 == 0) with
  | some (_, .arrayV es) => some (es.map (fun v => match v with | .intV _ n => n | _ => -1))
  | _ => none

private def callWith (fn : String) (arg : GoVal) (w : GoWorld) : Option (GoVal × GoWorld) :=
  match (callFunction prog 64 fn [arg]) w with
  | .ok (.ok v, w') => some (v, w')
  | _ => none

/-! ## ROW 1 — `digitZero` returns 4.

`len(dst)` is the HEADER's length, not the backing array's. A model that
ranged over the backing object returns 8. -/

#guard (match callWith "digitZero" mid dotBase with
        | some (.intV _ n, _) => n == 4
        | _ => false) == true

/-! ## ROW 2 — the caller's array reads `"..0000.."`.

The decisive row for the index form: exactly four writes, and they land
at cells 2..5. Ranging over the backing array gives `"00000000"`;
dropping `off` gives `"0000...."`. -/

#guard (match callWith "digitZero" mid dotBase with
        | some (_, w) => baseBytes w == some [46, 46, 48, 48, 48, 48, 46, 46]
        | _ => false) == true

/-! ## ROW 3 — `allFF(b[2:6])` is TRUE though the array holds a `0x00`.

The value form's arm. The zero byte at cell 6 is outside the window, so
the loop never sees it. Any model that iterates the backing array
returns false here. -/

#guard (match callWith "allFF" win26 ffBase with
        | some (.boolV b, _) => b == true
        | _ => false) == true

/-! ## ROW 4 — the SAME function at a shifted header is FALSE.

Same code, same backing array, same length; only `off` differs, and the
answer flips. This is the pair no header-free model can produce. -/

#guard (match callWith "allFF" win48 ffBase with
        | some (.boolV b, _) => b == false
        | _ => false) == true

/-! ## The reuse is real: `range` IS `execLoop`.

The desugaring's own claim — a range loop and the hand-written
three-clause `for` it desugars to step to the same world. If `rangeS`
ever forks from `execLoop`, this row breaks. -/

#guard (let byHand : List Stmt :=
          [ .forS (some (.declare "i" (i64 0)))
                  (some (.binary .lt (.ident "i") (.builtin1 "len" (.ident "dst"))))
                  (some (.incDec "i" true))
                  [ .assignIndex (.ident "dst") (.ident "i") (.lit (byt 48)) ] ]
        let pHand : FuncTable := [("digitZero", ⟨["dst"], byHand ++ [.ret (some (.builtin1 "len" (.ident "dst")))]⟩)]
        (match (callFunction prog 64 "digitZero" [mid]) dotBase,
               (callFunction pHand 64 "digitZero" [mid]) dotBase with
         | .ok (.ok (.intV _ a), wa), .ok (.ok (.intV _ b), wb) =>
             a == b && baseBytes wa == baseBytes wb
         | _, _ => false)) == true

/-! ## An EMPTY window runs the body zero times.

`len = 0` is the boundary the desugared condition has to get right on the
FIRST test, before any iteration. The array must come back untouched. -/

#guard (match callWith "digitZero" (.sliceV 0 2 0 6) dotBase with
        | some (.intV _ n, w) => n == 0 && baseBytes w == some (List.replicate 8 46)
        | _ => false) == true

/-! ## THE CLOBBERED RANGE VARIABLE — a constructed probe, not a vendored
function, because none of the vendored candidates exercises it and the
desugaring gets it wrong if the counter is not hidden.

    func count(s []byte) int {
        n := 0
        for i := range s { n++; i = 100; _ = i }
        return n
    }

`gc` says **5** over a 5-element slice: `range` runs the full length
however the body maltreats the range variable. Desugaring with `i` AS the
counter gives **1**, and that was this rung's first implementation until
this row caught it. -/

def clobberBody : List Stmt :=
  [ .declare "n" (i64 0),
    .rangeS (some "i") none (.ident "s")
      [ .assign "n" (.binary .add (.ident "n") (i64 1)),
        .assign "i" (i64 100) ],
    .ret (some (.ident "n")) ]

def clobberProg : FuncTable := [("count", ⟨["s"], clobberBody⟩)]

/-- a 5-element backing array, ranged over whole -/
def fiveW : GoWorld :=
  { store := [(0, .arrayV (List.replicate 5 (byt 7)))], nextAddr := 1, locals := [] }

#guard (match (callFunction clobberProg 128 "count" [.sliceV 0 0 5 5]) fiveW with
        | .ok (.ok (.intV _ n), _) => n == 5      -- gc: 5, NOT 1
        | _ => false) == true

/-! ## Non-vacuity — these rows assert NEGATIVES, so a harness that
checked nothing would fail them. -/

#guard (callWith "digitZero" mid dotBase).isSome
#guard (match callWith "digitZero" mid dotBase with
        | some (_, w) =>
            -- NOT the whole array, and NOT the array left alone
            baseBytes w != some (List.replicate 8 48)
              && baseBytes w != some (List.replicate 8 46)
        | _ => false) == true
#guard (match callWith "allFF" win26 ffBase, callWith "allFF" win48 ffBase with
        | some (.boolV a, _), some (.boolV b, _) => a != b   -- the pair DISAGREES
        | _, _ => false) == true

/-! ## `range` over a non-slice REFUSES — and refusal is never `undefined`. -/

#guard (match (execStmt prog 8 (.rangeS (some "i") none (.lit (.boolV true)) [])) dotBase with
        | .error (.unsupported c _ _) =>
            -- the CLASS is `unsupported`, and — the zero-UB gate, checked
            -- at a live call site rather than only in the image lemma —
            -- it is not `undefined`.
            c.className == "unsupported" && c.className != "undefined"
        | _ => false) == true

end Examples.go.rangeslice
