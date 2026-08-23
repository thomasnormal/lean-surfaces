import LeanModels.Go

/-!
# Rung 1's guards

The Go lane's `#guard` battery. This file is also the lane's **build
hook**: `LeanModels` is a `lean_lib` with no glob, so nothing under
`LeanModels/Go/` would be built by `lake build` on its own. Importing
`LeanModels.Go` from a file the `Examples.+` glob DOES match pulls the
whole lane into the default targets and into CI — with **no edit to
`LeanModels.lean` or `lakefile.toml`**, both of which
`tools/triad.sh` classifies as spine.

That is the C lane's precedent, taken deliberately:
`docs/c-tier-charter.md` §4.8 records the same mechanism, and records
that taking the authorized spine import ANYWAY was measured unnecessary,
tried, and reverted because it coupled the C lane into every Python
file's import graph.

Every guard below is non-vacuous: flipping the expected value makes Lean
report the failing expression, which was checked for a sample of them
rather than assumed.
-/

namespace Examples.go.rung1

open LeanModels.Go

/-! ## Integer overflow is DEFINED — the charter's headline, executable

`docs/go-charter.md`: "undefined" appears zero times in the Go
specification, against C23's 284. Here is the arithmetic corner where C
must refuse and Go must not. -/

#guard IntKind.wrap IntKind.int8 128 == -128        -- signed overflow WRAPS
#guard IntKind.wrap IntKind.int8 (-129) == 127
#guard IntKind.wrap IntKind.uint8 256 == 0          -- unsigned, modulo 2^n
#guard IntKind.wrap IntKind.uint8 (-1) == 255
#guard IntKind.wrap IntKind.int64 (2 ^ 63) == -(2 ^ 63)

/-! ## The per-file language version — the versioning exemplar

`docs/go-charter.md` §3.2 measured ONE compiler invocation applying BOTH
loop-scoping rules to byte-identical bodies, selected per file. The model
branches on data rather than forking. -/

#guard LangVersion.perIterationLoopVars LangVersion.go121 == false
#guard LangVersion.perIterationLoopVars LangVersion.go122 == true
#guard LangVersion.perIterationLoopVars ⟨1, 25⟩ == true

/-! ## Flow — a non-normal flow stops a sequence -/

#guard Flow.normal.isNormal == true
#guard (Flow.returned none).isNormal == false
#guard (Flow.broke (some "scan")).isNormal == false
#guard (Flow.continued none).isNormal == false

/-! ## The walker, on programs

`runTo` runs a statement sequence and reads one local back out, so a
guard can name a concrete answer instead of a monadic value. -/

def runTo (stmts : List Stmt) (name : String) : Option Int :=
  match (execSeq 64 stmts) ({} : GoWorld) with
  | .ok (.ok _, w) =>
      match w.locals.find? (fun p => p.1 == name) with
      | some (_, a) =>
          match w.store.find? (fun p => p.1 == a) with
          | some (_, .intV _ n) => some n
          | _ => none
      | none => none
  | _ => none

/-- The rendered refusal a program produced, if it refused.

**Core's `Loud` now carries the cause as DATA** — `.unsupported cause message
snapshot` — so the prefix `renderRefusal` writes is a rendering for HUMANS and
no longer the only way to recover the class. This function still returns the
message, and `refusedWith` below still reads the prefix, so every guard in this
file keeps its exact meaning and the text is byte-identical to what it was.

Consuming `cause` structurally instead of parsing the prefix is the obvious
next move and is deliberately NOT made here: it is the Go lane's call which of
its own guards should read a constructor rather than a string, and this file is
their demonstration surface, not the merging lane's. -/
def refusalOf (stmts : List Stmt) : Option String :=
  match (execSeq 64 stmts) ({} : GoWorld) with
  | .error (.unsupported _ m _) => some m
  | _ => none

/-- Did the program refuse with this cause? -/
def refusedWith (stmts : List Stmt) (c : RefusalCause) : Bool :=
  match refusalOf stmts with
  | some m => m.startsWith s!"[{c.tag}|"
  | none => false

private def i64 (n : Int) : Expr := .lit (GoVal.mkInt IntKind.int64 n)

/-! `var x = 2; x = x + 3` — declaration, assignment, binary, ident. -/
#guard runTo [.declare "x" (i64 2),
              .assign "x" (.binary .add (.ident "x") (i64 3))] "x" == some 5

/-! `x++` on a declared local. -/
#guard runTo [.declare "x" (i64 41), .incDec "x" true] "x" == some 42

/-! An `if` that takes the true branch, with a parenthesised condition —
`ParenExpr` is a NODE, not parser sugar. -/
#guard runTo [.declare "x" (i64 0),
              .ifS (.paren (.binary .lt (i64 1) (i64 2)))
                   [.assign "x" (i64 7)] [.assign "x" (i64 9)]] "x" == some 7

/-! The false branch. -/
#guard runTo [.declare "x" (i64 0),
              .ifS (.binary .gt (i64 1) (i64 2))
                   [.assign "x" (i64 7)] [.assign "x" (i64 9)]] "x" == some 9

/-! Signed overflow inside the WALKER, not just in `wrap`: the value
exists and no refusal is raised. -/
#guard runTo [.declare "x" (.binary .add (.lit (GoVal.mkInt IntKind.int8 127))
                                         (.lit (GoVal.mkInt IntKind.int8 1)))] "x"
       == some (-128)

/-! Address-of a local, then dereference it. Go locals are addressable,
which is why the world maps names to ADDRESSES. -/
#guard runTo [.declare "x" (i64 11),
              .declare "p" (.addrOf "x"),
              .declare "y" (.deref (.ident "p"))] "y" == some 11

/-! A non-normal flow stops the sequence: the assignment after the
`return` never runs, so `x` keeps its first value. -/
#guard runTo [.declare "x" (i64 1), .ret none, .assign "x" (i64 2)] "x" == some 1

/-! `break` likewise. -/
#guard runTo [.declare "x" (i64 1), .branch .break_ none, .assign "x" (i64 2)] "x" == some 1

/-! The empty statement is a no-op, and a labelled empty statement is
too — the shape that puts `EmptyStmt` in real code. -/
#guard runTo [.declare "x" (i64 3), .empty, .labeled "end" .empty] "x" == some 3

/-! ## THE ZERO-UB GATE, executable

`docs/family-architecture.md` §4.3's Go row: cause 2 is expected EMPTY and
should be gated. `GoRefusal` makes it unreachable by construction; these
rows check that the refusals the walker actually emits land in the other
three, and — critically — that `undefined` is a real constructor, so the
gate is a restriction rather than a statement about an empty type. -/

#guard (RefusalCause.undefined == RefusalCause.unsupportedConstruct) == false

/-! `goto` is in rung 1's census but not stepped at inch 1: it refuses as
an out-of-tier CONSTRUCT, never as undefined behaviour. -/
#guard refusedWith [.branch .goto_ (some "end")] RefusalCause.unsupportedConstruct

/-! An unbound identifier is a construct refusal too — not a zero value,
and not undefined. -/
#guard refusedWith [.expr (.ident "nope")] RefusalCause.unsupportedConstruct

/-! A statement in the vocabulary but unstepped names itself. -/
#guard refusedWith [.unmodeled "SwitchStmt"] RefusalCause.unsupportedConstruct

/-! A condition that is not a boolean refuses rather than coercing: Go has
no truthiness. -/
#guard refusedWith [.ifS (i64 1) [] []] RefusalCause.unsupportedConstruct

/-! ## Division by zero is a PANIC, not undefined behaviour

"Run-time panics" makes integer division by zero a defined run-time
panic. It therefore goes to ρ — it is catchable in principle by `recover`
— and must NOT appear as a refusal at all. -/

/-! It does not refuse. -/
#guard refusalOf [.declare "x" (.binary .quo (i64 1) (i64 0))] == none

/-! It panics: the run ends in ρ, with the runtime's message. -/
#guard (match (execSeq 64 [.declare "x" (.binary .quo (i64 1) (i64 0))]) ({} : GoWorld) with
        | .ok (.error p, _) =>
            match p.value with
            | .stringV msg => msg == "runtime error: integer divide by zero"
            | _ => false
        | _ => false) == true

/-! ## Axioms — no `sorry`, no `native_decide` -/

#print axioms LeanModels.Go.goRefusal_never_undefined
#print axioms LeanModels.Go.int8_max_plus_one
#print axioms LeanModels.Go.loopvars_go122
#print axioms LeanModels.Go.refuseGo_cause_never_undefined
#print axioms LeanModels.Go.wrap_idem_int8

end Examples.go.rung1
