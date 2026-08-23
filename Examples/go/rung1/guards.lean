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

open LeanModels LeanModels.Go

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
  match (execSeq [] 64 stmts) ({} : GoWorld) with
  | .ok (.ok _, w) =>
      match w.locals.find? (fun p => p.1 == name) with
      | some (_, a) =>
          match w.store.find? (fun p => p.1 == a) with
          | some (_, .intV _ n) => some n
          | _ => none
      | none => none
  | _ => none

/-- The refusal a program produced, if it refused — as DATA. Core's
`Loud.unsupported` now carries the class as a typed field, so this reads
it structurally. It used to return the message and the guards parsed a
`[tag|…]` prefix off the front; that prefix existed only because the
typed field did not, and both are retired. -/
def refusalOf (stmts : List Stmt) : Option (RefusalCause SpecRef) :=
  match (execSeq [] 64 stmts) ({} : GoWorld) with
  | .error (.unsupported c _ _) => some c
  | _ => none

/-- Did the program refuse in this §5.2 class? Compares `className`, which
Core emits verbatim and which a scoreboard buckets on. -/
def refusedWith (stmts : List Stmt) (cls : String) : Bool :=
  match refusalOf stmts with
  | some c => c.className == cls
  | none => false

/-- Which clause did the refusal cite? `π` is a typed field too, so the
citation is readable without touching the prose. -/
def refusalClause (stmts : List Stmt) : Option SpecRef :=
  (refusalOf stmts).map RefusalCause.detail

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

/-! ## Structs — `TypeSpec` is 72.4% of type declarations -/

#guard runTo [.typeDecl "pt" ["x", "y"],
              .declare "p" (.structLit "pt" [("x", i64 3), ("y", i64 4)]),
              .declare "r" (.field (.ident "p") "y")] "r" == some 4

/-! An absent field takes the zero value rather than being missing, and a
field the type does not declare is a refusal rather than an invention. -/

#guard (match (execSeq [] 64 [.typeDecl "pt" ["x", "y"],
                           .declare "p" (.structLit "pt" [("x", i64 1)])])
                          ({} : GoWorld) with
        | .ok (.ok _, w) =>
            match w.store.find? (fun q => q.1 == 0) with
            | some (_, .structV fs) => fs.length == 2
            | _ => false
        | _ => false) == true

#guard refusedWith [.typeDecl "pt" ["x"],
                    .declare "p" (.structLit "pt" [("nope", i64 1)])] "unsupported"
#guard refusedWith [.declare "p" (.structLit "undeclared" [])] "unsupported"

/-! ## THE §3.3 ACCEPTANCE TEST — one model, two versions, one program

`docs/go-charter.md` §3.3 set this as the gate for the loop-variable
delta: the model must give byte-identical loop bodies DIFFERENT meanings
under go1.21 and go1.22, because the real compiler does — §3.2 measured
one invocation applying both rules to one package.

The observable here is **pointer identity**, not closure capture, which is
the same thing §3.2 measured on the real toolchain: *"collecting `&i`
across iterations and counting distinct pointers gives 1 distinct address
under go1.21 and 3 under go1.22."* The program counts how many times
`&i` CHANGES across three iterations. -/

def loopVarProbe : List Stmt :=
  [ .declare "changes" (i64 0),
    .declare "last" (.lit GoVal.nilV),
    .forS (some (.declare "i" (i64 0)))
          (some (.binary .lt (.ident "i") (i64 3)))
          (some (.incDec "i" true))
          [ .declare "p" (.addrOf "i"),
            .ifS (.binary .ne (.ident "p") (.ident "last"))
                 [.assign "changes" (.binary .add (.ident "changes") (i64 1))] [],
            .assign "last" (.ident "p") ] ]

def runUnder (v : LangVersion) (stmts : List Stmt) (name : String) : Option Int :=
  match (execSeq [] 256 stmts) ({ lang := v } : GoWorld) with
  | .ok (.ok _, w) =>
      match w.locals.find? (fun q => q.1 == name) with
      | some (_, a) =>
          match w.store.find? (fun q => q.1 == a) with
          | some (_, .intV _ n) => some n
          | _ => none
      | none => none
  | _ => none

/-! **go1.21: the variable is re-used, so `&i` never changes — 1.**
**go1.22: each iteration has its own, so it changes every time — 3.**
Same `loopVarProbe`, same walker, one field of the world different. -/

#guard runUnder LangVersion.go121 loopVarProbe "changes" == some 1
#guard runUnder LangVersion.go122 loopVarProbe "changes" == some 3

/-! And the half a model can omit while still passing every
closure-capture test: the previous iteration's VALUE must be copied into
the fresh variable, or `post` advances a variable the body never sees and
an ordinary counting loop silently breaks. The loop runs exactly three
times under BOTH versions. -/

def countProbe : List Stmt :=
  [ .declare "n" (i64 0),
    .forS (some (.declare "i" (i64 0)))
          (some (.binary .lt (.ident "i") (i64 5)))
          (some (.incDec "i" true))
          [.assign "n" (.binary .add (.ident "n") (i64 1))] ]

#guard runUnder LangVersion.go121 countProbe "n" == some 5
#guard runUnder LangVersion.go122 countProbe "n" == some 5

/-! ## Bare `for {}` — 47.0% of loops, and only fuel bounds it -/

#guard (match (execSeq [] 64 [.forS none none none []]) ({} : GoWorld) with
        | .error .timeout => true
        | _ => false) == true

/-! `break` still escapes a bare loop, so the exhaustion above is the
loop's own semantics and not a walker that cannot leave one. -/

#guard runTo [.declare "x" (i64 7),
              .forS none none none [.branch .break_ none]] "x" == some 7

/-! ## `fallthrough` is DEFERRED as its own rung, at a measured 4.0%

208 of 5,186 switches (`docs/backlog/go.md` §G4). It refuses as an
out-of-tier construct — never as undefined behaviour. -/

#guard refusedWith [.branch .fallthrough_ none] "unsupported"
#guard (refusalOf [.branch .fallthrough_ none]).map RefusalCause.isUndefined == some false

/-! ## THE ZERO-UB GATE, executable

`docs/family-architecture.md` §4.3's Go row: cause 2 is expected EMPTY and
should be gated. `GoRefusal` makes it unreachable by construction; these
rows check that the refusals the walker actually emits land in the other
three, and — critically — that `undefined` is a real constructor, so the
gate is a restriction rather than a statement about an empty type. -/

#guard (RefusalCause.undefined (SpecRef.spec "x")).isUndefined == true

/-! `goto` is in rung 1's census but not stepped at inch 1: it refuses as
an out-of-tier CONSTRUCT, never as undefined behaviour. -/
#guard refusedWith [.branch .goto_ (some "end")] "unsupported"

/-! An unbound identifier is a construct refusal too — not a zero value,
and not undefined. -/
#guard refusedWith [.expr (.ident "nope")] "unsupported"

/-! A statement in the vocabulary but unstepped names itself. -/
#guard refusedWith [.unmodeled "SwitchStmt"] "unsupported"

/-! A condition that is not a boolean refuses rather than coercing: Go has
no truthiness. -/
#guard refusedWith [.ifS (i64 1) [] []] "unsupported"

/-! The cited clause travels as DATA, so a guard can name it. `goto`
refuses under the spec's "Goto_statements"; an unbound identifier under
"Declarations_and_scope". Neither is reachable by reading prose. -/

#guard (refusalClause [.branch .goto_ (some "end")]).map SpecRef.section_
       == some "Goto_statements"
#guard (refusalClause [.expr (.ident "nope")]).map SpecRef.doc == some "spec"

/-! **The zero-UB gate, read as data.** No refusal this tier can emit is
in the `undefined` class — checked here on the four refusals the walker
actually produces, and proved for ALL of them in `Spec.lean`. -/

#guard (refusalOf [.branch .goto_ (some "end")]).map RefusalCause.isUndefined == some false
#guard (refusalOf [.expr (.ident "nope")]).map RefusalCause.isUndefined == some false
#guard (refusalOf [.unmodeled "SwitchStmt"]).map RefusalCause.isUndefined == some false
#guard (refusalOf [.ifS (i64 1) [] []]).map RefusalCause.isUndefined == some false

/-! ## Division by zero is a PANIC, not undefined behaviour

"Run-time panics" makes integer division by zero a defined run-time
panic. It therefore goes to ρ — it is catchable in principle by `recover`
— and must NOT appear as a refusal at all. -/

/-! It does not refuse. -/
#guard (refusalOf [.declare "x" (.binary .quo (i64 1) (i64 0))]).isNone

/-! It panics: the run ends in ρ, with the runtime's message. -/
#guard (match (execSeq [] 64 [.declare "x" (.binary .quo (i64 1) (i64 0))]) ({} : GoWorld) with
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
