import LeanModels.Go.Value
import LeanModels.Core.Outcome

/-!
# The Go tier's substrate, its refusals, and panic as ρ

M1 inch 1, second half. `docs/go-charter.md` §6 is the design; this is it
in Lean, with no evaluator attached beyond the first statement walker.

## The substrate, adopted BY SHAPE

`docs/family-architecture.md` §3.4 fixes the family's substrate as
`ExceptT ρ (StateT W Halt)`, in that order — `StateT` outside `ExceptT`
discards the state on a raise, and the tier's own error postcondition then
cannot be stated.

**ADOPTED, not defined.** This file first carried the shape locally with
an adoption note, per the ES lane's precedent. `LeanModels/Core/Outcome.lean`
landed at `376735e`, so the local copy was **REPLACED by the import** —
replaced, not wrapped. `SemM`, `Halt`, `Loud`, `refuse` and `exhausted`
all come from Core and this tier defines none of them.

Core's stack is `ExceptT ρ (StateT W (Except Loud))`, which is the same
layer order the local copy had and for the same stated reason: `StateT`
outside `ExceptT` discards the state on a raise.

## Why ρ is a PANIC, and why a panic has an identity

`docs/go-charter.md` §6.1 fixes ρ = panic. The Go specification, "Handling
panics", verbatim:

> While executing a function `F`, an explicit call to `panic` or a
> run-time panic terminates the execution of `F`. Any functions deferred
> by `F` are then executed as usual. Next, any deferred functions run by
> `F`'s caller are run, and so on up to any deferred by the top-level
> function in the executing goroutine. At that point, the program is
> terminated and the error condition is reported, including the value of
> the argument to `panic`.

That is `ExceptT`'s propagation exactly — unwinding that runs deferred
work at each frame and carries a value out — so `panic` in ρ makes the
correspondence mechanical rather than encoded.

**The identity is not decoration.** The spec's `recover` rule turns on
*which* panic is being recovered: a deferred function that itself panics
replaces the panic in flight, and `recover` stops the panicking sequence
only when called directly by a function deferred by the panicking frame.
A ρ carrying only a value cannot tell a re-panic from the panic it
replaced, and every later rule about `recover` would have to reconstruct
that distinction from context. So a `Panic` is `(id, value)`, and the
identity is minted at the point the panic starts.

Note that Go's zero-UB posture reaches even here: "Integer overflow" says
**"Overflow does not cause a run-time panic"**, so arithmetic never
produces one of these. `Spec.lean` gates that.
-/

namespace LeanModels.Go

/-- A pointer into the specification — the π every refusal carries.

A refusal that cannot name the clause it is refusing under is one a human
cannot act on, and one a scoreboard cannot bucket without parsing prose.
`doc` distinguishes the tier's TWO co-equal documents
(`docs/go-charter.md` §1): the language specification and the memory
model. -/
structure SpecRef where
  /-- `"spec"` for the Go Programming Language Specification, `"mem"` for
  the Go Memory Model. -/
  doc : String
  /-- The section's anchor, e.g. `"Integer_overflow"`. -/
  section_ : String
  deriving Repr, DecidableEq, Inhabited

namespace SpecRef
def spec (s : String) : SpecRef := ⟨"spec", s⟩
def mem (s : String) : SpecRef := ⟨"mem", s⟩
end SpecRef

/-- The family's four refusal causes (`docs/family-architecture.md` §5.2),
instantiated for Go.

`undefined` is PRESENT and is expected to stay EMPTY. That is the point:
`docs/go-charter.md`'s zero-UB finding is a claim about a document, and
leaving the constructor out would make it unfalsifiable inside the model.
Present-and-gated turns it into a property a `#guard` can check — the
treatment `docs/family-architecture.md` §4.3 prescribes for WebAssembly,
whose cause-2 bucket is empty by design. Go's is empty for a different
reason: the memory model bounds its worst case rather than surrendering
it. **A Go tier that ever emits `undefined` has a bug**, and `Spec.lean`
says so in a form that fails. -/
inductive RefusalCause where
  /-- Syntax or a construct the tier does not model yet. Retires by
  climbing a rung. -/
  | unsupportedConstruct
  /-- The language says this run has no meaning. **Expected empty for Go**
  — see the note above. -/
  | undefined
  /-- Outside the modeled slice: an unmodeled builtin or package. Retires
  by widening the slice, and is never a language-tier gap. -/
  | environment
  /-- The language admits several orders — or several schedules — and the
  model cannot show the observable invariant under all of them
  (`docs/go-charter.md` §2.1). Retires by strengthening the
  race-freedom census, never by guessing. -/
  | orderDependence
  deriving Repr, DecidableEq, Inhabited

/-! ## Refusal causes, and the π every refusal carries

Core's `Loud` has exactly two constructors — `timeout` and
`unsupported (msg : String)` — and its header is explicit that a tier
needing more causes *"does not extend this type"*. So the Go tier's
four-cause taxonomy (`docs/family-architecture.md` §5.2) and its
spec-section pointer live HERE, and are rendered into Core's message.

**This is a gap worth naming rather than papering over, and it is
reported to the coordinator**: §5.2 requires the four causes be
*"reported separately"* because pooling them makes the scoreboard
unreadable, and a `String` payload means a scoreboard must parse prose to
bucket them. The rendering below is deterministic and prefix-tagged so
that parsing is at least mechanical, but a structured payload in Core
would be better. -/

/-- A panic in flight — ρ. See the header for why it carries an identity
as well as a value. -/
structure Panic where
  /-- Minted when the panicking sequence starts, so a re-panic raised by a
  deferred function is a DIFFERENT panic from the one it replaced. -/
  id : Nat
  /-- The argument to `panic`, reported when the program terminates. -/
  value : GoVal
  deriving Repr, Inhabited

/-- The language version in force for a file.

`docs/go-charter.md` §3 measured that this is not a label: Go 1.21 and Go
1.22 give the same `for` statement different variable scoping, and §3.2's
run showed ONE compiler invocation applying BOTH semantics to
byte-identical loop bodies in one package. So the version is carried
**per file**, which is the one place the Go envelope must differ
structurally from C's `profile_id`. -/
structure LangVersion where
  major : Nat
  minor : Nat
  deriving Repr, DecidableEq, Inhabited

namespace LangVersion
def go121 : LangVersion := ⟨1, 21⟩
def go122 : LangVersion := ⟨1, 22⟩
/-- The predicate the loop rule branches on: per-iteration scoping is
Go 1.22 and later. -/
def perIterationLoopVars (v : LangVersion) : Bool :=
  v.major > 1 || (v.major = 1 && v.minor ≥ 22)
end LangVersion

/-- The world — W. The envelope's store shape, plus the two things every
rule needs to read and nothing else yet.

`sched` is carried from the FIRST COMMIT even though `Schedule` is a
one-element type and no rule reads it. `docs/go-charter.md` §6.2 makes
this the tier's one non-negotiable structural commitment, on measured
grounds: `docs/c-tier-charter.md` §3.3 records that C's concurrency rung
"is the one rung that is not a widening — it replaces a state function
with a memory-ORDER relation, which would change the interpreter's TYPE".
Carrying the field means the type never changes; only the inhabitants of
`Schedule` grow. -/
structure Schedule where
  /-- A one-element type today. The choice oracle of §6.2 — goroutine
  interleaving, `select`'s uniform choice, and map iteration order all
  resolve here, because all three are choices made outside the program
  text and the model should have exactly one place for them. -/
  unit : Unit := ()
  deriving Repr, Inhabited

structure GoWorld where
  /-- The store: addresses to values. Go locals are addressable, so a
  binding is not enough (`docs/go-charter.md` §6.1). -/
  store : List (Addr × GoVal) := []
  /-- Next free address, so allocation is deterministic and the ledger is
  statable. -/
  nextAddr : Addr := 0
  /-- Locals: name to ADDRESS, not name to value. Go locals are
  addressable — `&x` on a local is legal and rung 1's fixture takes the
  address of one — so a binding that held a value directly could not
  model `&x` at all. This is the same reason `docs/go-charter.md` §6.1
  gives for not reusing the Python tier's `REnv`. -/
  locals : List (String × Addr) := []
  /-- Emitted bytes. Output is world data, per the family's
  effects-as-world-data treatment. -/
  stdout : List String := []
  /-- The language version of the file being executed. Per FILE, not per
  program — see `LangVersion`. -/
  lang : LangVersion := LangVersion.go122
  /-- The choice oracle. Unread at inch 1, by design. -/
  sched : Schedule := {}
  deriving Repr, Inhabited

/-- The Go tier's instantiation of the FAMILY monad: the world is
`GoWorld`, and ρ is a panic. `SemM` is Core's. -/
abbrev GoM := SemM GoWorld Panic

/-- **The zero-UB gate, as a TYPE rather than a convention.**

`docs/go-charter.md` measured that "undefined" appears zero times in the
Go specification. `RefusalCause` nonetheless CARRIES `undefined`, because
the family taxonomy is one taxonomy and a lane that deleted the
constructor could not state that its bucket is empty.

The gate is this narrower type. Every refusal the Go tier emits goes
through `SemM.refuseGo`, whose cause argument is a `GoRefusal` — and
`GoRefusal` has no `undefined`. So the emptiness of cause 2 is not a
promise a reviewer checks by reading, nor a grep that a new call site can
slip past: **it is unreachable by construction, and `Spec.lean` proves the
image excludes it.** A future rung that genuinely found undefined
behaviour in Go would have to widen this type on purpose, which is
exactly the deliberate act it should be. -/
inductive GoRefusal where
  | unsupportedConstruct
  | environment
  | orderDependence
  deriving Repr, DecidableEq, Inhabited

/-- The image of `GoRefusal` in the family's four causes. `undefined` is
not in it, and that is the theorem `Spec.lean` records. -/
def GoRefusal.toCause : GoRefusal → RefusalCause
  | .unsupportedConstruct => .unsupportedConstruct
  | .environment => .environment
  | .orderDependence => .orderDependence

/-- The family's own name for each cause (`docs/family-architecture.md`
§5.2). Spelled explicitly rather than via `repr`, so the scoreboard's key
is stable under any change to the constructor's Lean name. -/
def RefusalCause.tag : RefusalCause → String
  | .unsupportedConstruct => "unsupported"
  | .undefined => "undefined"
  | .environment => "environment"
  | .orderDependence => "order-dependence"

/-- Render a refusal into Core's `String` payload. Deterministic and
prefix-tagged: the cause comes first, then the clause, then the prose, so
a scoreboard buckets on a prefix rather than on a search. -/
def renderRefusal (c : RefusalCause) (π : SpecRef) (msg : String) : String :=
  s!"[{c.tag}|{π.doc}:{π.section_}] {msg}"

/-- The Go tier's refusal, and the ONLY way this tier refuses. Narrower
than Core's `refuse` on purpose — see `GoRefusal`. -/
def refuseGo {W ρ α : Type} (r : GoRefusal) (π : SpecRef) (msg : String) : SemM W ρ α :=
  LeanModels.refuse (renderRefusal r.toCause π msg)

/-- Start a panicking sequence with a fresh identity. State-RETAINING, per
Core's ρ channel. -/
def panicWith (id : Nat) (v : GoVal) : GoM α := LeanModels.raiseIn ⟨id, v⟩

end LeanModels.Go
