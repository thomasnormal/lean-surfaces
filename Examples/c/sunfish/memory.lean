import Examples.c.sunfish.guards

/-!
# M2 inch 2, INSTANTIATED: the memory model runs on the shipped corpus

`LeanModels/C/C23/Memory.lean` states the model. This file RUNS it — on
the three situations `docs/c-semantics-design.md` §2 names as the reasons
the model has the shape it does, using the corpus's own numbers.

**A lemma nobody instantiated is a lemma nobody checked**, and this
program has recorded three occasions where a green theorem turned out to
say nothing. So each of inch 2's four well-formedness theorems is applied
here to concrete fixture arguments, beside `#guard`s that execute the
operations themselves.

## The layout numbers, and where they come from

Struct layout is IMPLEMENTATION-DEFINED (`J.3.10`), so these offsets are
measurements, not derivations. They were probed with `_Static_assert` on
**both** hosts in `docs/c-profile.json` — `arm64-apple-darwin` and
`x86_64-unknown-linux-gnu` — and both agree:

    Pos    size 144   b 0   score 120   wc0..bc1 124..127   ep 128   kp 132   h 136
    Move   size 12    i 0   j 4   prom 8
    kcctx  size 24    p 0   m 8   found 20

The field NAMES and TYPES they rest on are checked against the ingested
envelope below, so a corpus that changed shape breaks this file rather
than silently invalidating its arithmetic. Deriving the offsets inside
Lean is the layout inch's job, not this one's.
-/

namespace Examples.c.sunfish.memory

-- The gates below compute over 120- and 144-element byte lists, and the
-- theorem applications reduce them; the default depth is not enough.
set_option maxRecDepth 8000

open LeanModels.C.C23
open LeanModels.C (CType)

/-! ## The version gate, perturbed in both directions

`LeanModels/C/C23.lean` states which envelopes the C23 surface accepts.
A gate nobody perturbed is decoration, so it is tested for what it
ACCEPTS and for what it would REJECT. -/

#guard acceptsEnvelope sunfishC == true
#guard acceptsEnvelope { sunfishC with profileFlags := ["-std=c17"] } == false
#guard acceptsEnvelope { sunfishC with language := "cpp" } == false

/-! ## The layout facts are accountable to the ingested term

Measured offsets are only as good as the struct they were measured on, so
the record this file assumes is checked against `sunfishC` — two paths,
one answer, exactly as M1's guards do it. -/

/-- The `Pos` record as the envelope carries it. -/
private def posFields : Option (List (String × CType)) :=
  (sunfishC.unit.items.filterMap fun i => match i with
    | .decl (.record _ fs _) =>
        let named := fs.filterMap fun f => match f with
          | .field n t _ => some (n, t)
          | _ => none
        if named.any (fun p => p.1 == "score") then some named else none
    | _ => none).head?

-- The nine fields, in declaration order, with the types the layout assumed.
#guard posFields == some
  [("b", "char[120]"), ("score", "int"), ("wc0", "unsigned char"),
   ("wc1", "unsigned char"), ("bc0", "unsigned char"), ("bc1", "unsigned char"),
   ("ep", "int"), ("kp", "int"), ("h", "uint64_t")]

/-- The `kcctx` record — the callback protocol's context. -/
private def kcctxFields : Option (List (String × CType)) :=
  (sunfishC.unit.items.filterMap fun i => match i with
    | .decl (.record (some "kcctx") fs _) =>
        some (fs.filterMap fun f => match f with
          | .field n t _ => some (n, t)
          | _ => none)
    | _ => none).head?

#guard kcctxFields == some [("p", "const Pos *"), ("m", "Move"), ("found", "int")]

/-! ## Layout, as measured (see the module docstring) -/

def posSize : Nat := 144
def posB : Nat := 0
def posScore : Nat := 120
def posEp : Nat := 128
def posH : Nat := 136

def kcctxSize : Nat := 24
def kcctxFound : Nat := 20

/-! ## Scenario 1 — `Pos p; memcpy(p.b, board, 120);`

sunfish.c L1130. **This is why the byte lattice is per-BYTE.** After the
`memcpy`, `p.b` is fully determined and `p.score`, `p.ep`, `p.kp`, `p.h`
are still indeterminate. A model that refused any read from a partly
initialized object would refuse the corpus; one that allowed it would
invent a score. -/

/-- `Pos p;` — an automatic object, every byte indeterminate (§6.2.4, §6.7.11). -/
def m1 : Mem := (Mem.empty.alloc .automatic posSize (some "Pos")).1
def pPos : Ptr := Ptr.toObject (Mem.empty.alloc .automatic posSize (some "Pos")).2

/-- The 120 board bytes the `memcpy` delivers. -/
def board : List CByte := List.replicate 120 (CByte.conc 46)   -- '.' = 46

/-- `memcpy(p.b, board, 120)` — a store through the DECAYED array. -/
def m1' : Except Refusal Mem := m1.storeBytes (Mem.member pPos posB) board

-- The store succeeds: 120 bytes at offset 0 of a 144-byte object.
#guard m1'.toOption.isSome

-- `p.b[0]` reads back what was written (§6.3.2.1p2 lvalue conversion).
#guard (m1'.toOption.get! |>.loadInt (Mem.member pPos posB) IntTy.char_)
  == .ok (.int IntTy.char_ 46)

-- `p.b[119]` too — the last byte the memcpy covered.
#guard (m1'.toOption.get! |>.loadInt (Mem.member pPos 119) IntTy.char_)
  == .ok (.int IntTy.char_ 46)

-- **`p.score` REFUSES.** The memcpy never reached offset 120, so its bytes
-- are indeterminate: J.2(11), §6.2.4 — an AUTOMATIC object read while its
-- representation is indeterminate.  No sanitizer on either development host
-- detects this; the byte lattice is the only instrument that does.
#guard (m1'.toOption.get! |>.loadInt (Mem.member pPos posScore) IntTy.int_)
  == .error (.memUB (.indetAutomatic 0 posScore))

-- ...and so do `p.ep` and `p.h`, for the same reason.
#guard !((m1'.toOption.get! |>.loadInt (Mem.member pPos posEp) IntTy.int_).toOption.isSome)
#guard !((m1'.toOption.get! |>.loadInt (Mem.member pPos posH) IntTy.ulong).toOption.isSome)

-- The refusal names its Annex J entry, and its cause never retires.
#guard (Refusal.memUB (.indetAutomatic 0 posScore)).j2 == some "J.2(11)"
#guard (Refusal.memUB (.indetAutomatic 0 posScore)).cause == (.undefined () : Cause)

-- Reading one byte PAST the object is a different refusal — J.2(46), the
-- structural one that `(obj, off)` makes decidable.
#guard (m1'.toOption.get! |>.loadInt (Mem.member pPos posSize) IntTy.char_)
  == .error (.memUB (.outOfBounds 0 144 1 144))

/-! ### The theorems, applied here

`resolve_alloc` and `loadBytes_storeBytes`, run on scenario 1's own
arguments rather than on a schematic. -/

/-- `resolve_alloc` at the `Pos` allocation: a 4-byte access into a
freshly created 144-byte automatic object resolves. -/
example : m1.resolve pPos 4
    = .ok (0, ⟨.automatic, true, List.replicate posSize .indet, some "Pos"⟩, 0) :=
  Mem.resolve_alloc Mem.empty .automatic posSize 4 (some "Pos") (by decide)

/-- `loadBytes_storeBytes` on the `memcpy`: the 120 board bytes read back
exactly. The store's success is supplied as the hypothesis it must be. -/
example (m' : Mem) (h : m1.storeBytes (Mem.member pPos posB) board = .ok m') :
    m'.loadBytes (Mem.member pPos posB) board.length = .ok board :=
  Mem.loadBytes_storeBytes (by rfl) h

/-! ## Scenario 2 — `struct kcctx c = {…}; gen_moves(p, kc_cb, &c);`

sunfish.c L369-370. **This is why a C local cannot be an environment
binding.** `&c` on an automatic object is the corpus's callback protocol,
the mechanism behind all 19 indirect calls; and when the block ends, every
pointer derived from it must stop working. -/

def m2 : Mem := (Mem.empty.alloc .automatic kcctxSize (some "struct kcctx")).1
/-- `&c` — §6.5.4.2p3, one of the 31 automatic address-of sites. -/
def pC : Ptr := Mem.addrOf (Mem.empty.alloc .automatic kcctxSize (some "struct kcctx")).2

/-- `c.found = 0`, through the pointer the callee received. -/
def m2' : Except Refusal Mem := m2.storeInt (Mem.member pC kcctxFound) IntTy.int_ 0

#guard (m2'.toOption.get! |>.loadInt (Mem.member pC kcctxFound) IntTy.int_)
  == .ok (.int IntTy.int_ 0)

-- The callee writes `c.found = 1` — the callback protocol's whole point.
#guard ((m2'.toOption.get! |>.storeInt (Mem.member pC kcctxFound) IntTy.int_ 1).toOption.get!
  |>.loadInt (Mem.member pC kcctxFound) IntTy.int_) == .ok (.int IntTy.int_ 1)

/-- The block ends (§6.2.4p6: the lifetime runs "until execution of that
block ends in any way"). -/
def m2dead : Mem := (m2'.toOption.get!).kill 0

-- **The pointer is still a well-formed VALUE, and using it REFUSES.**
-- J.2(9), §6.2.4p2.  That is only expressible because the object is a
-- tombstone rather than a reused slot.
#guard (m2dead.loadInt (Mem.member pC kcctxFound) IntTy.int_)
  == .error (.memUB (.deadObject 0 .automatic))
#guard (Refusal.memUB (.deadObject 0 .automatic)).j2 == some "J.2(9)"

/-- `resolve_kill` on the `kcctx` object: after the block ends, EVERY
access through `&c` refuses — for any width, not just the one gated above. -/
example (n : Nat) : m2dead.resolve (Mem.member pC kcctxFound) n
    = .error (.memUB (.deadObject 0 .automatic)) :=
  Mem.resolve_kill (m2'.toOption.get!) 0 _ _ n rfl rfl

/-! ## Scenario 3 — `realloc` MOVES the transposition table

sunfish.c L453-454, on the search path. **This is why pointers carry
provenance.** The old object dies and a fresh object receives the bytes;
every pointer derived from the old one must stop working, and an
`Addr := Nat` model cannot say so because the new block might reuse the
number. -/

def m3 : Mem := (Mem.empty.malloc 8).1
def pOld : Ptr := (Mem.empty.malloc 8).2

/-- Store a value into the table before it moves. -/
def m3' : Mem := (m3.storeInt pOld IntTy.int_ 1234).toOption.get!

-- Freshly `malloc`ed storage reads back as J.2(185) — `malloc`'s OWN
-- indeterminate entry, NOT the automatic J.2(11).  The annex separates
-- them and so does the model.
#guard (m3.loadInt pOld IntTy.int_) == .error (.memUB (.indetAllocated 0 0))
#guard (Refusal.memUB (.indetAllocated 0 0)).j2 == some "J.2(185)"

/-- `realloc(p, 16)` — the table grows and MOVES. -/
def m3r : Except Refusal (Mem × Ptr) := m3'.realloc pOld 16

#guard m3r.toOption.isSome

/-- The pointer `realloc` returned. -/
def pNew : Ptr := (m3r.toOption.get!).2
def m3new : Mem := (m3r.toOption.get!).1

-- **PROVENANCE TRANSFER**: the bytes moved to a genuinely different object.
#guard pNew.obj != pOld.obj
#guard (m3new.loadInt pNew IntTy.int_) == .ok (.int IntTy.int_ 1234)

-- **And the OLD pointer is dead.** J.2(10), §6.2.4p2 — the value of a
-- pointer to an object whose lifetime has ended is used.
#guard (m3new.loadInt pOld IntTy.int_) == .error (.memUB (.deadObject 0 .allocated))
#guard (Refusal.memUB (.deadObject 0 .allocated)).j2 == some "J.2(10)"

-- The grown tail is indeterminate, not zero — §7.24.3.7 (`J.2(186)` names
-- the same fact from the annex's side).
#guard !((m3new.loadInt (Mem.member pNew 12) IntTy.int_).toOption.isSome)

/-! ### `realloc(p, 0)` — the C23 change with NO Annex J entry -/

-- §7.24.3.7p3: undefined in C23, and NOT undefined in C17.
#guard (m3'.realloc pOld 0) == .error (.memUB (.reallocZero pOld))

-- **And Annex J has no entry for it.** Verified by exhaustive search of
-- all 221 entries; the gap is carried in the type rather than in a
-- comment, so this `none` is a finding a reader trips over.
#guard (Refusal.memUB (.reallocZero pOld)).j2 == none
#guard (MemFault.reallocZero pOld).clause == "7.24.3.7p3"
-- ...but it is still UB, so it still never retires.
#guard (Refusal.memUB (.reallocZero pOld)).cause == (.undefined () : Cause)

/-! ## The pointer-comparison asymmetry

§6.5.9p6 and §6.5.10p7 are neighbours in the standard and give OPPOSITE
verdicts on the same operands. A tidy model gets this wrong. -/

#guard Mem.ptrEq pOld pNew == false          -- §6.5.10p7: DEFINED, simply unequal
#guard Mem.ptrEq pOld pOld == true
#guard (Mem.ptrLt pOld pNew) == .error (.memUB (.relationalAcrossObjects pOld pNew))
#guard (Mem.ptrLt pOld (Mem.member pOld 4)) == .ok true   -- same object: fine
#guard (Mem.ptrLt Ptr.null Ptr.null).toOption.isNone      -- null is in no object

/-! ## `free`, and the two entries the annex keeps apart -/

#guard (m3'.free pOld).toOption.isSome
#guard (m3'.free Ptr.null).toOption.isSome                -- §7.24.3.3p2: a no-op
#guard ((m3'.free pOld).toOption.get! |>.free pOld)
  == .error (.memUB (.freeUnmatched pOld))                -- J.2(184): already freed
#guard (m1.free pPos) == .error (.memUB (.freeUnmatched pPos))  -- not from an allocator

/-! ## §6.5.7p9 — one-past-the-end is a LEGAL VALUE and an ILLEGAL ACCESS

The standard splits these, and so does the model: forming the pointer
succeeds, dereferencing it refuses. Getting this wrong in either
direction is a class of bug the corpus's 328 subscripts would hide. -/

#guard (Mem.offsetPtr m3new pNew 4 4).toOption == some ⟨some 1, 16⟩   -- exactly one past
#guard !((Mem.offsetPtr m3new pNew 4 5).toOption.isSome)              -- two past: J.2(43)
#guard !((m3new.loadInt ⟨some 1, 16⟩ IntTy.int_).toOption.isSome)     -- deref: J.2(46)
#guard (Mem.subscript m3new pNew 4 2).toOption == some ⟨some 1, 8⟩    -- §6.5.3.2p2 = `*(a+2)`

/-! ## The three causes stay unpooled

`docs/c23-goal.md` §3.1: they retire on completely different schedules,
so the scorer must be able to tell them apart without parsing a string. -/

#guard (Refusal.libc "qsort").cause == (.environment () : Cause)
#guard (Refusal.valueUB (.divideByZero "/")).cause == (.undefined () : Cause)
#guard (Refusal.valueUB (.divideByZero "/")).j2 == some "J.2(41)"
#guard (Refusal.valueUB (.signedOverflow "+" IntTy.int_ 2147483648)).j2 == some "J.2(35)"
-- `libc` has no J.2 index, because it is not UB.
#guard (Refusal.libc "qsort").j2 == none

-- **The third cause lives in `Halt`, not in `Refusal`** — the §3.4 ruling.
-- It reaches a scoreboard through `Outcome`, which is where the causes are
-- compared, and the three still do not pool.
#guard (Outcome.unsupported (α := CVal) "SwitchStmt").cause? == some (.unsupported () : Cause)
#guard (Outcome.refused (α := CVal) (.libc "qsort")).cause? == some (.environment () : Cause)
#guard (Outcome.refused (α := CVal) (.valueUB (.divideByZero "/"))).cause? == some (.undefined () : Cause)
#guard (Outcome.timeout (α := CVal)).cause? == none

-- **THE SNAPSHOT IS NOT AN OBSERVABLE, and these gates are where that is
-- checked rather than asserted.** Two refusals of the same construct
-- reached through DIFFERENT memories compare EQUAL, because `Halt`'s `BEq`
-- ignores the snapshot; and `Outcome` has nowhere to put a `Mem` at all.
#guard (LeanModels.Core.Loud.unsupported (σ := Mem) (.unsupported ()) "switch" (some Mem.empty))
    == (LeanModels.Core.Loud.unsupported (σ := Mem) (.unsupported ()) "switch" none)
#guard (LeanModels.Core.Loud.unsupported (σ := Mem) (.unsupported ()) "switch" (some m1))
    == (LeanModels.Core.Loud.unsupported (σ := Mem) (.unsupported ()) "switch" (some Mem.empty))
-- ...but the CAUSE and the PROSE are still compared, so the guard has not
-- disabled the gate it protects.
#guard (LeanModels.Core.Loud.unsupported (σ := Mem) (.unsupported ()) "switch" none)
    != (LeanModels.Core.Loud.unsupported (σ := Mem) (.unsupported ()) "goto" none)
#guard (LeanModels.Core.Loud.unsupported (σ := Mem) (.unsupported ()) "switch" none)
    != (LeanModels.Core.Loud.unsupported (σ := Mem) (.undefined ()) "switch" none)

end Examples.c.sunfish.memory
