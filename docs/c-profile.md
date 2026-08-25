# The C tier's profile — an ABSTRACT schema, not a pinned machine

**Status: the C-tier charter's inch 3 (`docs/c-tier-charter.md` §4.3),
landed. This supersedes the architecture memo's §3.3 "pin one host" and
answers its open question 3.**

**The ruling is the coordinator's default and Thomas can override it.**
It was taken with an explicit stop-condition attached: *if the census
shows ctwin depends on any fact where the two development hosts differ,
stop and flag loudly, because that changes the ruling.* **The condition
was tested first and it does not fire** (§2). Everything below stands on
that measurement.

---

## 1 The ruling

**Pin the FACTS the corpus depends on, as a schema every host must
satisfy — not one machine as the oracle.**

The architecture memo proposed `docs/c-profile-<id>.md`, one document per
host, with the host chosen up front because *"the profile must be pinned
before the extractor is written, since it is an input to the AST."* That
premise is right and is kept. The conclusion is replaced, for three
reasons:

1. **The tier has two development hosts** — an arm64 macOS laptop and an
   x86-64 Linux box — and pinning either one makes the other a
   second-class citizen that silently produces a different envelope.
2. **A schema is CHECKABLE and a pin is only DECLARABLE.** §3's guard
   decides any host in under a second, including hosts nobody has, which
   is what turns "which machine is the oracle" from a standing question
   into a gate.
3. **It is the honest shape of the claim.** The tier does not depend on
   Apple clang; it depends on `CHAR_BIT == 8` and eight facts like it.
   Writing down the machine instead of the facts would state the claim
   more narrowly than it is and more strongly than it is at the same
   time.

The `-std=c23 -D_FORTIFY_SOURCE=0` pin from the memo's §4.3 is unchanged
and is not what this document replaces: those flags are an INPUT to the
AST and remain a first-class envelope field.

## 2 The stop-condition, tested — the two hosts agree on everything

`harness/c_profile_probe.py`, landed with this document, decides every
fact by `_Static_assert` under `clang -target <triple> -fsyntax-only`.
clang folds the constant expression for the TARGET's ABI, so **one laptop
can certify a host it cannot execute** — which is the whole reason a
two-host schema is checkable at all. Nothing runs a cross-compiled
binary.

```
$ python3 harness/c_profile_probe.py --target arm64-apple-darwin \
      --target x86_64-unknown-linux-gnu -o docs/c-profile.json
wrote docs/c-profile.json (2 hosts, 13 facts, 8 depended-on)
all hosts agree on every fact
```

**Thirteen facts, eight depended on, zero disagreements.** The ruling
stands. Machine-readable rows in `docs/c-profile.json`.

## 3 The facts

`depended on` means the corpus has a construct whose MEANING changes if
the fact changes. Facts that are merely true are recorded anyway, because
the argument that they are NOT depended on is itself a claim that should
be re-checkable when the corpus moves.

**Every fact names the Annex J.3 item it answers.** J.3 is C23's own
numbered list of implementation-defined behavior, and a profile fact is
this implementation's ANSWER to one of its questions — so the column is
what makes the profile checkable against the standard rather than only
against the corpus. Where a fact answers no J.3 question the column says
so and why; `unsigned_wraps`, for instance, is standard-GUARANTEED
(§6.3.1.3p2) and is recorded only so the tier does not refuse it while
refusing signed overflow. (C23 also inserted a J.3.1 "General", shifting
C17's J.3.1-J.3.13 up by one — `docs/c23-spec-mirror.md` §6.)

| fact | expression | dep? | J.3 item | witness / why |
| --- | --- | :-: | --- | --- |
| `char_bit_8` | `CHAR_BIT == 8` | **yes** | **J.3.5(1)** | `pos_seal` memcpy's the 120-byte board into `uint64_t w[15]`; 120 bytes is 15 words only at 8-bit bytes (L199-201) |
| `int_32` | `sizeof(int) == 4` | **yes** | **J.3.14(1)** | `PACK_VM` packs `(uint32_t)(int)` into a `uint64_t`'s high half; the move-ordering key is exact only at 32 bits (L649-652) |
| `long_64` | `sizeof(long) == 8` | **yes** | **J.3.14(1)** | `TABLE_SIZE` and the node counters are `long` (L83, L496-497) |
| `twos_complement` | `INT_MIN == -INT_MAX - 1` | **yes** | **none — C23 DELETED it** | §6.2.6.2p6 NOTE 2 mandates it, and the deletion from J.3 is the mandate's auditable trace (C17's integers list had 5 entries, C23's `J.3.6` has 4). The signed-overflow UB boundary is stated against it |
| `char_signed` | `(char)-1 < 0` | **yes** | **J.3.5(5)** | see §4.1 — the in-bounds argument, not the values |
| `unsigned_wraps` | `(unsigned)-1 == UINT_MAX` | **yes** | — defined, §6.3.1.3p2 | `mix64`'s `x *= 0xff51…ULL` is deliberate defined wraparound (L192-193) |
| `int_to_uint32_modulo` | `(uint32_t)(-1) == 0xFFFFFFFFu` | **yes** | — defined, §6.3.1.3p2 | `PACK_VM` biases by `(uint32_t)(val) ^ 0x80000000u` (L649) |
| `uint_to_int_wraps` | `(int)0x80000000u == INT_MIN` | **yes** | **J.3.6(3)**, §6.3.1.3p3 | see §4.2 — implementation-defined in C23 exactly as in C17, so THIS profile is the pin |
| `little_endian` | `__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__` | no | — not in J.3 | see §4.3 — measured, deliberately not depended on |
| `arithmetic_right_shift` | `(-1 >> 1) == -1` | no | **J.3.6(4)**, §6.5.8p5 | see §4.4 — the corpus has ZERO signed right shifts |
| `pointer_64` | `sizeof(void *) == 8` | no | J.3.8 | 0 integer↔pointer casts, so no observable depends on the width |
| `long_long_64` | `sizeof(long long) == 8` | no | **J.3.14(1)** | reached only through `uint64_t`, which `<stdint.h>` fixes exactly |
| `short_16` | `sizeof(short) == 2` | no | **J.3.14(1)** | unused by the corpus |

Also recorded, on both hosts: `__STDC_VERSION__` is `202311L`, and
**`__STDC_IEC_60559_BFP__` is NOT defined** — neither host claims Annex F.
That is the measured gate on the memo's float rung R4, unchanged, and it
is a property of both hosts rather than of the one that happened to be
asked.

## 4 The four facts worth an argument

### 4.1 `char_signed` is depended on for the IN-BOUNDS argument, not for a value

The board is `char b[120]` and every byte in it is ASCII below 128, so no
comparison against `'R'`, `'q'`, `'.'`, `'\n'` or `' '` changes meaning
with the sign. But `gen_moves` indexes a 128-entry table by a board byte:

```c
unsigned char cq = CLS[(int)p->b[j]];
```

Under signed `char` that index is in `[-128, 127]`, and the argument that
it never goes negative is a fact about the board's CONTENTS, not about
the type. The model has to make that argument either way; the profile is
what says which of the two versions of it applies. So: depended on, and
the dependence is on the proof obligation rather than on an answer.

**This is also the one fact that excludes a host.** Linux AArch64 has
UNSIGNED `char`, which is exactly the divergence the architecture memo
flagged. It is not one of the two development hosts, and §5 shows the
guard rejecting it by name.

### 4.2 `uint_to_int_wraps` — the standard does NOT guarantee this, so the profile must

`VM_VAL` recovers the signed move value from the packed key:

```c
#define VM_VAL(k)  ((int)((uint32_t)((k) >> 32) ^ 0x80000000u))
```

The `(int)` conversion receives an out-of-range `uint32_t` for every
negative move value.

> **CORRECTED at M2 inch 2.** This section previously said *"C23 §6.3.1.3
> mandates the two's-complement result; under C17 it was
> implementation-defined,"* and concluded that the `-std=c23` pin was
> load-bearing for the move ordering. **Both halves were wrong.**
> Verified against N3220: **§6.3.1.3p3 is word-for-word identical to C11
> and C17** — "either the result is implementation-defined or an
> implementation-defined signal is raised" — and **`J.3.6(3)` still lists
> the behavior as implementation-defined.** C23 changed signed
> REPRESENTATION (§6.2.6.2p6 NOTE 2), not this conversion rule.

So the corpus's move ordering — the thing the fidelity gate compares
first — rests on **implementation-defined behavior that no standard
version guarantees.** That does not make it fragile; it makes it exactly
the kind of fact this profile exists for. Both hosts wrap, the fact is
`depended_on`, and a third host that raised a signal instead would fail
`harness/c_profile_probe.py --check` loudly.

**The correction makes the pin MORE important, not less.** Under the old
(false) reading, `-std=c23` was the guarantee and the profile entry was a
belt-and-braces record. Under the true reading the profile entry is the
ONLY thing standing between the move ordering and a host that answers
J.3.6(3) differently. An appeal to the standard here would have silently
withdrawn the check.

Note the asymmetry with `int_to_uint32_modulo` one row above: conversion
TO an unsigned type has been defined by modulo arithmetic since C89
(§6.3.1.3p2) and has no J.3 entry at all. Only the conversion back was
ever in question — and it still is.

### 4.3 `little_endian` is measured and deliberately NOT depended on

`pos_seal` hashes the board by memcpy'ing it into `uint64_t w[15]` and
folding the words, so **the hash value `h` genuinely differs between a
little-endian and a big-endian host.** A naive reading would make
endianness a depended-on fact. It is not, and the corpus argues why in
its own comments:

* `pos_eq` uses `a->h == b->h` only as a constant-time fast reject in
  front of a full `memcmp` on the 120 board bytes plus every other field
  (L209-217) — the comment says it verbatim: *"a derived-value fast
  reject, never a substitute."*
* the bucket layout `h` induces is unobservable, because keys are unique,
  chain hits are confirmed by `pos_eq`, and iteration order lives in a
  separate insertion-order list (L403-405).

So `h` is not observable, and a host that computed different hashes would
produce identical transcripts. Recorded as measured-not-depended-on with
the reason, because that reason is a property of TODAY's `pos_seal` and
would have to be re-checked if the hash ever reached an output.

### 4.4 `arithmetic_right_shift` is not depended on — there are no signed right shifts

The memo listed right-shift-of-a-negative among the implementation-defined
facts to pin. Measured on today's corpus: **all six `>>` sites are on
`uint64_t` operands** — three in `mix64` (L192-194) and three in
`VM_VAL`/`VM_MOVE` (L652-653). There is no signed right shift to have an
opinion about. The fact is probed anyway so the claim stays checkable.

The `<<` side is likewise clean: the shifts are on `uint64_t` or on
non-negative small `int`s (`1 << 12`, `4 << pi` for `pi` in 0..5), so no
signed left-shift overflow.

## 4a STRUCTURE LAYOUT — natural alignment, DECLARED (`natural_alignment`)

C23 §6.7.2.1p18 leaves the padding between structure members, and after the
last one, **implementation-defined**. The tier needs it: `torLayout` cannot
size a `struct` or answer `offsetof` without a rule, and **54 of 300
`gcc.c-torture` tests were refused for `no layout for declared type` with
`struct`/`union` the entire remainder** once the arrays and typedefs were
handled (`docs/backlog/c.md` 2026-08-25-c-25).

`2026-08-25-c-25` refused to compute one, and the refusal was right for the
reason it gave — **a layout computed from an UNDECLARED rule is a fabricated
layout, the same defect as a fabricated column one abstraction up.** The
answer is not to keep refusing; it is to stop the rule being undeclared.
That is what this file already does for `CHAR_BIT`, `sizeof(int)` and
`sizeof(long)`, which are implementation-defined in exactly the same sense.

**THE RULE, pinned:**

* every member is placed at the next offset satisfying **its own**
  alignment, which for a scalar is its size and for an array is its
  element's;
* members are **not reordered** — §6.7.2.1p18 requires increasing addresses
  in declaration order, so this half is the standard's and not the
  profile's;
* the aggregate's alignment is its **widest member's**, and its size is
  rounded **up** to that alignment, so arrays of it stay aligned;
* a `union`'s members all sit at offset 0; its size is the largest member's,
  rounded up to the widest member's alignment.

**PROBED, not assumed.** `natural_alignment` is a `depended_on` fact with a
`_Static_assert` expression like every other, and both profiled hosts fold
it true:

```
_Alignof(int) == 4 && sizeof(struct { char c; int i; }) == 8 &&
_Alignof(struct { char c; int i; }) == 4 && sizeof(struct { char a; char b; }) == 2
```

The four conjuncts are chosen to pin the four halves of the rule: a scalar's
alignment, the padding BEFORE a member, the aggregate's own alignment, and
the absence of padding where none is needed.

> **A profile does not make an implementation-defined choice go away; it
> makes it ATTRIBUTABLE. The objection to a fabricated layout was never
> "computing one is wrong" — it was "computing one from a rule nobody wrote
> down is wrong", and the distance between those is one probed fact.**

**J.3 index**: J.3.9(1), the alignment requirements of structure and union
members and the padding between them. **HONEST LIMIT**: this is the SysV /
AAPCS shape. A host that packs differently — or a translation unit using
`_Alignas`, `#pragma pack` or bit-fields — is outside the pin, and the tier
refuses rather than guessing: none of the three is in the modelled
vocabulary, so they arrive as `unsupported` and never as a wrong offset.

## 5 The guard

The `#guard` of the C lane. Any host, in under a second, without running
anything on it:

```
$ python3 harness/c_profile_probe.py --check docs/c-profile.json \
      --target x86_64-unknown-linux-gnu
c_profile_probe: x86_64-unknown-linux-gnu satisfies all 8 depended-on facts

$ python3 harness/c_profile_probe.py --check docs/c-profile.json \
      --target aarch64-unknown-linux-gnu
c_profile_probe: aarch64-unknown-linux-gnu FAILS the abstract profile on 1 depended-on fact(s):
  char_signed              (char)-1 < 0  (required True, host says False)
      the board is char b[120] and CLS[(int)p->b[j]] indexes a 128-entry
      table by it (L346); every board byte is ASCII < 128, so no VALUE
      changes — but the in-bounds ARGUMENT is a function of the sign
```

A failure names the fact, the expression, both answers, and why the
corpus cares. That is the difference between a gate and an assertion.

**The instrument refuses rather than guesses.** A `_Static_assert` that
fails is the NEGATIVE answer; anything else — an unknown triple, a
missing header — is an instrument fault and exits non-zero saying so,
because reporting a broken probe as "the host differs" would be a silent
wrong answer of exactly the kind the covenant forbids.

## 6 What this means for the envelope

`profile_id` stays a first-class envelope field (memo §4.3) and the
ingester still refuses a mismatch loudly. What changes is what it
identifies: **not a machine, but the schema version plus the flag pin.**
Two hosts that both satisfy the schema and run the same
`-std=c23 -D_FORTIFY_SOURCE=0` produce the same envelope, and that is now
a checked property rather than a hope.

## 7 Honest limits

* **Eight depended-on facts is a claim about TODAY's corpus.** Every
  witness cites a line. When `sunfish.c` moves, `harness/c_construct_census.py
  --compare` says whether the surface moved, and the witnesses here are what
  has to be re-read if it did.
* **The schema covers implementation-defined facts, not the whole
  profile.** Alignment, struct padding and `_Alignof` are not probed;
  they become depended-on the moment the memory model's `effTy` walks a
  struct, which is milestone M3, not M1.
* **Nothing here is verified on the Linux box itself.** Cross-target
  constant folding certifies the ABI clang believes that target has. That
  is the right instrument for ABI facts and the wrong one for anything
  environmental — the ASan channel in particular is still DESIGNED and
  unverified, and still owes a run on real hardware.
* **`__STDC_IEC_60559_BFP__` being undefined on both hosts is recorded,
  not solved.** R4 stays gated.
