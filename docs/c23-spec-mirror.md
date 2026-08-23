# The spec-mirror convention — reading the C surface beside N3220

**Status: the convention, adopted at M2 inch 2 on Thomas's ruling** —
*"our lean surface for C will read like a Lean translation of the C23
spec — one might read the two documents side by side and everything makes
sense."*

This document is the mirror's rulebook: which document is cited, in what
form, how the files are laid out against the standard's clause structure,
and what Annex J contributes. Everything numbered here was **verified
against the fetched N3220 text**, with C17 (N2310) beside it for the
"did it move?" questions. Nothing is quoted from memory, and three of
this project's previously published claims did not survive the check (§4).

---

## 1 The document that is cited

**ISO/IEC 9899:2024 is not quotable and not freely available. N3220 is.**

N3220 is WG14's final working draft of C23. Its clause and paragraph
numbering matches the published standard, and it is downloadable from
open-std.org, so a reader can hold it beside the Lean sources — which is
the entire point of the convention. Citations therefore read

    -- C23 (N3220) §6.5.6p7: integer division discards the fractional
    -- part — "truncation toward zero" (footnote 104).

**Cite and paraphrase; never transcribe.** This is the CompCert and
Cerberus convention and it is a licensing constraint as much as a style
one: the standard's text is copyrighted, the clause NUMBERS are not.
A citation is a pointer for a human holding the other document, plus a
one-line paraphrase so the Lean file stands alone. Long verbatim quotes
do not appear in this repository, and no part of N3220 is vendored.

### 1.1 The citation's three jobs

1. **Locate** — clause and paragraph, precise enough to open the PDF at
   the right place (`§6.5.6p7`, not `§6.5`).
2. **Paraphrase** — one line, in the repository's own words, so a reader
   without the draft still knows what the definition claims.
3. **Classify** — for anything the model REFUSES, name the Annex J entry
   (§3). A refusal that cannot name its J.2 index is a refusal nobody can
   check against the standard's own checklist.

### 1.1a The edition tag — so a scanner can classify without reading prose

A surface that documents a renumbering necessarily CONTAINS superseded
numbers, and a citation instrument that cannot tell them apart will
report the documentation as drift. Two rules make every citation
machine-classifiable:

1. **An untagged `§` inside `LeanModels/C/C23/` is C23 (N3220)** by
   construction.
2. **A citation to a superseded edition carries the edition tag
   immediately before the section sign** — `C17 §6.5.5`, never a bare
   `§6.5.5` and never `C17: §6.5.5` with punctuation between.

A third case is not an ISO citation at all: `docs/c23-spec-mirror.md §4.2`
and the like are INTERNAL document references, and they are always
preceded by the document's filename or an explicit "the design's". An
instrument should exclude a `§` whose line carries a `docs/….md` token
before it.

This matters concretely: `LeanModels/C/C23/Value.lean` states the C17
numbers for division and shift *on purpose*, in the warning that tells a
reader carrying a citation in from C17 what moved. Those are correct
documentation, not stale citations, and the tag is what says so.

### 1.2 What becomes what

| in the standard | in the surface |
| --- | --- |
| a "shall" about semantics | a **theorem** |
| a constraint violation | a **refusal** (the ingester's, or `unsupported`) |
| "the behavior is undefined" | a **refusal with a J.2 cause** — never a value |
| "the behavior is unspecified" | a **J.1 register entry** (§5) — decided explicitly, never silently |
| "implementation-defined" | a **profile fact**, mapped to its J.3 item (§6) |

---

## 2 Layout — the files mirror the clause structure

Modules and the sections inside them follow the standard's order, so the
two documents can be read in parallel rather than cross-referenced.

| clause | surface |
| --- | --- |
| §6.2.5 Types, §6.2.6 Representations | `C23/Value.lean` |
| §6.3 Conversions | `C23/Value.lean` (arithmetic), `C23/Memory.lean` (§6.3.2.1 decay, §6.3.2.3 pointers) |
| §6.2.4 Storage durations, §6.2.6.1 Representations | `C23/Memory.lean` |
| §6.5 Expressions, subclause by subclause | `C23/Expr.lean` |
| §6.8 Statements and blocks | `C23/Stmt.lean` |
| §7.23.6.1 `fprintf` | the `printf` slice, at its rung |
| Annex J.2 | the UB taxonomy, everywhere a refusal is raised |

Within a file, definitions appear in the standard's paragraph order where
that is feasible. Where Lean's dependency order forces a different
sequence, the section headers still carry the clause numbers, so the
reading order is recoverable even when the elaboration order is not.

**The version namespace is part of the mirror.** `LeanModels.C.C23` is
the C23 surface; `LeanModels.C` is the version-neutral envelope substrate.
§4's table is why that boundary is a directory rather than a flag.

---

## 3 Annex J.2 — the UB taxonomy, made official

`docs/c-semantics-design.md` §3.2 armed eleven UB classes before this
convention existed. Annex J.2 is the standard's own list of the same
thing, and in C23 **it is numbered** — entries `(1)` through `(221)`.
(In C17 and C11 it was an unnumbered bulleted list, so `J.2(35)` is a
citation form C23 made possible and earlier revisions did not.)

Every refusal the model raises names its J.2 index and its normative
clause. The index is the checklist coordinate; the clause is where the
rule actually lives.

| refusal | J.2 | normative |
| --- | --- | --- |
| signed overflow / exceptional condition | **J.2(35)** | §6.5.1p5 |
| division or remainder by zero | **J.2(41)** | §6.5.6p6 |
| shift count negative or ≥ width | **J.2(48)** | §6.5.8p3 |
| `<<` of a negative signed value, or signed `<<` overflow | **J.2(49)** | §6.5.8p4 |
| indirection through an invalid pointer value | **J.2(39)** | §6.5.4.2 |
| object referred to outside its lifetime | **J.2(9)** | §6.2.4 |
| value of a pointer to a dead object is used | **J.2(10)** | §6.2.4p2 |
| array subscript out of range | **J.2(46)** | §6.5.7 |
| pointer arithmetic leaving the object | **J.2(43)**, **(44)**, **(45)** | §6.5.7p9, p10 |
| automatic object with indeterminate representation | **J.2(11)** | §6.2.4 |
| non-value representation read by a non-character lvalue | **J.2(12)** | §6.2.6.1p5 |
| **`malloc`ed object used before it is written** | **J.2(185)** | §7.24.3.6p2 |
| `realloc`'s bytes beyond the old size | **J.2(186)** | §7.24.3.7 |
| effective-type / strict-aliasing violation | **J.2(36)** | §6.5.1p6, p7 |
| value of a freed pointer is used | **J.2(183)** | §7.24.3 |
| freeing an unmatched or already-freed pointer | **J.2(184)** | §7.24.3.3, §7.24.3.7 |
| unsequenced side effects on the same scalar object | **J.2(34)** | §6.5.1p2 |
| copy between overlapping objects by a library function | **J.2(99)** | §7.26.2.1p2 |
| invalid argument value to a library function | **J.2(107)** | §7.1.4p1 |
| `longjmp` into a terminated environment | **J.2(126)** | §7.13.2.1p2 |

### 3.1 Two entries the design doc conflated, now split

`J.2(11)` names objects with **automatic** storage duration. Allocated
storage has its **own** entry, `J.2(185)`. The byte lattice refuses both,
but they retire differently and are recorded apart — the automatic one is
a language rule, the allocated one a library rule.

### 3.2 Three gaps, recorded rather than papered over

The annex does not cover everything the model refuses, and inventing an
index would be worse than admitting the gap. Each was established by
exhaustive search of all 221 entries, not by assumption:

1. **`realloc(ptr, 0)` has no J.2 entry.** C23 made it undefined —
   §7.24.3.7p3, "or if the size is zero, the behavior is undefined" — but
   Annex J was not updated to match. Cite the clause directly. *(C17 did
   not have this rule at all; there, zero size fell under the family-wide
   implementation-defined rule.)*
2. **`aligned_alloc`'s uninitialized storage has no entry**, though
   `malloc`'s does (`J.2(185)`). Clause-citable, not J-citable. The
   corpus does not call `aligned_alloc`, so nothing depends on it today.
3. **A pointer's representation after its object dies is not in J.1.**
   It is not unspecified behavior: §6.2.4p2 makes the representation
   *indeterminate*, and USING it is UB via `J.2(10)`/`J.2(11)`.

### 3.3 A defect in N3220 itself

**`J.2(125)` cross-references §7.13.2.1, but the rule it names — the
contexts in which `setjmp` may appear — lives at §7.13.1.1p4/p5.** The
annex's back-reference points at `longjmp`'s subclause instead of
`setjmp`'s. Recorded here because a lane that followed the annex would
land on the wrong clause and conclude the rule was missing. Cite
§7.13.1.1p4/p5.

---

## 4 What the check refuted

Three claims this project had already published did not survive
verification against N3220. All three are corrected in place; they are
listed together here because each is the same failure — a plausible
number carried from memory or from an older revision.

### 4.1 C23 did NOT define out-of-range conversion to a signed type

`docs/c-semantics-design.md` §1.2 and `LeanModels/C/C23/Value.lean` both
claimed that C23 §6.3.1.3 mandates two's-complement wraparound when
converting an out-of-range value to a signed type, and that the
`-std=c23` pin was therefore load-bearing.

**It does not. N3220 §6.3.1.3p3 is word-for-word identical to C11 and
C17**: "either the result is implementation-defined or an
implementation-defined signal is raised." Confirmed twice over by
**J.3.6(3)**, which still lists it as implementation-defined.

What C23 *did* change is signed **representation**, and the NORMATIVE
sentence is **§6.2.6.2p2**: C23 fixes the sign bit's value, where C17's
same paragraph offered three representations (sign-and-magnitude, ones'
complement, two's complement). §6.2.6.2p6 NOTE 2 is the confirming
change-history note, not the rule. The auditable trace is that **C17's
integers list in J.3 had five entries and C23's J.3.6 has four** — the
deleted item is the sign-representation one. Representation mandated; the
conversion rule untouched.

**Consequence for the version boundary, and it is the reason this
correction was worth chasing:** the edition-sensitive definition in
`Value.lean` is **`IntTy.minVal`**, not `convert`. `minVal`'s
`-(2^(bits-1))` is a C23 commitment; under C17 it is wrong for two of the
three permitted representations. `convert` is implementation-defined in
every edition and is pinned by the profile. *(The family-architecture
lane verified this independently against both drafts and corrected its
§1.3 to match.)*

**Consequence for the model, and it is a real one.** `convert` is not
implementing a standard mandate. It is resolving an
**implementation-defined** behavior, which under this project's own
discipline belongs to the PROFILE and must be measured on every host
rather than asserted. `VM_VAL` (sunfish.c L652) depends on it, so it is
depended-on implementation-defined behavior — exactly the thing
`docs/c-profile.md` exists to pin. See §6.

### 4.2 C23 renumbered §6.5 and §6.8 — every operator citation shifts by one

N3220 inserts a new **§6.5.1 "General"** (absorbing C17's §6.5 preamble),
pushing all seventeen operator subclauses down by one. The same editorial
pattern applies at §6.8, §6.7, §5.1.2 and Annex J.3.

| C17 | C23 (N3220) | |
| --- | --- | --- |
| §6.5 preamble | **§6.5.1** General | sequencing p2–p3, exceptional condition p5, effective type p6–p7 |
| §6.5.1 primary | **§6.5.2** | |
| §6.5.2 postfix | **§6.5.3** | subscript **.2**, calls **.3**, members **.4**, postfix `++` **.5**, compound literal **.6** |
| §6.5.3 unary | **§6.5.4** | prefix `++` **.1**, `&`/`*` **.2**, unary arithmetic **.3**, `sizeof` **.4** |
| §6.5.4 cast | **§6.5.5** | |
| §6.5.5 multiplicative | **§6.5.6** | |
| §6.5.6 additive | **§6.5.7** | |
| §6.5.7 shift | **§6.5.8** | |
| §6.5.8 relational | **§6.5.9** | |
| §6.5.9 equality | **§6.5.10** | |
| §6.5.10–12 bitwise AND/XOR/OR | **§6.5.11–13** | |
| §6.5.13 logical AND | **§6.5.14** | |
| §6.5.14 logical OR | **§6.5.15** | |
| §6.5.15 conditional | **§6.5.16** | |
| §6.5.16 assignment | **§6.5.17** | General **.1**, simple **.2**, compound **.3** |
| §6.5.17 comma | **§6.5.18** | |
| §6.8.1 labeled | **§6.8.2** | new §6.8.1 General; compound **.3**, expression **.4**, selection **.5**, iteration **.6**, jump **.7** |
| §5.1.2.2.3 program termination | **§5.1.2.3.4** | "reaching the `}` that terminates `main` returns 0" |

Note the sub-level shifts under *postfix* (because §6.5.3.1 "General" was
inserted) but **not** under *unary*.

### 4.3 The library clauses moved, and one move is a trap

| header | C17 | C23 |
| --- | --- | --- |
| `<setjmp.h>` | 7.13 | **7.13** (unchanged) |
| `<stdio.h>` | 7.21 | **7.23** |
| `<stdlib.h>` | 7.22 | **7.24** |
| `<string.h>` | 7.24 | **7.26** |

**C17's 7.24 is `<string.h>`; C23's 7.24 is `<stdlib.h>`.** A stale
`§7.24.x` citation does not fail — it silently retargets from string
handling to general utilities. That is the sharpest argument this project
has for versioning the surface by directory.

Within `<stdlib.h>`, `malloc` also moved **inside** its subclause: C23
added `free_sized` (7.24.3.4) and `free_aligned_sized` (7.24.3.5), so
`malloc` is **§7.24.3.6** (C17: 7.22.3.4) and `realloc` **§7.24.3.7**.
Within `<string.h>`, a new "Introduction" at §7.26.5.1 shifts every
search function by one (`memchr` **§7.26.5.2**, `strtok` **§7.26.5.9**).

`fprintf` = **§7.23.6.1**, format mini-language at p3–p15 — the one
number this project already had right.

---

## 5 The J.1 register — unspecified behavior, decided explicitly

Annex J.1 lists behaviors that are neither undefined nor
implementation-defined: the standard permits several outcomes and
requires no record of which. **In C23 J.1 is numbered**, `(1)`–`(63)`.

A definitional interpreter cannot leave these ambient. Three responses
are legitimate, and the register records which was taken for every item
the tier touches:

* **pick-and-declare** — choose an outcome, record it as a MODELING
  CHOICE, distinct from a profile fact (a profile fact is measured on a
  host; a modeling choice is decided by this project);
* **refuse** — decline the program;
* **measure** — census that the corpus never depends on the difference.

### 5.1 Thomas's ruling, and the shape it forces

> **"A program is only correct if it would be correct under any argument
> evaluation order. Since you don't know which the hardware is going to
> choose."**

This is the register's DEFAULT policy, and it is stronger than
pick-and-declare. Concretely:

1. **The evaluation order is an explicit PARAMETER of the semantics**,
   declared like the profile and never ambient. The interpreter stays
   deterministic *given* the parameter, so the ∃-fuel threshold form
   survives untouched.
2. **The canonical order is how witnesses are extracted, never what is
   claimed.** Left-to-right is the canonical choice; scoring a suite runs
   at the canonical order because a scoreboard needs one run, not
   `n!` of them.
3. **Correctness theorems quantify over the parameter**: *∀ order, the
   same observable outcome.* Per site, the obligation discharges cheapest
   first — (i) the interference census, (ii) a proof of invariance.
4. **A suite test whose expected output depends on one particular order
   is, under this ruling, an INCORRECT PROGRAM.** The verdict system gets
   an order-dependent class; it is not a MATCH even when the reference
   compiler's order happens to agree.

### 5.2 The partition does half the work

Much apparent order-dependence is not J.1 at all — it is UB, and refusing
is the answer. The line, in the standard's own terms:

* **§6.5.1p2 — unsequenced**: two side effects on the same scalar object,
  or a side effect and a value computation using it, with no sequencing
  between them → **undefined**, `J.2(34)`, REFUSE. Not a quantifier.
* **§6.5.3.3p10 — indeterminately sequenced**: a function call's argument
  evaluations do not interleave, but either order may be chosen →
  `J.1(16)`. **This is exactly the ∀-order domain.**
* **§6.5.14p4, §6.5.15p4, §6.5.16, §6.5.18** — `&&`, `||`, `?:` and `,`
  are sequence points and are *not* in the domain at all.

### 5.3 The register

| J.1 | item | clause | decision | status |
| ---: | --- | --- | --- | --- |
| **(16)** | order of evaluation of a call's function designator, arguments and their subexpressions | §6.5.3.3 | **∀ order** (Thomas's ruling); canonical = left-to-right for witness extraction | domain measured: **7 sites** |
| **(15)** | order of evaluation of subexpressions, and the order in which side effects take place | §6.5.1 | **∀ order**, same discipline | **0** operators with effects in both operands |
| **(10)** | value of padding bytes when storing into a structure | §6.2.6.1 | **modeling choice: `indet`** — the byte lattice already has the value, and reading one refuses | armed, fires on 0 corpus sites |
| **(13)** | value of padding bits in an integer representation | §6.2.6.2 | not reachable — the value model stores a mathematical integer, never a representation | not applicable |

**The interference census, measured** (`harness/c_construct_census.py`,
rows `call_arg_order_domain` / `call_arg_two_effects` /
`unsequenced_operands_both_effectful`):

* **7** of 320 call sites have two or more arguments with an effect in
  any argument — the entire J.1(16) domain:
  `map_find_h:L428`, `fmt_move:L978`, `printf:L1301`,
  `set_knob:L1317/1331/1363/1369`.
* **0** call sites have two effectful arguments.
* **0** binary operators have an effect in both operands (of 891 with
  unsequenced operands, excluding the four sequence-point operators).

At all seven the effectful argument is a nested call and its siblings are
address computations or plain scalar reads, so the per-site discharge is
"can this callee write what these siblings read" — an effect-summary
question that belongs to the calls inch, priced at **7 sites rather than
320**.

**REACHABILITY, and it decides when the discharge can be attempted.** "The
effectful argument is a nested call" is not only the shape of the domain —
until inch 5's handler repair it was also the reason the domain could not
be evaluated at all. A `CallHandler` taking UNEVALUATED arguments had no
evaluator for them, so every nested call to a defined function refused,
and a `∀ order` theorem stated then would have quantified over **seven
refusals**: true, and evidence of nothing. The repair (`evalArgs` inside
the expression layer's mutual block; the handler takes `List CVal`) makes
the domain reachable, and only then is the obligation worth stating. This
is `2026-08-23-c-5`'s law applied to a quantifier: **a claim that cannot
fail is not a check.**

**Items not yet reached** are not in the register. An item enters when an
inch touches it, and it is decided then — never silently.

---

## 6 Annex J.3 — the profile, mapped

`docs/c-profile.md` pins the implementation-defined behavior the corpus
depends on. J.3 is the standard's own list of that behavior, numbered and
restarting per subclause. C23 inserted a new J.3.1 "General", shifting
C17's J.3.1–J.3.13 up by one.

| profile fact | J.3 item | clause |
| --- | --- | --- |
| `char_bit_8` | **J.3.5(1)** — the number of bits in a byte | §3.7 |
| `char_signed` | **J.3.5(5)** — which of `signed char`/`unsigned char` matches plain `char` | §6.2.5, §6.3.1.1 |
| `int_32`, `long_64` and the type ranges | **J.3.14(1)** — the values of the `<limits.h>`/`<stdint.h>` macros *(no single J.3.6 entry covers integer sizes)* | §5.2.5.3, §7.22 |
| `arithmetic_right_shift` | **J.3.6(4)** — "the results of some bitwise operations on signed integers", a catch-all that does not name shifts; the precise cite is normative | **§6.5.8p5** |
| **`conv_to_signed_wraps`** *(new — see §4.1)* | **J.3.6(3)** — the result of converting an integer to a signed type when unrepresentable | §6.3.1.3p3 |

**J.3.6 "Integers" has exactly four entries in C23**: (1) extended
integer types that exist; (2) the rank of an extended integer type; (3)
the result of, or signal raised by, an unrepresentable conversion to a
signed type; (4) the results of some bitwise operations on signed
integers. C17's corresponding list had five — the deleted entry is the
sign-representation one, and its deletion is the auditable trace of C23's
two's-complement mandate.

**J.3.5(1) points at §3.7, the clause-3 *definition* of "byte"**, not at
`<limits.h>` — worth knowing, because the obvious place to look is the
wrong one.

---

## 7 The coverage-by-clause instrument

Specced here, built at its rung. **Not built yet**, and saying so is the
point: an instrument with nothing to scan is a stub, and the surface
currently cites a handful of clauses.

`harness/c_clause_coverage.py`:

* scan `LeanModels/C/C23/**.lean` for citations matching the §1
  convention, plus the J.1/J.2/J.3 indices;
* emit the conformance map against N3220's own table of contents — per
  clause: cited / modeled / refused / absent;
* drift-guarded like every instrument in this repository: a `--check`
  mode that exits non-zero when the committed map and a fresh scan
  disagree, and a self-test that a malformed citation is REJECTED rather
  than silently skipped;
* one row per clause in clause order, deterministic output.

That map is the scoreboard to read beside N3220, and it is the honest
counterweight to a suite score: a suite says "agrees with what these
projects test", and the clause map says "and here is which of the
standard the surface has actually spoken about."
