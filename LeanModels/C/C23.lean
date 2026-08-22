import LeanModels.C.Ast
import LeanModels.C.C23.Value
import LeanModels.C.C23.Memory

/-!
# The C23 surface (`LeanModels.C.C23`)

**One namespace per language VERSION.** `lean-surfaces` is a family of
versioned language surfaces, and a user proving about C chooses which C.
This namespace is ISO/IEC 9899:2024 — cited throughout as **N3220**, the
freely available final working draft, whose numbering is stable and
quotable where the published standard's text is not.

## The boundary, and why it falls here

`LeanModels/C/` holds the **version-neutral substrate**: `Ast.lean`,
`Json.lean`, `Load.lean` — the `c-0.1` envelope and its ingestion. An
ingested translation unit is the same first-order term whichever C
version you go on to reason about; the node vocabulary is clang's, not
any standard's, and `docs/c-envelope-schema.md` is versioned on its own
schedule (`c-0.1`).

`LeanModels/C/C23/` holds everything that assigns **MEANING**. That is
where the versions actually differ, and the differences are not cosmetic
— each of these was verified against N3220 with C17 (N2310) beside it:

| what changed | C17 | C23 (N3220) |
| --- | --- | --- |
| §6.5's subclause numbering | `6.5.5` multiplicative … | **`6.5.6`** — a new `6.5.1 General` shifts all 17 operator subclauses |
| §6.8's numbering | `6.8.1` labeled … | **`6.8.2`** — same pattern, new `6.8.1 General` |
| signed representation | sign-magnitude / ones' / two's | **two's complement mandated** (6.2.6.2p6 NOTE 2) |
| `J.3` integers list | 5 entries | **4** — the sign-representation item was DELETED, which is the mandate's auditable trace |
| Annex J.1/J.2/J.3 | unnumbered bullets | **numbered** `(1)…(63)`, `(1)…(221)` — so `J.2(35)` is a C23 citation form and not a C17 one |
| `realloc(p, 0)` | implementation-defined | **undefined** (7.24.3.7p3) |
| library clause numbers | `<string.h>` = 7.24 | **`<stdlib.h>` = 7.24** — the same number, a different header |
| effective-type wording | "signed or unsigned type corresponding to" | "**underlying type of** the effective type" (6.5.1p7) |

The last two are the reason this boundary is a directory and not a
comment. A stale `7.24.x` citation does not fail — it silently retargets
from string handling to general utilities. A surface that cannot say
which C it means cannot notice that.

**What is NOT claimed**: nothing here models C17. The table above is the
evidence that a C17 surface would be a different set of files, not a flag
on these ones; deciding whether that surface is a copy or a delta is a
separate architecture question with its own census.

Milestone M2 builds this namespace inch by inch
(`docs/c-semantics-design.md` §7).

* **Inch 1 — `C23/Value.lean`**: §6.2.5 types, §6.3.1 conversions, and
  the arithmetic where unsigned wraps and signed refuses.
* **Inch 2 — `C23/Memory.lean`**: §6.2.4 storage durations, §6.2.6.1 the
  byte lattice, §6.3.2 pointers and decay, §6.5.3-§6.5.4 the operators
  that make and use them, §7.24.3 allocation. Instantiated on the shipped
  corpus in `Examples/c/sunfish/memory.lean`.
-/

namespace LeanModels.C.C23

open LeanModels.C (Envelope)

/-! ## The version gate

The envelope records the `profile_flags` it was extracted under
(`docs/c-envelope-schema.md` §1), and `-std=c23` is one of them. A
translation unit extracted under a different `-std` is a different
program — the same source text, parsed by different rules — so the C23
surface states what it accepts rather than assuming it.

This is a GATE, not decoration: it can see its number
(`Envelope.profileFlags`), and the `#guard`s below perturb it in both
directions. -/

/-- The `-std=` flag this surface requires in an envelope's profile. -/
def stdFlag : String := "-std=c23"

/-- Was this envelope extracted under the C23 rules this surface models? -/
def acceptsEnvelope (e : Envelope) : Bool :=
  e.language == "c" && e.profileFlags.contains stdFlag

end LeanModels.C.C23
