import LeanModels.Ada

/-!
# M1's round-trip guards (`Examples.ada.report`)

The Ada lane's M1: an Ada compilation ingests, source → libadalang →
`ada-0.1` envelope → a literal Lean term, and the term answers structural
questions **another instrument already knows**. Two instruments, two paths,
one answer. **There is no semantics here and none exists.**

Two fixtures, chosen because the hazard census picked them rather than
because they were convenient (`docs/backlog.md` §L74, §L75):

* **`report`** — the ACATS `Report` package, the unit every executable test
  depends on. One FILE holding TWO compilation units, which is
  `docs/ada-envelope-schema.md` §0.3's one-envelope-is-one-COMPILATION point
  met in the tier's first artifact.
* **`b371001`** — a four-file class-B test with SIX units including CHILD
  units. `B3710010.A` holds `B371001_1`, `B371001_1.Child_1` and
  `B371001_0`, and its own name is **none of them**: the top-unit hazard
  that afflicts one ACATS file in seven, in the first multi-file fixture.

`Report`'s subprogram numbers were written into `docs/ada-charter.md` §5.7
from the SOURCE, before any parser had been built; libadalang then reported
them. The markings were checked against the ACAA's own `SUMMARY` tool before
this file existed (`harness/ada_round_trip.py`). Non-vacuity is checked the
way the C lane checks it: flipping a count makes Lean report the failing
expression, and that was run.
-/

namespace Examples.ada.report

open LeanModels.Ada

/-! ## The fixtures

`maxRecDepth` is raised for the LITERAL, not for a proof: `report.a` is 591
lines of Ada whose tree carries 398 nodes in its specification alone, and a
first-order term of that depth is what ingestion produces by construction.

`load_ada_program` reads `docs/ada-construct-census.json` at elaboration time
and REFUSES any kind outside it, so **these two commands succeeding is
itself the same-set vocabulary check** `docs/ada-envelope-schema.md` §3
promised — enforced by the ingester rather than only by a harness. -/

set_option maxRecDepth 1000000 in
load_ada_program report from "Examples/ada/report/report.json"

set_option maxRecDepth 1000000 in
load_ada_program b371001 from "Examples/ada/b371001/b371001.json"

/-! ## The envelope's own claims -/

#guard report.schemaVersion == "ada-0.1"
#guard report.language == "ada"
#guard report.languageVersion == "Ada2012"
#guard report.profileId == "ada-profile-0.1"
#guard report.sourceFiles.size == 1
#guard report.sourceFiles[0]!.path == "acats42/support/report.a"

-- The ACATS ZIP delivery ships CRLF, and the ACAA's own SUMMARY tool dies
-- on it. The envelope records what the extractor SAW.
#guard report.sourceFiles[0]!.lineEndings == "crlf"

/-! ## ONE FILE, TWO COMPILATION UNITS

`docs/ada-envelope-schema.md` §0.3: an Ada envelope is one COMPILATION, not
one file. `report.a` carries the package specification and its body. -/

#guard report.compilationUnits.size == 2
#guard report.unitNames == #[some "Report", some "Report"]
#guard report.compilationUnits[0]!.kind == some "PackageDecl"
#guard report.compilationUnits[1]!.kind == some "PackageBody"
#guard report.compilationUnits.all (·.file == 0)

/-! ## The unit `Report`'s own shape

Predicted from the source in `docs/ada-charter.md` §5.7 before a parser
existed; reported by libadalang afterwards. -/

-- 15 subprogram declarations: six reporting procedures, six
-- optimizer-defeating identity functions, `Equal`, `Legal_File_Name`
-- and `Time_Stamp`.
#guard report.compilationUnits[0]!.decl.countKind "SubpDecl" == 15

-- `subtype File_Num is Integer range 1 .. 5;`
#guard report.compilationUnits[0]!.decl.countKind "SubtypeDecl" == 1

-- Nothing in `Report` is outside the census vocabulary.
#guard report.unsupportedCount == 0

-- `Report` parses clean: it is not a class-B test.
#guard report.diagnostics.isEmpty

-- `Report` carries no ACATS markings — it is support code, not a test.
-- Recorded honestly rather than as an agreement: the round-trip gate calls
-- this comparison VACUOUS for the same reason.
#guard report.markings.isEmpty

/-! ## THE TOP-UNIT HAZARD, as a guard

680 of 4,810 ACATS files — one in seven — have a name that is not among
their unit names (`docs/backlog.md` §L74). `b371001` is that case, and these
are the guards a path-derived top would have got wrong. -/

#guard b371001.sourceFiles.size == 4
#guard b371001.compilationUnits.size == 6

-- The first FILE is `b3710010.a`; the units it contributes are named
-- `B371001_1`, `B371001_1.Child_1` and `B371001_0` — and NOT `B3710010`.
#guard (b371001.compilationUnits.filter (·.file == 0)).map (·.name)
  == #[some "B371001_1", some "B371001_1.Child_1", some "B371001_0"]

-- CHILD units are present and carry their dotted names.
#guard (b371001.unitNames.filter
    (fun n => match n with
              | some m => (m.splitOn ".").length > 1
              | none => false)).size == 3

-- The compilation ORDER comes from the eighth character of the ACATS file
-- name and is RECORDED, never re-derived at read time.
#guard b371001.compilationUnits.map (·.order) == #[0, 0, 0, 1, 2, 3]

/-! ## The markings — the expected result of 37.1% of the suite

Twelve markings across four files, and **every one of them agrees with the
ACAA's own `SUMMARY` tool** (`harness/ada_round_trip.py`, §L75): the suite
owner's software vouches for the half of the envelope that decides B-class
verdicts. -/

#guard b371001.markings.size == 12
#guard (b371001.markingsOf "ERROR").size == 11
#guard (b371001.markingsOf "OK").size == 1

-- Markings are attributed to their own source file, not pooled.
#guard (b371001.markings.filter (·.file == 0)).isEmpty

-- Every marking carries a full CERR-grade span. The scoreboard emits the
-- ACAA's `CERR` records, which need a line AND a position.
--
-- The 2026-08-23 audit found the previous form VACUOUS twice over: it tested
-- `endLine ≥ line && endCol ≥ col`, which an ALL-ZERO span satisfies -- so
-- the guard could not detect the very absence it existed to pin -- and
-- `endCol ≥ col` is not a validity property of a MULTI-LINE span at all
-- (10:40 to 12:5 is legal and would have failed it). The positive property
-- is asserted instead: a real line, a real column, and an end that is
-- after the start in the reading order a span actually has.
#guard b371001.markings.all (fun m =>
  m.line > 0 && m.col > 0 &&
    (m.endLine > m.line || (m.endLine == m.line && m.endCol >= m.col)))

#guard b371001.unsupportedCount == 0

/-! ## Non-vacuity, positively

The counts are EXACT rather than a floor, so a change in the extractor moves
them. `Node.flatten` counts an `absent` node — an absent optional field is a
value in Ada, not an omission — so these are 81 and 13 higher than a walker
that skipped nulls would report, and that difference is the whole point of
the constructor. -/

#guard report.compilationUnits[0]!.decl.flatten.size == 398
#guard b371001.compilationUnits[0]!.decl.flatten.size == 77

end Examples.ada.report
