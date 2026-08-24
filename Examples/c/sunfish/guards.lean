import LeanModels.C

/-!
# M1's capstone: the corpus is INGESTED

`tools/ctwin/sunfish.c` — the node-identical C twin of classic
`sunfish.py`, living in the SUNFISH repository — round-trips
source → clang → `c-0.1` envelope → a literal Lean term, and the term
answers structural questions the CENSUS knows by an independent path.

**Two instruments, two paths, one answer.** Every number below was fixed
in `docs/c-envelope-schema.md` §6 BEFORE this file existed, and each is a
row of `docs/c-construct-census.json`, produced by
`harness/c_construct_census.py` walking clang's AST directly. This file
reaches the same numbers by walking a Lean term built by a different
program (`extractors/c/extract.py` + `LeanModels/C/Json.lean`). Agreement
between them is evidence; a disagreement would be a defect in one of the
two, and the census is the oracle.

That is not hypothetical. The extractor's first `externals` walk lacked
the `loc.file` filter and reported 30 names where the census said 27 —
the three extras being names the SYSTEM HEADERS reference from their own
macro bodies, which appear nowhere in the corpus. The census caught it,
before this file was written.

**There is no semantics here.** M1 is ingestion; the interpreter, the
memory model and the UB refusals are M2 and later, and which of the
charter's three endgames they serve is the owner's open choice
(`docs/c-tier-charter.md` §3, §5).
-/

namespace Examples.c.sunfish

open LeanModels.C

/-! ## The corpus

`maxRecDepth` is raised for the LITERAL, not for a proof: 1458 lines of C
whose AST carries 3123 implicit conversions is a deep first-order term by
construction. -/

set_option maxRecDepth 100000 in
load_c_program sunfishC from "Examples/c/sunfish/sunfish.json"

/-! ## The five structural guards

Fixed by `docs/c-envelope-schema.md` §6 before the ingester existed. Each
cites the census row it must agree with. -/

-- 58 function definitions -- 57 `static` plus `main`.
-- (c-construct-census.json: functions_with_bodies)
#guard sunfishC.unit.functionDefns.length == 58

-- ...of which 57 are `static` (functions_static).
#guard (sunfishC.unit.functionDefns.filter (·.storage == some "static")).length == 57

-- 71 file-scope objects (file_scope_objects).  The knob block is most of
-- them, and it is growing -- mutable static duration is this corpus's NORM,
-- which is why the memory model has to carry it from line one
-- (docs/c-tier-charter.md §1.4).
#guard sunfishC.unit.fileScopeObjects.length == 71

-- 19 indirect call sites (indirect_calls), every one through the `movecb`
-- callback parameter.  This is the corpus's callback protocol, and it is why
-- a C local cannot be an environment binding: `&c` on an automatic
-- `struct kcctx` is how the context reaches the callee.
#guard sunfishC.unit.indirectCalls.length == 19

-- ZERO unsupported statements.  No `switch` (control.SwitchStmt = 0; the one
-- `switch` in the file is the word, in a comment at L283), and nothing else
-- outside the pinned vocabulary either -- so the whole translation unit is IN
-- tier, not merely mostly in it.  That is what makes R1 a rung, not a v0 hole.
#guard sunfishC.unit.unsupportedStmts.length == 0

-- 27 external names (external_names) -- the entire libc surface.  The LIST,
-- not just its length, because the identity of the slice is what milestone M4
-- will owe a semantics for.
#guard (sunfishC.externals.map (·.name)) ==
  ["abort", "atoi", "atol", "calloc", "clock_gettime", "fclose", "fflush",
   "fgets", "fopen", "fprintf", "free", "getenv", "longjmp", "malloc",
   "memchr", "memcmp", "memcpy", "printf", "puts", "realloc", "setjmp",
   "snprintf", "sprintf", "strchr", "strcmp", "strcpy", "strtok"]

/-! ## The envelope's own claims

The profile and the corpus pin are part of the artifact, so they are
checked too — an envelope that quietly changed profile would be a
different program (`docs/c-envelope-schema.md` §0). -/

#guard sunfishC.schemaVersion == "c-0.1"
#guard sunfishC.language == "c"
#guard sunfishC.profileId == "c-profile-0.1"
#guard sunfishC.profileFlags == ["-std=c23", "-D_FORTIFY_SOURCE=0"]
#guard sunfishC.sourceFile == "tools/ctwin/sunfish.c"
#guard sunfishC.sourceSha256 ==
  "7d5e0ff8782f804844f383d6f72314dbf948f8e3a26f4033794d6357140b77d7"

/-! ## `pyfloordiv`, round-tripped

The charter's §4.7 choice, and its reasons are M1's whole thesis: three
statements; the site the ctwin README names as **the #1 place C clones
silently diverge from Python**, so the square's first cross-language
datum; and two of the eleven armed UB classes in three statements — the
division class at `b == 0` and at `INT_MIN / -1`, and the signed-overflow
class at `q--` when `q` is `INT_MIN`. The first thing this tier ever says
about C therefore includes something it must REFUSE.

    static int pyfloordiv(int a, int b) {
        int q = a / b, r = a % b;
        if (r != 0 && ((r < 0) != (b < 0))) q--;
        return q;
    }
-/

-- The function is there, exactly once.
#guard (sunfishC.unit.functionDefns.filter (·.name == "pyfloordiv")).length == 1

/-- `pyfloordiv` as ingested, for the guards below. -/
private def pfd : Option FunctionDefn :=
  sunfishC.unit.functionDefns.find? (·.name == "pyfloordiv")

-- Signature, storage and span -- L160-164 of the pinned corpus.
#guard (pfd.map fun f => (f.ty, f.storage, f.span.line, f.span.endLine))
  == some ("int (int, int)", some "static", 160, 164)

-- Two `int` parameters, in order.
#guard (pfd.map fun f => f.params.map fun p => match p with
    | .param n t _ => (n, t)
    | _ => (none, "?")) == some [(some "a", "int"), (some "b", "int")]

-- THREE statements: a two-object declaration, an `if`, a `return`.
#guard (pfd.bind fun f => f.body.map fun b => match b with
    | .compound body _ => body.length
    | _ => 0) == some 3

-- The declaration binds `q` then `r`.
#guard (pfd.bind fun f => f.body.map fun b => match b with
    | .compound (.decl ds _ :: _) _ => ds.map fun d => match d with
        | .var n _ _ _ _ => n
        | _ => "?"
    | _ => []) == some ["q", "r"]

-- The two UB-carrying operator families are present and are the ones named:
-- `/` and `%` in the initializers, `--` in the `if`.  What they MEAN is M2's
-- business; that they are here, and which they are, is M1's.
#guard (pfd.map fun f => (f.body.map Stmt.substmts).getD [] |>.flatMap
    Stmt.ownExprs |>.filterMap fun e => match e with
      | .binop op _ _ _ _ => if op == "/" || op == "%" then some op else none
      | .unop op _ _ _ _ => if op == "--" then some op else none
      | _ => none) == some ["/", "%", "--"]

-- Nothing in this function fell outside the tier.
#guard (pfd.bind fun f => f.body.map fun b =>
    (b.substmts.filter fun s => match s with
      | .unsupported .. => true
      | _ => false).length) == some 0

end Examples.c.sunfish
