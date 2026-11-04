#!/usr/bin/env python3
"""Tests for tools/gen_sv_refusals.py (stdlib unittest; run: python3 tools/test_gen_sv_refusals.py).

Most tests build a MINI REPOSITORY in a temporary directory (a tiny extract.py, one Lean file, a
tiny expected.json and a register that covers them), so they say exactly what the checker does
without depending on the state of the real tree, which other jobs change all the time.  The
mutation tests are the point: a tag removed from the register, a fake tag added to a scratch copy
of the code, a tag removed from the code, a stale generated file, a `later` without a prerequisite
must each make --check fail with a message that names the culprit.  A few tests also look at the
real register: it validates, and dropping an entry from a copy of it is noticed.

svGolf is a separate project and a checkout may not carry `svgolf/`: the mini repositories are built
WITH it by default and WITHOUT it (`Mini(svgolf=False)`) for the NoSvgolfTests, so both situations
are exercised whatever the real tree looks like; the two tests that look at the real tree's svgolf/
skip themselves with a reason when it is absent (and the converse one when it is present).
"""
import contextlib
import copy
import io
import json
import os
import re
import shutil
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_sv_refusals as g  # noqa: E402

REAL_ROOT = os.path.dirname(HERE)

EXTRACT = '''\
_SYM = None

def unsupported(sm, node, sv_kind=None, text=None):
    return {"kind": "Unsupported", "sv_kind": sv_kind}

def process_symbolic(sm):
    a = _convert_stmt(sm, 1)
    b = guarded(sm)
    return a, b

def _convert_stmt(sm, s):
    if s == 1:
        return unsupported(sm, s, "ForLoopStatement:body")
    if s == 2:
        return unsupported(sm, s)
    kind = "x"
    return unsupported(sm, s, "Thing:" + kind)

def guarded(sm):
    if _SYM is None:
        return unsupported(sm, 1, "M0Guarded:y")
    return None

def m0_only(sm):
    return unsupported(sm, 1, "M0Only:x")
'''

LEAN = '''\
/-! docs mention `.unsupported "Doc:only" "x"` in a comment -/
def connProcs : List Proc :=
  [.unsupported "PortConn:net-width" "narrow"]

-- .unsupported "Fake:comment" "line comment"
#guard loudKind [.unsupported "Test:only" "x"] == some "Test:only"
  && true

def other : Proc := .unsupported s!"Dyn:{x}" y
'''

EXPECTED = {"tasks": {"t": {"negatives": {"neg1": {"stage": "solution"}}, "attacks": {"atk1": {"stage": "source"}}}}}


def entry(eid, tag, cat="refused-now", **kw):
    e = {"id": eid, "tag": tag, "group": "g1", "layers": ["extractor"], "trigger": "H: x", "why": "because",
         "category": cat, "proposed": False}
    if cat in ("later", "never"):
        e["proposed"] = True
    e.update(kw)
    return e


def register():
    return {
        "version": 1, "scope": "mini", "snapshot": "test", "intro": "intro text", "scope_note": "scope note",
        "categories": {c: "def of " + c for c in g.CATEGORIES},
        "principles": [{"id": "P-A", "text": "principle a"}],
        "policies": [{"policy": "p", "source": "s", "decided_by_thomas": True}],
        "groups": [{"id": "g1", "title": "Group one", "note": ""}],
        "plan_items": [{"id": "PL", "title": "plan", "source": "src", "decided_by_thomas": True}],
        "docs": [{"path": "docs/x.md", "what": "x"}], "departures": [], "holes": [], "schema": ["s"],
        "scan": {"extractor": "extractors/sv/extract.py", "extractor_root": "process_symbolic",
                 "lean_files": ["LeanModels/Sv/Hier2.lean"], "lean_ignore_tags": [],
                 "svgolf_expected": "svgolf/tests/expected.json"},
        "entries": [
            entry("for", "ForLoopStatement", "later", prerequisite="loops", plan="PL",
                  kinds={"extractor": ["ForLoopStatement:body"]}, value_rank=1, value_note="popcount"),
            entry("dflt", "default tag", kinds={"extractor": ["@default:_convert_stmt"]}),
            entry("thing", "Thing:*", "never", principle="P-A", kinds={"extractor": ["Thing:*"]}),
            entry("net", "PortConn:net-width", layers=["lean-model"], kinds={"lean": ["PortConn:net-width"]}),
            entry("dyn", "Dyn", layers=["lean-model"], kinds={"lean": ["Dyn"]}),
            entry("msg", "a message", layers=["lean-model"], match=[{"file": "LeanModels/Sv/Hier2.lean", "text": "narrow"}]),
        ],
        "svgolf": {
            "intro": "i", "stages": [{"id": "source", "what": "w", "refuses": "r"}], "policies": ["pol"],
            "groups": [{"id": "sg1", "stage": "source", "title": "G", "intro": "gi", "write_ok": "assign y = a;",
                        "refused_example": "assign y = a +;"}],
            "never_summary": ["n"], "lifting": ["l"], "limits": ["lim"], "links": [{"path": "a/b.md", "what": "w"}],
            "entries": [entry("s1", "an attack", group="sg1", layers=["svgolf-gate"], attacks=["t/neg1", "t/atk1"],
                              match=[{"file": "extractors/sv/extract.py", "text": "process_symbolic"}])],
        },
    }


class Mini:
    """A mini repository in a temporary directory."""

    def __init__(self, reg=None, extract=EXTRACT, lean=LEAN, svgolf=True):
        self.dir = tempfile.mkdtemp(prefix="svref-")
        files = [("extractors/sv/extract.py", extract), ("LeanModels/Sv/Hier2.lean", lean)]
        if svgolf:
            files.append(("svgolf/tests/expected.json", json.dumps(EXPECTED)))
        for rel, text in files:
            self.put(rel, text)
        self.reg = reg if reg is not None else register()
        self.save()

    def put(self, rel, text):
        p = os.path.join(self.dir, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w", encoding="utf-8") as fh:
            fh.write(text)

    def get(self, rel):
        with open(os.path.join(self.dir, rel), encoding="utf-8") as fh:
            return fh.read()

    def save(self):
        self.put(g.REGISTER, json.dumps(self.reg, indent=1))

    def has(self, rel):
        return os.path.exists(os.path.join(self.dir, rel))

    def write(self, *flags):
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            return g.main(["--root", self.dir, "--write"] + list(flags))

    def check(self, strict=False):
        out = io.StringIO()
        rc = g.run_check(self.dir, strict, out)
        return rc, out.getvalue()

    def cleanup(self):
        shutil.rmtree(self.dir, ignore_errors=True)


class MiniCase(unittest.TestCase):
    def mini(self, **kw):
        m = Mini(**kw)
        self.addCleanup(m.cleanup)
        return m

    def fresh(self, **kw):
        m = self.mini(**kw)
        self.assertEqual(m.write(), 0)
        return m


class ScannerTests(unittest.TestCase):
    def test_extractor_live_and_m0(self):
        allk, live = g.extractor_kinds(EXTRACT)
        self.assertEqual(set(live), {"ForLoopStatement:body", "@default:_convert_stmt", "Thing:*"})
        self.assertIn("M0Only:x", allk)
        self.assertNotIn("M0Only:x", live)
        # the call under `if _SYM is None:` is dead in symbolic mode
        self.assertNotIn("M0Guarded:y", live)

    def test_lean_ignores_comments_and_guard_blocks(self):
        d = tempfile.mkdtemp()
        try:
            os.makedirs(os.path.join(d, "LeanModels/Sv"))
            with open(os.path.join(d, "LeanModels/Sv/Hier2.lean"), "w") as fh:
                fh.write(LEAN)
            tags = g.lean_tags(d, ["LeanModels/Sv/Hier2.lean"])
        finally:
            shutil.rmtree(d)
        self.assertEqual(set(tags), {"PortConn:net-width", "Dyn"})

    def test_find_line_resolves_a_function_by_name(self):
        d = tempfile.mkdtemp()
        try:
            os.makedirs(os.path.join(d, "x"))
            with open(os.path.join(d, "x/a.lean"), "w") as fh:
                fh.write("-- connProcs mentioned in a comment\ndef Foo.connProcs : Nat := 1\ndef elemAcc? : Nat := 2\n")
            self.assertEqual(g.find_line(d, "x/a.lean", "Foo.connProcs"), 2)   # the definition, not the comment
            self.assertEqual(g.find_line(d, "x/a.lean", "elemAcc?"), 3)
            self.assertIsNone(g.find_line(d, "x/a.lean", "nope"))
        finally:
            shutil.rmtree(d)


class CheckTests(MiniCase):
    def test_clean_mini_repo_passes(self):
        m = self.fresh()
        rc, out = m.check()
        self.assertEqual(rc, 0, out)
        self.assertIn("sv-refusals: ok", out)

    def test_removing_an_entry_from_the_register_fails(self):
        m = self.fresh()
        m.reg["entries"] = [e for e in m.reg["entries"] if e["id"] != "for"]
        m.save()
        m.write()
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn("ForLoopStatement:body", out)
        self.assertIn("is not in the register", out)

    def test_fake_extractor_tag_in_a_scratch_copy_of_the_code_fails(self):
        m = self.fresh()
        m.put("extractors/sv/extract.py", EXTRACT.replace("    kind = \"x\"\n", "    kind = \"x\"\n    if s == 9:\n        return unsupported(sm, s, \"Fake:new\")\n"))
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn("Fake:new", out)

    def test_an_unreachable_function_is_not_required(self):
        m = self.fresh()
        m.put("extractors/sv/extract.py", EXTRACT + '\ndef _never_called(sm, s):\n    return unsupported(sm, s, "Fake:unreachable")\n')
        rc, out = m.check()
        self.assertEqual(rc, 0, out)

    def test_unreachable_m0_kind_is_not_required(self):
        m = self.fresh()
        m.put("extractors/sv/extract.py", EXTRACT + '\ndef more_m0(sm):\n    return unsupported(sm, 1, "M0More:z")\n')
        rc, out = m.check()
        self.assertEqual(rc, 0, out)

    def test_fake_lean_tag_fails(self):
        m = self.fresh()
        m.put("LeanModels/Sv/Hier2.lean", LEAN + '\ndef bad : Proc := .unsupported "Fake:lean" "x"\n')
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn("Fake:lean", out)

    def test_a_tag_removed_from_the_code_is_noticed(self):
        m = self.fresh()
        m.put("LeanModels/Sv/Hier2.lean", LEAN.replace('.unsupported "PortConn:net-width" "narrow"', '.error "gone"'))
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn("PortConn:net-width", out)
        self.assertIn("no longer", out)
        m2 = self.fresh()
        m2.put("extractors/sv/extract.py", EXTRACT.replace('"ForLoopStatement:body"', '"Renamed:body"'))
        rc, out = m2.check()
        self.assertEqual(rc, 1)
        self.assertIn("ForLoopStatement:body", out)

    def test_message_match_that_disappears_is_noticed(self):
        m = self.fresh()
        m.put("LeanModels/Sv/Hier2.lean", LEAN.replace('"narrow"', '"wide"'))
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn("'narrow'", out)

    def test_stale_generated_file_fails(self):
        m = self.fresh()
        m.put(g.OUT_MD, m.get(g.OUT_MD) + "hand edit\n")
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn(g.OUT_MD, out)
        self.assertIn("stale", out)
        m2 = self.mini()
        rc, out = m2.check()
        self.assertEqual(rc, 1)
        self.assertIn("missing", out)

    def test_svgolf_attack_names_must_be_cited(self):
        m = self.fresh()
        m.reg["svgolf"]["entries"][0]["attacks"] = ["t/neg1"]
        m.save()
        m.write()
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn("t/atk1", out)

    def test_advisory_attacks_need_no_citation(self):
        m = self.fresh()
        exp = json.loads(json.dumps(EXPECTED))
        exp["tasks"]["t"]["attacks"]["adv1"] = {"stage": "unproved", "advisory": True}
        m.put("svgolf/tests/expected.json", json.dumps(exp))
        m.write()
        rc, out = m.check()
        self.assertEqual(rc, 0, out)
        self.assertNotIn("adv1", out)
        exp["tasks"]["t"]["attacks"]["adv2"] = {"stage": "unproved"}     # not marked: still cited
        m.put("svgolf/tests/expected.json", json.dumps(exp))
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn("t/adv2", out)
        self.assertNotIn("t/adv1", out)

    def test_svgolf_cites_a_name_that_does_not_exist(self):
        m = self.fresh()
        m.reg["svgolf"]["entries"][0]["attacks"].append("t/ghost")
        m.save()
        m.write()
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn("t/ghost", out)


class ValidationTests(MiniCase):
    def errors(self, mutate):
        m = self.mini()
        mutate(m.reg)
        return g.validate(m.reg)

    def test_later_needs_a_prerequisite(self):
        errs = self.errors(lambda r: r["entries"][0].pop("prerequisite"))
        self.assertTrue(any("later without a prerequisite" in e for e in errs), errs)

    def test_never_needs_a_known_principle(self):
        errs = self.errors(lambda r: r["entries"][2].update(principle="P-MADE-UP"))
        self.assertTrue(any("without a principle of the table" in e for e in errs), errs)

    def test_later_and_never_state_proposed(self):
        errs = self.errors(lambda r: r["entries"][0].pop("proposed"))
        self.assertTrue(any("boolean `proposed`" in e or "missing field 'proposed'" in e for e in errs), errs)

    def test_refused_now_cannot_be_proposed(self):
        errs = self.errors(lambda r: r["entries"][1].update(proposed=True))
        self.assertTrue(any("refused-now must not carry proposed=true" in e for e in errs), errs)

    def test_duplicate_ids_unknown_group_unknown_plan(self):
        errs = self.errors(lambda r: (r["entries"][1].update(id="for"), r["entries"][3].update(group="nope"),
                                      r["entries"][0].update(plan="NOPE")))
        text = "\n".join(errs)
        self.assertIn("duplicated", text)
        self.assertIn("unknown group", text)
        self.assertIn("unknown plan item", text)

    def test_pending_needs_its_decision(self):
        errs = self.errors(lambda r: r["entries"][1].update(category="refused-pending"))
        self.assertTrue(any("refused-pending without the source of the decision" in e for e in errs), errs)

    def test_clean_register_validates(self):
        self.assertEqual(g.validate(self.mini().reg), [])


class PendingTests(MiniCase):
    def add_pending(self, m, ext_tag="Round6:new", lean_tag=None, text=None):
        e = entry("pend", "Round6:new", "refused-pending", decided_by="Thomas 2026-10-29 (test)")
        e["kinds"] = {"extractor": [ext_tag]} if lean_tag is None else {"lean": [lean_tag]}
        if text:
            e["match"] = [{"file": "LeanModels/Sv/Hier2.lean", "text": text}]
        m.reg["entries"].append(e)
        m.save()
        m.write()

    def test_pending_tag_may_be_absent_from_the_code(self):
        m = self.fresh()
        self.add_pending(m)
        rc, out = m.check()
        self.assertEqual(rc, 0, out)
        self.assertNotIn("now in the code", out)

    def test_pending_tag_that_appears_warns_and_strict_fails(self):
        m = self.fresh()
        self.add_pending(m)
        m.put("extractors/sv/extract.py", EXTRACT.replace("    kind = \"x\"\n", "    kind = \"x\"\n    if s == 9:\n        return unsupported(sm, s, \"Round6:new\")\n"))
        rc, out = m.check()
        self.assertEqual(rc, 0, out)
        self.assertIn("warning: pending entry 'pend'", out)
        rc, out = m.check(strict=True)
        self.assertEqual(rc, 1)
        self.assertIn("now in the code", out)

    def test_pending_lean_tag_and_message(self):
        m = self.fresh()
        self.add_pending(m, lean_tag="Round6:lean")
        rc, out = m.check()
        self.assertEqual(rc, 0, out)
        m.put("LeanModels/Sv/Hier2.lean", LEAN + '\ndef p : Proc := .unsupported "Round6:lean" "x"\n')
        rc, out = m.check()
        self.assertEqual(rc, 0, out)
        self.assertIn("now in the code", out)

    def test_an_uncovered_code_tag_is_still_an_error_even_with_pending_rows(self):
        m = self.fresh()
        self.add_pending(m)
        m.put("LeanModels/Sv/Hier2.lean", LEAN + '\ndef p : Proc := .unsupported "Other:tag" "x"\n')
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn("Other:tag", out)


class NoSvgolfTests(MiniCase):
    """A checkout without `svgolf/`: the ls-sv half is checked in full, the svGolf half is skipped."""

    def test_the_directory_decides(self):
        self.assertTrue(g.has_svgolf(self.mini().dir))
        self.assertFalse(g.has_svgolf(self.mini(svgolf=False).dir))

    def test_check_passes_without_svgolf_and_says_what_it_skipped(self):
        m = self.fresh(svgolf=False)
        self.assertFalse(m.has("svgolf"))
        rc, out = m.check()
        self.assertEqual(rc, 0, out)
        self.assertIn("svGolf: half skipped because svgolf/ is absent", out)
        self.assertIn("sv-refusals: ok (6 ls-sv entries; svGolf half skipped, svgolf/ is absent)", out)
        self.assertNotIn("expected.json:", out)       # the attack citations were not read

    def test_write_without_svgolf_writes_the_register_only_and_creates_no_directory(self):
        m = self.mini(svgolf=False)
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(g.main(["--root", m.dir, "--write"]), 0)
        self.assertEqual(out.getvalue().split(), ["wrote", g.OUT_MD])
        self.assertTrue(m.has(g.OUT_MD))
        self.assertFalse(m.has("svgolf"))
        self.assertFalse(m.has(g.OUT_SVGOLF))

    def test_the_ls_sv_register_is_byte_identical_with_and_without_svgolf(self):
        with_sv, without = self.fresh(), self.fresh(svgolf=False)
        self.assertTrue(with_sv.has(g.OUT_SVGOLF))
        self.assertEqual(with_sv.get(g.OUT_MD), without.get(g.OUT_MD))

    def test_a_missing_svgolf_document_is_not_demanded(self):
        m = self.mini(svgolf=False)
        rc, out = m.check()                              # nothing written yet: only the ls-sv document is missing
        self.assertEqual(rc, 1)
        self.assertIn("%s is missing" % g.OUT_MD, out)
        self.assertNotIn("ERROR: " + g.OUT_SVGOLF, out)

    def test_svgolf_entries_are_not_checked_without_svgolf(self):
        # a svGolf row that cites an attack nobody has and a file that does not exist: invisible without svgolf/
        m = self.fresh(svgolf=False)
        sv = m.reg["svgolf"]["entries"][0]
        sv["attacks"].append("t/ghost")
        sv["match"] = [{"file": "svgolf/score/nope.py", "text": "x"}]
        sv["where"] = [{"file": "svgolf/score/nope.py", "fn": "f"}]
        m.save()
        m.write()
        rc, out = m.check()
        self.assertEqual(rc, 0, out)
        self.assertNotIn("nope.py", out)
        # ... and caught as soon as svgolf/ is there
        m.put("svgolf/tests/expected.json", json.dumps(EXPECTED))
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn("t/ghost", out)
        self.assertIn("svgolf/score/nope.py does not exist", out)

    def test_a_missing_ls_sv_entry_is_still_caught_without_svgolf(self):
        m = self.fresh(svgolf=False)
        m.reg["entries"] = [e for e in m.reg["entries"] if e["id"] != "for"]
        m.save()
        m.write()
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn("ForLoopStatement:body", out)
        self.assertIn("is not in the register", out)

    def test_a_fake_ls_sv_tag_is_still_caught_without_svgolf(self):
        m = self.fresh(svgolf=False)
        m.put("LeanModels/Sv/Hier2.lean", LEAN + '\ndef bad : Proc := .unsupported "Fake:lean" "x"\n')
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn("Fake:lean", out)
        m.put("LeanModels/Sv/Hier2.lean", LEAN)
        m.put("extractors/sv/extract.py", EXTRACT.replace("    kind = \"x\"\n", "    kind = \"x\"\n    if s == 9:\n        return unsupported(sm, s, \"Fake:new\")\n"))
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn("Fake:new", out)

    def test_a_tag_removed_from_the_code_is_still_noticed_without_svgolf(self):
        m = self.fresh(svgolf=False)
        m.put("LeanModels/Sv/Hier2.lean", LEAN.replace('.unsupported "PortConn:net-width" "narrow"', '.error "gone"'))
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn("PortConn:net-width", out)
        self.assertIn("no longer", out)

    def test_a_stale_ls_sv_document_is_still_caught_without_svgolf(self):
        m = self.fresh(svgolf=False)
        m.put(g.OUT_MD, m.get(g.OUT_MD) + "hand edit\n")
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn("stale", out)

    def test_the_register_is_still_validated_without_svgolf(self):
        m = self.fresh(svgolf=False)
        m.reg["svgolf"]["entries"][0]["category"] = "later"           # a later row without a prerequisite
        m.save()
        self.assertEqual(m.write(), 1)

    def test_no_svgolf_flag_skips_the_half_even_where_svgolf_exists(self):
        m = self.fresh()
        m.put(g.OUT_SVGOLF, m.get(g.OUT_SVGOLF) + "hand edit\n")
        rc, out = m.check()
        self.assertEqual(rc, 1)
        self.assertIn(g.OUT_SVGOLF, out)
        out = io.StringIO()
        self.assertEqual(g.run_check(m.dir, False, out, svgolf=False), 0, out.getvalue())
        self.assertIn("half skipped", out.getvalue())
        with contextlib.redirect_stdout(io.StringIO()) as w:
            self.assertEqual(g.main(["--root", m.dir, "--no-svgolf", "--check"]), 0)
        self.assertIn("half skipped", w.getvalue())

    def test_svgolf_flag_forces_the_half_where_the_directory_is_absent(self):
        m = self.mini(svgolf=False)
        with contextlib.redirect_stdout(io.StringIO()) as w:
            self.assertEqual(g.main(["--root", m.dir, "--svgolf", "--check"]), 1)
        self.assertIn("ERROR: %s is missing" % g.OUT_SVGOLF, w.getvalue())
        self.assertEqual(m.write("--svgolf"), 1)                      # refuses rather than creating svgolf/
        self.assertFalse(m.has("svgolf"))

    def test_emit_svgolf_does_not_need_the_directory(self):
        m = self.mini(svgolf=False)
        out = os.path.join(m.dir, "elsewhere.md")
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(g.main(["--root", m.dir, "--emit-svgolf", out]), 0)
        self.assertFalse(m.has("svgolf"))
        with open(out, encoding="utf-8") as fh:
            self.assertEqual(fh.read(), g.render_svgolf(m.reg) + "\n")


class GlobTests(unittest.TestCase):
    def test_exact_and_glob_matching(self):
        self.assertTrue(g.kind_matches("Thing:*", "Thing:*"))
        self.assertFalse(g.kind_matches("Thing:foo", "Thing:*"))      # a family must be declared on purpose
        self.assertTrue(g.kind_matches("Thing:foo", "glob:Thing:*"))
        self.assertTrue(g.kind_matches("*", "*"))
        self.assertFalse(g.kind_matches("Other", "glob:Thing:*"))


class RealRegisterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = g.load(REAL_ROOT)

    def test_real_register_is_structurally_valid(self):
        self.assertEqual(g.validate(self.data), [])

    def test_every_later_names_a_prerequisite_and_every_never_a_principle(self):
        principles = {p["id"] for p in self.data["principles"]}
        for e in g.all_entries(self.data):
            if e["category"] == "later":
                self.assertTrue(e["prerequisite"].strip(), e["id"])
            if e["category"] == "never":
                self.assertIn(e["principle"], principles, e["id"])

    def test_dropping_an_extractor_entry_from_the_real_register_is_noticed(self):
        data = copy.deepcopy(self.data)
        victim = next(e for e in data["entries"] if e.get("kinds", {}).get("extractor") and e["category"] != "refused-pending"
                      and not any(o is not e and set(o.get("kinds", {}).get("extractor", [])) & set(e["kinds"]["extractor"])
                                  for o in data["entries"]))
        data["entries"] = [e for e in data["entries"] if e is not victim]
        errs, _, _ = g.check_code(REAL_ROOT, data)
        self.assertTrue(any(k in " ".join(errs) for k in victim["kinds"]["extractor"]), (victim["id"], errs[:3]))

    def test_dropping_a_lean_entry_from_the_real_register_is_noticed(self):
        data = copy.deepcopy(self.data)
        victim = next(e for e in data["entries"] if e.get("kinds", {}).get("lean") and e["category"] != "refused-pending"
                      and not any(o is not e and set(o.get("kinds", {}).get("lean", [])) & set(e["kinds"]["lean"])
                                  for o in data["entries"]))
        data["entries"] = [e for e in data["entries"] if e is not victim]
        errs, _, _ = g.check_code(REAL_ROOT, data)
        self.assertTrue(any(k in " ".join(errs) for k in victim["kinds"]["lean"]), (victim["id"], errs[:3]))

    def test_a_fake_tag_in_a_scratch_copy_of_the_real_extractor_is_noticed(self):
        d = tempfile.mkdtemp()
        try:
            os.makedirs(os.path.join(d, "extractors/sv"))
            src = g.read(REAL_ROOT, "extractors/sv/extract.py")
            marker = "def process_symbolic("
            self.assertIn(marker, src)
            # a new live refusal reachable from process_symbolic
            src = src.replace(marker, 'def _fake_live_refusal(sm, n):\n    return unsupported(sm, n, "FakeFamily:fake-detail")\n\n' + marker, 1)
            i = src.index(marker)
            j = src.index("\n", src.index(":", src.index(")", i)))
            src = src[:j + 1] + "    _fake_live_refusal(sm, None)\n" + src[j + 1:]
            with open(os.path.join(d, "extractors/sv/extract.py"), "w") as fh:
                fh.write(src)
            allk, live = g.extractor_kinds(src)
        finally:
            shutil.rmtree(d)
        self.assertIn("FakeFamily:fake-detail", live)
        covered = any(g.kind_matches("FakeFamily:fake-detail", k) for e in g.all_entries(self.data)
                      for k in g.kinds_of(e, "extractor"))
        self.assertFalse(covered)


class RealTreeSvgolfTests(unittest.TestCase):
    """The real tree's own situation: the svGolf half of --check follows the presence of svgolf/."""

    @classmethod
    def setUpClass(cls):
        cls.data = g.load(REAL_ROOT)

    @unittest.skipUnless(g.HAS_SVGOLF, "svgolf/ is absent in this checkout (the svGolf project lives on the golf branch)")
    def test_with_svgolf_the_attack_citations_are_read(self):
        _, _, info = g.check_code(REAL_ROOT, self.data)
        self.assertTrue(any("attack/negative names in expected.json" in i for i in info), info)
        self.assertFalse(any("half skipped" in i for i in info), info)

    @unittest.skipIf(g.HAS_SVGOLF, "svgolf/ is present in this checkout (see the converse test)")
    def test_without_svgolf_the_half_is_skipped_and_no_svgolf_file_is_read(self):
        _, _, info = g.check_code(REAL_ROOT, self.data)
        self.assertTrue(any("half skipped because svgolf/ is absent" in i for i in info), info)
        self.assertFalse(any("attack/negative names" in i for i in info), info)

    def test_a_forced_skip_reads_no_svgolf_file(self):
        errs, _, info = g.check_code(REAL_ROOT, self.data, svgolf=False)
        self.assertTrue(any("half skipped" in i for i in info), info)
        self.assertFalse(any("svgolf" in e for e in errs), errs)


class RenderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = g.load(REAL_ROOT)

    def test_rendering_is_deterministic(self):
        self.assertEqual(g.render_register(self.data), g.render_register(copy.deepcopy(self.data)))
        self.assertEqual(g.render_svgolf(self.data), g.render_svgolf(copy.deepcopy(self.data)))

    def test_tables_have_consistent_columns(self):
        for name, text in (("register", g.render_register(self.data)), ("svgolf", g.render_svgolf(self.data))):
            rows = text.split("\n")
            i = 0
            while i < len(rows):
                if rows[i].startswith("|"):
                    j = i
                    while j < len(rows) and rows[j].startswith("|"):
                        j += 1
                    widths = {len(re.findall(r"(?<!\\)\|", r)) for r in rows[i:j]}
                    self.assertEqual(len(widths), 1, "%s: ragged table at line %d: %r" % (name, i + 1, rows[i][:80]))
                    i = j
                else:
                    i += 1

    def test_code_helper_survives_backticks(self):
        self.assertEqual(g.code("a"), "`a`")
        self.assertEqual(g.code("`ifdef X"), "`` `ifdef X ``")

    def test_standalone_svgolf_emission_equals_the_committed_text_of_the_data(self):
        d = tempfile.mkdtemp()
        try:
            out = os.path.join(d, "REFUSALS.md")
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(g.main(["--root", REAL_ROOT, "--emit-svgolf", out]), 0)
            with open(out, encoding="utf-8") as fh:
                self.assertEqual(fh.read(), g.render_svgolf(self.data) + "\n")
        finally:
            shutil.rmtree(d)

    def test_ls_sv_register_links_nothing_into_svgolf(self):
        # svgolf/ may be absent from a checkout: the register cites its files as text, never as a link
        self.assertNotRegex(g.render_register(self.data), r"\]\((?:\.\./)?svgolf/")

    def test_svgolf_document_has_no_links_into_the_repository_tree(self):
        text = g.render_svgolf(self.data)
        self.assertNotRegex(text, r"\]\((?:\.\./|docs/|svgolf/)")


if __name__ == "__main__":
    unittest.main(verbosity=1)
