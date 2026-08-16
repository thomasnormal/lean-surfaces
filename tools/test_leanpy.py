#!/usr/bin/env python3
"""test_leanpy.py — the envelope cache's concurrency contract.

THE BUG THIS EXISTS FOR (2026-08-16, found by a library-mode sweep): the
cache is keyed by (source, extractor, frontend) and `envelope_for`
returns early the moment `os.path.exists(out)`. The extractor wrote
STRAIGHT TO `out`, and `json.dump` on a buffered file writes in chunks —
so "exists" was true from the instant the file was created until the dump
finished, and a second survey arriving in that window was handed a
truncated envelope. Measured on a 26MB envelope: the path appears at
+1.13s and the dump runs until +2.01s, growing through 554 distinct
sizes. The observed casualty was a `RUNNER` verdict reading
``is not a valid envelope: offset 106380: unexpected end of input``.

Same family as the recorded shared-jobs-file race, whose fix was to key
the path per process; this one is fixed by writing to a temp file in the
same directory and `os.replace`-ing it into place, so the final name only
ever names a COMPLETE envelope.

Run: python3 tools/test_leanpy.py   (wired into tools/ci.sh)
"""

import glob
import importlib.machinery
import importlib.util
import json
import os
import shutil
import sys
import tempfile
import time
import unittest
from multiprocessing import Process, Queue

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
_spec = importlib.util.spec_from_loader(
    "leanpy", importlib.machinery.SourceFileLoader(
        "leanpy", os.path.join(REPO_ROOT, "tools", "leanpy")))
leanpy = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(leanpy)

# Big enough that the dump is visibly incremental (see the module
# docstring's measurement) and small enough to stay a CI second or two.
FUNCS = 4000


def _fresh_source(dirpath, tag):
    """A source no cache can already hold — the miss is the point."""
    src = os.path.join(dirpath, "big.py")
    with open(src, "w", encoding="utf-8") as f:
        f.write("# %s\n" % tag)
        for i in range(FUNCS):
            f.write("def f%d(a, b):\n    return (a + %d) * (b - %d)\n\n\n" % (i, i, i))
    return src


def _extract(src, cache, q):
    q.put(("extract", leanpy.envelope_for(src, cache) is not None))


def _arriving_survey(src, cache, q, deadline):
    """A SECOND survey arriving mid-write.

    It waits for the cache entry's FINAL NAME to appear — which is exactly
    the condition `envelope_for`'s early return tests — and then does what
    a survey does: ask for the envelope and read it. Pinning the arrival
    instead of leaving it to luck is what makes the race deterministic;
    the window it lands in is the real one.
    """
    pat = os.path.join(cache, "big-*.json")
    while time.time() < deadline and not glob.glob(pat):
        time.sleep(0.001)
    if not glob.glob(pat):
        q.put(("arrival", "TIMEOUT: the cache entry never appeared"))
        return
    path = leanpy.envelope_for(src, cache)
    if path is None:
        q.put(("arrival", "EXTRACT-FAILED"))
        return
    try:
        with open(path, encoding="utf-8") as f:
            json.load(f)
    except ValueError as e:
        q.put(("arrival", "CORRUPT: %s" % e))
        return
    q.put(("arrival", "OK"))


class CacheAtomicityTests(unittest.TestCase):
    def test_a_concurrent_survey_never_reads_a_partial_envelope(self):
        """THE RACE, provoked: one survey extracts, a second arrives the
        instant the entry's final name exists. Before the atomic-rename
        fix this reads a truncated file; after it, the name cannot exist
        until the envelope is whole."""
        cache = tempfile.mkdtemp(prefix="leanpy-test-cache-")
        srcdir = tempfile.mkdtemp(prefix="leanpy-test-src-")
        try:
            for r in range(3):
                shutil.rmtree(cache, ignore_errors=True)
                os.makedirs(cache)
                src = _fresh_source(srcdir, "round %d %f" % (r, time.time()))
                q = Queue()
                pe = Process(target=_extract, args=(src, cache, q))
                pa = Process(target=_arriving_survey,
                             args=(src, cache, q, time.time() + 180))
                pe.start()
                pa.start()
                pe.join()
                pa.join()
                res = dict(q.get() for _ in range(2))
                self.assertTrue(res.get("extract"), "the extraction itself failed")
                self.assertEqual(res.get("arrival"), "OK",
                                 "round %d: a concurrent survey read a partial "
                                 "envelope (%s)" % (r, res.get("arrival")))
        finally:
            shutil.rmtree(cache, ignore_errors=True)
            shutil.rmtree(srcdir, ignore_errors=True)

    def test_the_extractor_never_writes_to_the_cache_entry_itself(self):
        """The writer-level invariant, checked without timing: whatever
        path the extractor is told to write, it is NOT the path handed
        back. That is what makes the rename the only way the final name
        comes into existence."""
        cache = tempfile.mkdtemp(prefix="leanpy-test-cache-")
        srcdir = tempfile.mkdtemp(prefix="leanpy-test-src-")
        seen = {}
        real_run = leanpy.subprocess.run

        def spy(cmd, **kw):
            if "--out" in cmd:
                seen["out"] = cmd[cmd.index("--out") + 1]
            return real_run(cmd, **kw)

        try:
            src = _fresh_source(srcdir, "atomicity %f" % time.time())
            leanpy.subprocess.run = spy
            path = leanpy.envelope_for(src, cache)
            self.assertIsNotNone(path, "extraction failed")
            self.assertIn("out", seen, "the extractor was never invoked")
            self.assertNotEqual(os.path.realpath(seen["out"]),
                                os.path.realpath(path),
                                "the extractor wrote straight to the cache entry")
            self.assertEqual(os.path.dirname(os.path.realpath(seen["out"])),
                             os.path.dirname(os.path.realpath(path)),
                             "the temp file must share the entry's directory, or "
                             "os.replace is not atomic")
            self.assertFalse(os.path.exists(seen["out"]),
                             "the temp file outlived the rename")
            with open(path, encoding="utf-8") as f:
                json.load(f)
        finally:
            leanpy.subprocess.run = real_run
            shutil.rmtree(cache, ignore_errors=True)
            shutil.rmtree(srcdir, ignore_errors=True)

    def test_a_failed_extraction_leaves_no_cache_entry_and_no_temp(self):
        """A syntax error must not publish anything: a half-answer in the
        cache would be served to every later run."""
        cache = tempfile.mkdtemp(prefix="leanpy-test-cache-")
        srcdir = tempfile.mkdtemp(prefix="leanpy-test-src-")
        try:
            src = os.path.join(srcdir, "broken.py")
            with open(src, "w", encoding="utf-8") as f:
                f.write("def f(:\n")
            self.assertIsNone(leanpy.envelope_for(src, cache))
            self.assertEqual(os.listdir(cache), [],
                             "a failed extraction left something in the cache")
        finally:
            shutil.rmtree(cache, ignore_errors=True)
            shutil.rmtree(srcdir, ignore_errors=True)


class CompanionPathInvarianceTests(unittest.TestCase):
    """The dirty-tree family's other half.

    `rel_posix` feeds three embedded strings — the envelope's
    `source_file`, and the companion's `source:` header and
    `load_program … from "…"`. It used to be the path AS GIVEN, so an
    INLINE-mode source (`sum_to.py`, which regenerates its committed
    companion on every extraction) came out with absolute lines whenever a
    survey passed an absolute path, and the tree went dirty. Warm caches
    hid it: the cache is keyed by source BYTES, so the rewrite only
    happened on a first extraction.

    The canonical form was read off the committed companion
    (`Examples/python/sum_to/sum_to.py` — repo-relative POSIX), not
    chosen. These tests drive the real committed example, because "matches
    what is checked in" is the property that actually keeps the tree
    clean.
    """

    SRC = "Examples/python/sum_to/sum_to.py"
    COMPANION = "Examples/python/sum_to/SumTo.lean"
    ENVELOPE = "Examples/python/sum_to/sum_to.json"

    def setUp(self):
        # A failure must not leave the tree dirty -- that is the very thing
        # under test.
        self._saved = {}
        for rel in (self.COMPANION, self.ENVELOPE):
            with open(os.path.join(REPO_ROOT, rel), "rb") as f:
                self._saved[rel] = f.read()

    def tearDown(self):
        for rel, data in self._saved.items():
            with open(os.path.join(REPO_ROOT, rel), "wb") as f:
                f.write(data)

    def _extract(self, arg, cwd):
        r = leanpy.subprocess.run(
            [sys.executable, os.path.join(REPO_ROOT, "extractors/python/extract.py"), arg],
            cwd=cwd, capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr or r.stdout)
        with open(os.path.join(REPO_ROOT, self.COMPANION), "rb") as f:
            companion = f.read()
        with open(os.path.join(REPO_ROOT, self.ENVELOPE), "rb") as f:
            envelope = f.read()
        return companion, envelope

    def test_relative_absolute_and_other_cwd_agree_with_what_is_committed(self):
        spellings = [
            ("relative, from the repo root", self.SRC, REPO_ROOT),
            ("absolute", os.path.join(REPO_ROOT, self.SRC), REPO_ROOT),
            ("relative, from a subdirectory",
             os.path.join("python", "sum_to", "sum_to.py"),
             os.path.join(REPO_ROOT, "Examples")),
            ("absolute, from an unrelated cwd",
             os.path.join(REPO_ROOT, self.SRC), tempfile.gettempdir()),
        ]
        results = {}
        for name, arg, cwd in spellings:
            results[name] = self._extract(arg, cwd)
        first = spellings[0][0]
        for name, _, _ in spellings[1:]:
            self.assertEqual(results[name][0], results[first][0],
                             "companion differs: %s vs %s" % (name, first))
            self.assertEqual(results[name][1], results[first][1],
                             "envelope differs: %s vs %s" % (name, first))
        # …and the invariant form is the COMMITTED one, so extraction never
        # dirties the tree.
        self.assertEqual(results[first][0], self._saved[self.COMPANION],
                         "the companion no longer matches what is committed")

    def test_the_committed_form_is_repo_relative_posix(self):
        """Read off the committed file, so the convention cannot drift
        silently into `rel_posix`'s idea of it."""
        text = self._saved[self.COMPANION].decode("utf-8")
        self.assertIn("source: %s\n" % self.SRC, text)
        self.assertIn('load_program sum_to from "%s"'
                      % self.ENVELOPE, text)
        self.assertEqual(leanpy_extract().rel_posix(
            os.path.join(REPO_ROOT, self.SRC)), self.SRC)

    def test_a_source_outside_the_repo_keeps_an_absolute_invariant_path(self):
        """There is no repo-relative form for it, and absolute is already
        invariant — but it must be the REALPATH, or two spellings of the
        same out-of-tree file still disagree."""
        extract = leanpy_extract()
        d = tempfile.mkdtemp(prefix="leanpy-test-out-of-tree-")
        try:
            src = os.path.join(d, "m.py")
            with open(src, "w", encoding="utf-8") as f:
                f.write("def f():\n    return 1\n")
            direct = extract.rel_posix(src)
            self.assertTrue(direct.startswith("/"), direct)
            self.assertEqual(direct, os.path.realpath(src).replace(os.sep, "/"))
            # a second spelling of the same file
            self.assertEqual(extract.rel_posix(os.path.join(d, ".", "m.py")), direct)
        finally:
            shutil.rmtree(d, ignore_errors=True)


def leanpy_extract():
    """The extractor module, loaded the way leanpy loads it."""
    spec = importlib.util.spec_from_loader(
        "leanpy_extract", importlib.machinery.SourceFileLoader(
            "leanpy_extract", os.path.join(REPO_ROOT, "extractors/python/extract.py")))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


if __name__ == "__main__":
    unittest.main(verbosity=2)
