#!/usr/bin/env python3
"""Regression tests for extractors/python/extract.py.

Run from anywhere: python3 extractors/python/test_extract.py
Stdlib-only, Python 3.9 compatible. Covers the extractor guarantees that
are not exercised by the Lean build:

  * header-injection regression: a source under a ``/-``-containing path
    (dash-leading directory segment, e.g. scratch roots under /tmp) must
    produce a companion whose header is ``--`` line comments — the
    block-comment form would open a nested Lean comment and corrupt the
    file;
  * the historical block-comment header is preserved byte-for-byte for
    normal paths (companions of unchanged sources regenerate byte-stably);
  * double-run determinism: same input bytes => same output bytes;
  * a source with no ``# lean[`` blocks gets an envelope and NO companion
    (three-file per-example layout);
  * a hand-written .lean at the companion path is never overwritten — hard
    ExtractError naming the file.
"""

import importlib.util
import os
import shutil
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))

spec = importlib.util.spec_from_file_location(
    "extract_under_test", os.path.join(HERE, "extract.py"))
extract = importlib.util.module_from_spec(spec)
spec.loader.exec_module(extract)

SOURCE_WITH_BLOCK = (
    "def double(x):\n"
    "    return x + x\n"
    "\n"
    "\n"
    "# lean[\n"
    "# #py_check double(21) = 42\n"
    "# ]\n"
)

SOURCE_NO_BLOCK = (
    "def double(x):\n"
    "    return x + x\n"
)


def read(path):
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def write(path, text):
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)


class ExtractorTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="extract-test-", dir="/tmp")

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    # -- the header-injection regression (the '/-' path bug) ---------------

    def test_dash_segment_path_gets_line_comment_header(self):
        # A directory segment starting with '-' makes the path contain '/-',
        # which inside a '/- ... -/' block comment opens a NESTED comment.
        srcdir = os.path.join(self.tmp, "-home-someone-project")
        os.makedirs(srcdir)
        src = os.path.join(srcdir, "double.py")
        write(src, SOURCE_WITH_BLOCK)
        extract.process_file(src, self.tmp)

        companion = os.path.join(self.tmp, "Double.lean")
        text = read(companion)
        header = text.split("import LeanModels")[0]
        self.assertIn("/-", src.replace(os.sep, "/"))  # premise of the test
        self.assertTrue(
            text.startswith("-- " + extract.AUTOGEN_MARKER),
            "dangerous path must switch the header to line comments:\n" + header,
        )
        self.assertIn("-- source: ", header)
        self.assertIn("-- sha256: ", header)
        # No block comment anywhere in the header => nothing to corrupt.
        self.assertNotIn("/-\n", header)
        # The dangerous sequence may only survive where Lean cannot read it
        # as a comment opener: inside `--` line comments and inside the
        # `load_program ... from "<path>"` string literal. (The original
        # failure mode: a bare `/-` opened an unterminated block comment.)
        for ln in text.split("\n"):
            if "/-" in ln:
                self.assertTrue(
                    ln.lstrip().startswith("--") or 'from "' in ln,
                    "raw block-comment opener leaked into the companion: %r" % ln,
                )

    def test_normal_path_keeps_block_comment_header_verbatim(self):
        src = os.path.join(self.tmp, "double.py")
        write(src, SOURCE_WITH_BLOCK)
        extract.process_file(src, self.tmp)
        text = read(os.path.join(self.tmp, "Double.lean"))
        sha = extract.hashlib.sha256(
            SOURCE_WITH_BLOCK.encode("utf-8")).hexdigest()
        expected = (
            "/-\n"
            + extract.AUTOGEN_MARKER + " — DO NOT EDIT.\n"
            + "source: " + src.replace(os.sep, "/") + "\n"
            + "sha256: " + sha + "\n"
            + "-/\n"
        )
        self.assertTrue(
            text.startswith(expected),
            "historical block-comment header must be byte-stable",
        )

    # -- determinism --------------------------------------------------------

    def test_double_run_is_byte_stable(self):
        src = os.path.join(self.tmp, "double.py")
        write(src, SOURCE_WITH_BLOCK)
        extract.process_file(src, self.tmp)
        json1 = read(os.path.join(self.tmp, "double.json"))
        lean1 = read(os.path.join(self.tmp, "Double.lean"))
        extract.process_file(src, self.tmp)
        self.assertEqual(json1, read(os.path.join(self.tmp, "double.json")))
        self.assertEqual(lean1, read(os.path.join(self.tmp, "Double.lean")))

    # -- three-file layout: no blocks => no companion ------------------------

    def test_no_lean_blocks_emits_envelope_only(self):
        src = os.path.join(self.tmp, "double.py")
        write(src, SOURCE_NO_BLOCK)
        extract.process_file(src, self.tmp)
        self.assertTrue(os.path.exists(os.path.join(self.tmp, "double.json")))
        self.assertFalse(
            os.path.exists(os.path.join(self.tmp, "Double.lean")),
            "a block-less source must not generate a companion",
        )

    # -- default companion dir: next to the source ---------------------------

    def test_default_companion_dir_is_source_dir(self):
        # Per-example layout: with companion_dir=None the companion must land
        # NEXT TO the source (Examples/python/sum_to/sum_to.py → Examples/python/sum_to/
        # SumTo.lean), not in any fixed root.
        srcdir = os.path.join(self.tmp, "sum_to")
        os.makedirs(srcdir)
        src = os.path.join(srcdir, "sum_to.py")
        write(src, SOURCE_WITH_BLOCK)
        extract.process_file(src, None)
        self.assertTrue(
            os.path.exists(os.path.join(srcdir, "SumTo.lean")),
            "default companion dir must be the source file's own directory",
        )
        self.assertFalse(os.path.exists(os.path.join(self.tmp, "SumTo.lean")))

    # -- hand-written files are never clobbered ------------------------------

    def test_refuses_to_overwrite_hand_written_lean(self):
        src = os.path.join(self.tmp, "double.py")
        write(src, SOURCE_WITH_BLOCK)
        companion = os.path.join(self.tmp, "Double.lean")
        hand_written = "-- my precious hand-written spec\ntheorem t : True := trivial\n"
        write(companion, hand_written)
        with self.assertRaises(extract.ExtractError) as ctx:
            extract.process_file(src, self.tmp)
        self.assertIn("Double.lean", str(ctx.exception))
        self.assertEqual(read(companion), hand_written, "file must be untouched")

    def test_overwrites_generated_companion(self):
        src = os.path.join(self.tmp, "double.py")
        write(src, SOURCE_WITH_BLOCK)
        extract.process_file(src, self.tmp)
        first = read(os.path.join(self.tmp, "Double.lean"))
        extract.process_file(src, self.tmp)  # must not raise
        self.assertEqual(first, read(os.path.join(self.tmp, "Double.lean")))


if __name__ == "__main__":
    unittest.main(verbosity=2)
