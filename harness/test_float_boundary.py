#!/usr/bin/env python3
"""Check exact binary64 transport and fail-closed runner decoding."""

import json
from pathlib import Path
import subprocess
import tempfile
import unittest


REPO_ROOT = Path(__file__).resolve().parent.parent
RUNNER = REPO_ROOT / ".lake/build/bin/leanmodels-run"
ENVELOPE = REPO_ROOT / "Examples/python/float_lab/float_lab.json"


class FloatBoundaryTests(unittest.TestCase):
    def run_words(self, words, expected_exit=0):
        jobs = [{"path": str(ENVELOPE), "function": "default",
                 "args": [{"t": "float", "bits": word}]} for word in words]
        with tempfile.NamedTemporaryFile(mode="w", suffix=".jsonl") as batch:
            batch.write("\n".join(json.dumps(job) for job in jobs))
            batch.flush()
            result = subprocess.run([str(RUNNER), "--batch", batch.name],
                                    capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, expected_exit, result.stderr)
        rows = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(len(rows), len(words))
        return rows

    def test_representative_binary64_words_are_preserved(self):
        words = ["0", "1", "9223372036854775808", "9218868437227405312",
                 "9221120237041090561", "18446744073709551615"]
        for word, row in zip(words, self.run_words(words)):
            with self.subTest(word=word):
                self.assertEqual(row["status"], "ok")
                self.assertEqual(row["value"], {"t": "float", "bits": word})

    def test_invalid_words_are_rejected_not_truncated(self):
        words = ["-1", "18446744073709551616", "1.5", "nan", ""]
        for word, row in zip(words, self.run_words(words, expected_exit=1)):
            with self.subTest(word=word):
                self.assertEqual(row["status"], "runner-error")
                self.assertIn("float", row["msg"])


if __name__ == "__main__":
    unittest.main()
