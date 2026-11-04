#!/usr/bin/env python3
"""Check CI self-test reporting without sourcing or running the CI script."""

import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest


CI_SCRIPT = pathlib.Path(__file__).resolve().with_name("ci.sh")


def isolated_helper():
    source = CI_SCRIPT.read_text(encoding="utf-8")
    start = source.index("selftest_report() {")
    stop = source.index("\nselftests() {", start)
    return source[start:stop] + '\nselftest_report "$@"\n'


class SelftestReportingTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="ci-report-test-")
        self.addCleanup(directory.cleanup)
        self.root = pathlib.Path(directory.name)
        self.output_directory = self.root / "output"
        self.output_directory.mkdir()
        self.helper = isolated_helper()

    def run_helper(self, command, name="bounded-probe", tmpdir=None):
        environment = dict(os.environ)
        environment["TMPDIR"] = str(tmpdir or self.output_directory)
        return subprocess.run(
            ["bash", "-c", self.helper, "isolated-ci-selftest", name] + command,
            cwd=self.root, env=environment, capture_output=True, text=True, timeout=10,
        )

    def python_command(self, source):
        return [sys.executable, "-c", source]

    def assert_output_files_removed(self):
        self.assertEqual(list(self.output_directory.iterdir()), [])

    def marker_command(self, marker):
        return self.python_command(
            "import pathlib; pathlib.Path({!r}).write_text('child ran')".format(str(marker))
        )

    def test_success_is_quiet_even_when_the_child_writes_both_streams(self):
        command = self.python_command(
            "import sys; print('stdout hidden', flush=True); "
            "print('stderr hidden', file=sys.stderr, flush=True)"
        )
        completed = self.run_helper(command)
        self.assertEqual(completed.returncode, 0)
        self.assertEqual(completed.stdout, "")
        self.assertEqual(completed.stderr, "")
        self.assert_output_files_removed()

    def test_failure_reports_the_name_exact_status_and_both_streams(self):
        command = self.python_command(
            "import sys; print('stdout retained', flush=True); "
            "print('stderr retained', file=sys.stderr, flush=True); sys.exit(7)"
        )
        completed = self.run_helper(command, name="triad.sh diagnostic")
        self.assertEqual(completed.returncode, 1)
        self.assertEqual(
            completed.stdout,
            "    SELF-TEST FAILED: triad.sh diagnostic (exit 7)\n"
            "stdout retained\nstderr retained\n",
        )
        self.assertEqual(completed.stderr, "")
        self.assert_output_files_removed()

    def test_failure_output_is_not_deduplicated_or_truncated(self):
        command = self.python_command(
            "import sys; print('first failure\\nfirst failure\\nlast failure', flush=True); "
            "sys.exit(7)"
        )
        completed = self.run_helper(command)
        self.assertEqual(completed.returncode, 1)
        self.assertTrue(completed.stdout.endswith("first failure\nfirst failure\nlast failure\n"))
        self.assert_output_files_removed()

    def test_timeout_reports_status_124_and_preserves_partial_output(self):
        timeout = shutil.which("timeout")
        self.assertIsNotNone(timeout, "CI reporting tests require the existing timeout command")
        command = [timeout, "1", "bash", "-c", "printf '%s\\n' before-timeout; exec sleep 30"]
        completed = self.run_helper(command, name="timed-probe")
        self.assertEqual(completed.returncode, 1)
        self.assertEqual(
            completed.stdout,
            "    SELF-TEST FAILED: timed-probe (exit 124)\nbefore-timeout\n",
        )
        self.assertEqual(completed.stderr, "")
        self.assert_output_files_removed()

    def test_unrelated_files_in_tmpdir_are_preserved(self):
        existing = self.output_directory / "keep.txt"
        existing.write_text("unrelated content", encoding="utf-8")
        completed = self.run_helper(self.python_command("raise SystemExit(0)"))
        self.assertEqual(completed.returncode, 0)
        self.assertEqual(completed.stdout, "")
        self.assertEqual(existing.read_text(encoding="utf-8"), "unrelated content")
        self.assertEqual(list(self.output_directory.iterdir()), [existing])

    def test_missing_tmpdir_fails_before_starting_the_child(self):
        missing = self.root / "missing-output-directory"
        marker = self.root / "missing-child-ran"
        completed = self.run_helper(self.marker_command(marker), tmpdir=missing)
        self.assertEqual(completed.returncode, 1)
        self.assertEqual(completed.stdout, "")
        self.assertNotEqual(completed.stderr, "")
        self.assertFalse(marker.exists())
        self.assertFalse(missing.exists())
        self.assert_output_files_removed()

    def test_unwritable_tmpdir_fails_before_starting_the_child(self):
        unwritable = self.root / "unwritable-output-directory"
        unwritable.mkdir()
        unwritable.chmod(0o500)
        self.addCleanup(unwritable.chmod, 0o700)
        if os.access(unwritable, os.W_OK):
            self.skipTest("current user can override directory write permissions")
        marker = self.root / "unwritable-child-ran"
        completed = self.run_helper(self.marker_command(marker), tmpdir=unwritable)
        self.assertEqual(completed.returncode, 1)
        self.assertEqual(completed.stdout, "")
        self.assertNotEqual(completed.stderr, "")
        self.assertFalse(marker.exists())
        self.assertEqual(list(unwritable.iterdir()), [])
        self.assert_output_files_removed()

    def test_non_directory_tmpdir_fails_before_starting_the_child(self):
        non_directory = self.root / "not-a-directory"
        non_directory.write_text("preserve", encoding="utf-8")
        marker = self.root / "non-directory-child-ran"
        completed = self.run_helper(self.marker_command(marker), tmpdir=non_directory)
        self.assertEqual(completed.returncode, 1)
        self.assertFalse(marker.exists())
        self.assertEqual(non_directory.read_text(encoding="utf-8"), "preserve")
        self.assert_output_files_removed()


if __name__ == "__main__":
    unittest.main()
