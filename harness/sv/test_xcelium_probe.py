#!/usr/bin/env python3
"""Exercise Xcelium readiness admission without invoking a simulator."""

import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest

import xcelium_probe


READY = "LEAN_SURFACES_XCELIUM_READY"
LICENSE_ERROR = "xmsim: *F,NOLICN: Unable to checkout a simulation license."


class ClassifyResultTests(unittest.TestCase):
    def test_exact_completion_marker_admits_success(self):
        for output in (READY, READY + "\n", "tool banner\n" + READY + "\n"):
            with self.subTest(output=output):
                self.assertEqual(xcelium_probe.classify_result(0, output), 0)

    def test_success_without_exact_marker_is_a_hard_error(self):
        for output in ("", "finished successfully", " " + READY,
                       READY + " suffix", "prefix " + READY):
            with self.subTest(output=output):
                self.assertEqual(xcelium_probe.classify_result(0, output), 1)

    def test_nonzero_with_no_completion_is_not_success(self):
        for returncode in (1, 2, 127, -signal.SIGTERM):
            with self.subTest(returncode=returncode):
                self.assertEqual(
                    xcelium_probe.classify_result(returncode, "tool failed"), 1
                )

    def test_only_pinned_license_error_is_unavailable(self):
        for severity in ("F", "E"):
            output = "xmsim: *%s,NOLICN: license checkout failed\nLMF-03015" % severity
            with self.subTest(severity=severity):
                self.assertEqual(xcelium_probe.classify_result(1, output), 77)

    def test_warning_does_not_turn_license_absence_into_failure(self):
        output = LICENSE_ERROR + "\nxrun: *W,NOTICE: tool warning\n"
        self.assertEqual(xcelium_probe.classify_result(1, output), 77)

    def test_unrelated_fatal_or_error_is_hard_failure(self):
        for severity in ("F", "E"):
            output = "xrun: *%s,ELABERR: invalid module" % severity
            with self.subTest(severity=severity):
                self.assertEqual(xcelium_probe.classify_result(1, output), 1)

    def test_mixed_license_and_real_errors_remain_hard_failure(self):
        for severity in ("F", "E"):
            output = LICENSE_ERROR + "\nxrun: *%s,ELABERR: invalid module" % severity
            with self.subTest(severity=severity):
                self.assertEqual(xcelium_probe.classify_result(1, output), 1)

    def test_generic_license_text_cannot_trigger_a_skip(self):
        for output in ("license server unavailable", "NOLICN", "LMF-03015",
                       "xmsim: NOLICN: license absent",
                       "xmsim: *W,NOLICN: license warning"):
            with self.subTest(output=output):
                self.assertEqual(xcelium_probe.classify_result(1, output), 1)

    def test_marker_cannot_hide_nonzero_or_real_errors(self):
        for returncode, output in (
            (1, READY),
            (1, READY + "\n" + LICENSE_ERROR),
            (0, READY + "\n" + LICENSE_ERROR),
            (0, READY + "\nxrun: *F,ELABERR: invalid module"),
            (0, READY + "\nxrun: *E,ELABERR: invalid module"),
        ):
            with self.subTest(returncode=returncode, output=output):
                self.assertEqual(
                    xcelium_probe.classify_result(returncode, output), 1
                )

    def test_zero_exit_with_license_error_is_not_unavailable(self):
        self.assertEqual(xcelium_probe.classify_result(0, LICENSE_ERROR), 1)

    def test_signal_termination_with_license_text_remains_hard_failure(self):
        self.assertEqual(
            xcelium_probe.classify_result(-signal.SIGTERM, LICENSE_ERROR), 1
        )


class ProbeXceliumTests(unittest.TestCase):
    def setUp(self):
        self.temporary_directory = tempfile.TemporaryDirectory(
            prefix="xcelium-probe-tests-"
        )
        self.addCleanup(self.temporary_directory.cleanup)
        self.directory = Path(self.temporary_directory.name)

    def executable(self, source):
        binary = self.directory / "xrun stub"
        binary.write_text(
            "#!%s\n" % sys.executable + source,
            encoding="utf-8",
        )
        binary.chmod(0o755)
        return str(binary)

    def test_probe_runs_real_sv_and_preserves_stream_diagnostics(self):
        record = self.directory / "invocation.json"
        binary = self.executable(
            "import json, os, pathlib, sys\n"
            "sources = {argument: pathlib.Path(argument).read_text()\n"
            "           for argument in sys.argv[1:] if argument.endswith('.sv')}\n"
            "record = {'arguments': sys.argv[1:], 'sources': sources,\n"
            "          'pid': os.getpid(), 'session': os.getsid(0)}\n"
            "pathlib.Path(%r).write_text(json.dumps(record))\n" % str(record)
            + "print(%r)\n" % READY
            + "print('stdout diagnostic')\n"
            + "print('stderr diagnostic', file=sys.stderr)\n"
        )
        status, output = xcelium_probe.probe_xcelium(binary, timeout=5)
        self.assertEqual(status, 0)
        self.assertIn("stdout diagnostic", output)
        self.assertIn("stderr diagnostic", output)
        observed = json.loads(record.read_text(encoding="utf-8"))
        self.assertIn("-sv", observed["arguments"])
        self.assertTrue(observed["sources"])
        source = "\n".join(observed["sources"].values())
        for required in ("module", "$display", READY, "$finish"):
            with self.subTest(required=required):
                self.assertIn(required, source)
        if os.name == "posix":
            self.assertEqual(observed["pid"], observed["session"])

    def test_license_diagnostics_from_stdout_and_stderr_are_retained(self):
        binary = self.executable(
            "import sys\n"
            "print(%r)\n" % LICENSE_ERROR
            + "print('LMF-03015: license checkout failed', file=sys.stderr)\n"
            + "sys.exit(1)\n"
        )
        status, output = xcelium_probe.probe_xcelium(binary, timeout=5)
        self.assertEqual(status, 77)
        self.assertIn(LICENSE_ERROR, output)
        self.assertIn("LMF-03015", output)

    def test_probe_reads_license_diagnostics_from_xrun_log(self):
        binary = self.executable(
            "import pathlib, sys\n"
            "pathlib.Path('xrun.log').write_text(%r)\n" % LICENSE_ERROR
            + "sys.exit(1)\n"
        )
        status, output = xcelium_probe.probe_xcelium(binary, timeout=5)
        self.assertEqual(status, 77)
        self.assertIn(LICENSE_ERROR, output)

    def test_xrun_log_error_cannot_be_hidden_by_stdout_license_error(self):
        real_error = "xrun: *E,ELABERR: invalid module"
        binary = self.executable(
            "import pathlib, sys\n"
            "print(%r)\n" % LICENSE_ERROR
            + "pathlib.Path('xrun.log').write_text(%r)\n" % real_error
            + "sys.exit(1)\n"
        )
        status, output = xcelium_probe.probe_xcelium(binary, timeout=5)
        self.assertEqual(status, 1)
        self.assertIn(real_error, output)

    def test_probe_success_without_marker_is_hard_failure(self):
        binary = self.executable("print('finished without readiness marker')\n")
        status, output = xcelium_probe.probe_xcelium(binary, timeout=5)
        self.assertEqual(status, 1)
        self.assertIn("finished without readiness marker", output)

    def test_spawn_failure_is_hard_failure(self):
        missing = str(self.directory / "missing-xrun")
        status, output = xcelium_probe.probe_xcelium(missing, timeout=5)
        self.assertEqual(status, 1)
        self.assertTrue(output)

    @unittest.skipUnless(os.name == "posix", "process groups require POSIX")
    def test_timeout_kills_the_whole_child_process_group(self):
        record = self.directory / "processes.json"
        binary = self.executable(
            "import json, os, pathlib, subprocess, sys, time\n"
            "child = subprocess.Popen([sys.executable, '-c',\n"
            "                          'import time; time.sleep(60)'])\n"
            "record = {'parent': os.getpid(), 'child': child.pid}\n"
            "pathlib.Path(%r).write_text(json.dumps(record))\n" % str(record)
            + "print('probe started', flush=True)\n"
            + "print(%r, flush=True)\n" % LICENSE_ERROR
            + "time.sleep(60)\n"
        )
        started = time.monotonic()
        try:
            status, output = xcelium_probe.probe_xcelium(binary, timeout=1.5)
        finally:
            if record.exists():
                observed = json.loads(record.read_text(encoding="utf-8"))
                self.addCleanup(self.kill_group, observed["parent"])
        self.assertEqual(status, 1)
        self.assertLess(time.monotonic() - started, 10)
        self.assertIn("probe started", output)
        self.assertIn("timed out", output.lower())
        self.assertIn(LICENSE_ERROR, output)
        observed = json.loads(record.read_text(encoding="utf-8"))
        deadline = time.monotonic() + 3
        while self.running(observed["child"]) and time.monotonic() < deadline:
            time.sleep(0.05)
        self.assertFalse(self.running(observed["parent"]))
        self.assertFalse(self.running(observed["child"]))

    def kill_group(self, process):
        try:
            os.killpg(process, signal.SIGKILL)
        except ProcessLookupError:
            pass

    def running(self, process):
        result = subprocess.run(
            ["ps", "-o", "stat=", "-p", str(process)],
            capture_output=True,
            text=True,
            timeout=5,
        )
        state = result.stdout.strip()
        return bool(state) and not state.startswith("Z")


if __name__ == "__main__":
    unittest.main()
