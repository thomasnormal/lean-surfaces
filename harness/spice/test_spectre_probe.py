#!/usr/bin/env python3
"""Exercise Spectre readiness admission without invoking a simulator."""

import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest

import spectre_probe


NODE = "lean_surfaces_spectre_ready"
LICENSE_ERROR = (
    "FATAL (SPECTRE-209): Cannot run the simulation because the required "
    "license could not be checked out"
)
READY_RAW = """Title: Spectre readiness probe
Plotname: DC operating point
Flags: real
No. Variables: 1
No. Points: 1
Variables:
0 lean_surfaces_spectre_ready voltage
Values:
0 1.000000000000000e+00
"""


class ClassifyResultTests(unittest.TestCase):
    def test_success_requires_verified_analysis_and_no_errors(self):
        for output in ("", "Spectre completed", "WARNING (SPECTRE-123): warning"):
            with self.subTest(output=output):
                self.assertEqual(spectre_probe.classify_result(0, output, True), 0)
                self.assertEqual(spectre_probe.classify_result(0, output, False), 1)

    def test_only_pinned_license_diagnostic_is_unavailable(self):
        for severity in ("FATAL", "ERROR"):
            output = LICENSE_ERROR.replace("FATAL", severity)
            with self.subTest(severity=severity):
                self.assertEqual(spectre_probe.classify_result(2, output, False), 77)

    def test_mixed_coded_or_uncoded_errors_are_hard_failures(self):
        for extra in (
            "ERROR (SPECTRE-1600): invalid deck",
            "FATAL (OTHER-209): invalid deck",
            "ERROR: could not write output",
            "Fatal: unexpected failure",
        ):
            with self.subTest(extra=extra):
                output = LICENSE_ERROR + "\n" + extra
                self.assertEqual(spectre_probe.classify_result(2, output, False), 1)

    def test_generic_license_text_cannot_trigger_a_skip(self):
        for output in (
            "license unavailable",
            "SPECTRE-209",
            "SPECTRE-209: license unavailable",
            "WARNING (SPECTRE-209): license unavailable",
            "FATAL (SPECTRE-210): license unavailable",
            "ERROR (LMF-03015): license checkout failed",
        ):
            with self.subTest(output=output):
                self.assertEqual(spectre_probe.classify_result(2, output, False), 1)

    def test_contradictory_license_results_are_hard_failures(self):
        for returncode, verified in ((0, False), (0, True), (2, True)):
            with self.subTest(returncode=returncode, verified=verified):
                self.assertEqual(
                    spectre_probe.classify_result(returncode, LICENSE_ERROR, verified), 1
                )

    def test_signal_or_unexplained_exit_is_not_unavailable(self):
        for returncode, output in (
            (-signal.SIGTERM, LICENSE_ERROR),
            (1, ""),
            (127, "command failed"),
        ):
            with self.subTest(returncode=returncode, output=output):
                self.assertEqual(
                    spectre_probe.classify_result(returncode, output, False), 1
                )

    def test_artifact_cannot_hide_zero_exit_errors(self):
        for output in (
            LICENSE_ERROR,
            "ERROR (SPECTRE-1600): invalid deck",
            "ERROR: could not write output",
        ):
            with self.subTest(output=output):
                self.assertEqual(spectre_probe.classify_result(0, output, True), 1)


class AnalysisReadyTests(unittest.TestCase):
    def setUp(self):
        self.temporary_directory = tempfile.TemporaryDirectory(
            prefix="spectre-analysis-tests-"
        )
        self.addCleanup(self.temporary_directory.cleanup)
        self.rawfile = Path(self.temporary_directory.name) / "probe.raw"

    def test_exact_one_volt_analysis_is_ready(self):
        self.rawfile.write_text(READY_RAW)
        self.assertTrue(spectre_probe.analysis_ready(self.rawfile))

    def test_missing_malformed_or_inconsistent_analysis_is_not_ready(self):
        self.assertFalse(spectre_probe.analysis_ready(self.rawfile))
        for text in (
            "",
            READY_RAW.replace("No. Points: 1", "No. Points: 0"),
            READY_RAW.replace("No. Points: 1", "No. Points: 2"),
            READY_RAW.replace("No. Points: 1\n", ""),
            READY_RAW.replace("No. Variables: 1", "No. Variables: 2"),
            READY_RAW.replace(NODE, "another_node"),
            READY_RAW.replace("0 1.000000000000000e+00", "1 1.0"),
            READY_RAW + "1 1.0\n",
        ):
            with self.subTest(text=text):
                self.rawfile.write_text(text)
                self.assertFalse(spectre_probe.analysis_ready(self.rawfile))

    def test_duplicate_ready_node_is_not_verified(self):
        text = READY_RAW.replace("No. Variables: 1", "No. Variables: 2")
        text = text.replace("Values:", "1 %s voltage\nValues:" % NODE)
        text = text.replace("0 1.000000000000000e+00", "0 1.0 1.0")
        self.rawfile.write_text(text)
        self.assertFalse(spectre_probe.analysis_ready(self.rawfile))

    def test_wrong_or_nonfinite_voltage_is_not_ready(self):
        for value in ("0", "1.000001", "nan", "inf", "-inf", "invalid"):
            with self.subTest(value=value):
                self.rawfile.write_text(
                    READY_RAW.replace("1.000000000000000e+00", value)
                )
                self.assertFalse(spectre_probe.analysis_ready(self.rawfile))


class ProbeSpectreTests(unittest.TestCase):
    def setUp(self):
        self.temporary_directory = tempfile.TemporaryDirectory(
            prefix="spectre-probe-tests-"
        )
        self.addCleanup(self.temporary_directory.cleanup)
        self.directory = Path(self.temporary_directory.name)

    def executable(self, source):
        binary = self.directory / "spectre stub"
        binary.write_text("#!%s\n" % sys.executable + source, encoding="utf-8")
        binary.chmod(0o755)
        return str(binary)

    def write_raw_source(self, raw):
        return (
            "import pathlib, sys\n"
            "raw = pathlib.Path(sys.argv[sys.argv.index('-raw') + 1])\n"
            "raw.write_text(%r)\n" % raw
        )

    def test_real_analysis_command_and_both_streams_are_preserved(self):
        record = self.directory / "invocation.json"
        binary = self.executable(
            self.write_raw_source(READY_RAW)
            + "import json, os\n"
            + "source = pathlib.Path(sys.argv[-1])\n"
            + "record = {'arguments': sys.argv[1:], 'source': source.read_text(),\n"
            + "          'pid': os.getpid(), 'session': os.getsid(0)}\n"
            + "pathlib.Path(%r).write_text(json.dumps(record))\n" % str(record)
            + "print('stdout diagnostic')\n"
            + "print('stderr diagnostic', file=sys.stderr)\n"
        )
        status, output = spectre_probe.probe_spectre(binary, timeout=5)
        self.assertEqual(status, 0)
        self.assertIn("stdout diagnostic", output)
        self.assertIn("stderr diagnostic", output)
        observed = json.loads(record.read_text(encoding="utf-8"))
        arguments = observed["arguments"]
        self.assertIn("-log", arguments)
        for option, expected in (
            ("-format", "nutascii"), ("+lqtimeout", "1"), ("+lqsleep", "1")
        ):
            with self.subTest(option=option):
                self.assertEqual(arguments[arguments.index(option) + 1], expected)
        for option in ("-raw", "-outdir"):
            self.assertTrue(Path(arguments[arguments.index(option) + 1]).is_absolute())
        self.assertIn(".op", observed["source"].lower().splitlines())
        self.assertIn(NODE, observed["source"])
        if os.name == "posix":
            self.assertEqual(observed["pid"], observed["session"])

    def test_license_diagnostic_and_stderr_are_retained(self):
        binary = self.executable(
            "import sys\n"
            "print(%r)\n" % LICENSE_ERROR
            + "print('checkout diagnostic', file=sys.stderr)\n"
            + "sys.exit(2)\n"
        )
        status, output = spectre_probe.probe_spectre(binary, timeout=5)
        self.assertEqual(status, 77)
        self.assertIn(LICENSE_ERROR, output)
        self.assertIn("checkout diagnostic", output)

    def test_stderr_error_cannot_hide_behind_stdout_license_failure(self):
        error = "ERROR (SPECTRE-1600): invalid deck"
        binary = self.executable(
            "import sys\n"
            "print(%r)\n" % LICENSE_ERROR
            + "print(%r, file=sys.stderr)\n" % error
            + "sys.exit(2)\n"
        )
        status, output = spectre_probe.probe_spectre(binary, timeout=5)
        self.assertEqual(status, 1)
        self.assertIn(error, output)

    def test_zero_exit_without_valid_analysis_is_a_hard_failure(self):
        for raw in (None, "", READY_RAW.replace("1.000000000000000e+00", "2.0")):
            with self.subTest(raw=raw):
                source = "print('Spectre completed')\n"
                if raw is not None:
                    source += self.write_raw_source(raw)
                status, output = spectre_probe.probe_spectre(
                    self.executable(source), timeout=5
                )
                self.assertEqual(status, 1)
                self.assertIn("Spectre completed", output)

    def test_artifact_and_zero_exit_cannot_hide_error_diagnostics(self):
        binary = self.executable(
            self.write_raw_source(READY_RAW) + "print(%r)\n" % LICENSE_ERROR
        )
        status, output = spectre_probe.probe_spectre(binary, timeout=5)
        self.assertEqual(status, 1)
        self.assertIn(LICENSE_ERROR, output)

    def test_spawn_failure_is_hard_failure(self):
        status, output = spectre_probe.probe_spectre(
            str(self.directory / "missing-spectre"), timeout=5
        )
        self.assertEqual(status, 1)
        self.assertTrue(output)

    def test_unterminated_stdout_cannot_hide_stderr_errors(self):
        for stdout, raw, returncode in (
            (LICENSE_ERROR, None, 2),
            ("Spectre banner", READY_RAW, 0),
        ):
            with self.subTest(stdout=stdout, returncode=returncode):
                source = "import sys\n"
                if raw is not None:
                    source += self.write_raw_source(raw)
                source += (
                    "sys.stdout.write(%r)\n" % stdout
                    + "print('ERROR (SPECTRE-1600): invalid deck', file=sys.stderr)\n"
                    + "sys.exit(%s)\n" % returncode
                )
                binary = self.executable(source)
                status, output = spectre_probe.probe_spectre(binary, timeout=5)
                self.assertEqual(status, 1)
                self.assertIn("ERROR (SPECTRE-1600)", output)

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
            status, output = spectre_probe.probe_spectre(binary, timeout=1.5)
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
