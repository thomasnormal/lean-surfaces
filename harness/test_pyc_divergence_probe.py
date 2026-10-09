#!/usr/bin/env python3
"""Python 3.9-compatible behavioral regressions for the Python divergence probe."""

import contextlib
import importlib.util
import io
import os
import unittest
from unittest import mock


def load_probe():
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "pyc_divergence_probe.py")
    spec = importlib.util.spec_from_file_location("pyc_probe_under_test", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class PycDivergenceProbeTests(unittest.TestCase):
    def setUp(self):
        self.probe = load_probe()
        self.statuses = ["created", "suspended", "running", "closed", "failed"]

    def test_constructor_cannot_hide_measured_divergence(self):
        measured = ((1, "first-raised"), (0, "first-raised\nDEFAULT"))
        for statuses in (self.statuses[:-1], self.statuses):
            with self.subTest(statuses=statuses):
                with mock.patch.object(self.probe, "_run_both", return_value=measured), \
                        mock.patch.object(self.probe, "_genstatus_constructors",
                                          return_value=statuses):
                    held, detail = self.probe.pyc_div_1_still_divergent()
                self.assertIs(held, True, detail)

    def test_both_raise_is_not_divergent(self):
        measured = ((1, "first-raised"), (1, "first-raised"))
        with mock.patch.object(self.probe, "_run_both", return_value=measured), \
                mock.patch.object(self.probe, "_genstatus_constructors",
                                  return_value=self.statuses):
            held, detail = self.probe.pyc_div_1_still_divergent()
        self.assertIs(held, False, detail)

    def test_unavailable_run_stays_unverified(self):
        with mock.patch.object(self.probe, "_run_both", return_value=None), \
                mock.patch.object(self.probe, "_genstatus_constructors",
                                  return_value=self.statuses):
            held, detail = self.probe.pyc_div_1_still_divergent()
        self.assertIsNone(held)
        self.assertIn("could not run", detail)

    def test_fresh_cursor_control_agrees(self):
        measured = ((0, "first-raised\n1"), (0, "first-raised 1"))
        with mock.patch.object(self.probe, "_run_both", return_value=measured):
            held, detail = self.probe.pyc_div_1_has_not_widened()
        self.assertIs(held, True, detail)

    def test_fresh_cursor_control_rejects_mismatch_or_failure(self):
        measurements = (
            ((0, "first-raised\n1"), (0, "first-raised\n2")),
            ((0, "first-raised\n1"), (1, "first-raised\n1")),
            ((1, "first-raised\n1"), (0, "first-raised\n1")),
            ((1, "first-raised\n1"), (1, "first-raised\n1")),
        )
        for measured in measurements:
            with self.subTest(measured=measured):
                with mock.patch.object(self.probe, "_run_both", return_value=measured):
                    held, detail = self.probe.pyc_div_1_has_not_widened()
                self.assertIs(held, False, detail)

    def test_fresh_cursor_unavailable_stays_unverified(self):
        with mock.patch.object(self.probe, "_run_both", return_value=None):
            held, detail = self.probe.pyc_div_1_has_not_widened()
        self.assertIsNone(held)
        self.assertIn("could not run", detail)

    def test_both_divergences_are_retired(self):
        expected = {
            "pyc_div_1_still_divergent", "pyc_div_1_has_not_widened",
            "pyc_div_2_still_divergent", "pyc_div_2_has_not_widened",
        }
        self.assertFalse(self.probe.LIVE_GUARDS)
        self.assertEqual(set(self.probe.RETIRED_GUARDS), expected)
        self.assertEqual(set(self.probe.GUARDS), expected)

    def run_main_with_measurements(self, first_measurement):
        measurements = {
            self.probe.DIV1_SRC: first_measurement,
            self.probe.DIV1_CTL_SRC: ((0, "first-raised\n1"),
                                     (0, "first-raised\n1")),
            self.probe.DIV2_SRC: ((1, ""), (1, "")),
            self.probe.DIV2_CTL_SRC: ((1, "1"), (1, "1")),
        }
        output = io.StringIO()
        with mock.patch.object(self.probe, "_run_both", side_effect=measurements.get), \
                mock.patch.object(self.probe, "_genstatus_constructors",
                                  return_value=self.statuses), \
                contextlib.redirect_stdout(output):
            result = self.probe.main()
        return result, output.getvalue()

    def test_retired_bug_rings_alarm_even_with_failed_constructor(self):
        result, output = self.run_main_with_measurements(
            ((1, "first-raised"), (0, "first-raised\nDEFAULT")))
        self.assertEqual(result, 1, output)
        self.assertIn("REGRESSION", output)
        self.assertIn("pyc_div_1_still_divergent", output)

    def test_fixed_behavior_leaves_retired_watch_green(self):
        result, output = self.run_main_with_measurements(
            ((1, "first-raised"), (1, "first-raised")))
        self.assertEqual(result, 0, output)
        self.assertNotIn("REGRESSION", output)
        self.assertIn("pyc_divergence_probe: PASS", output)

    def test_unavailable_main_reports_unverified_measurements(self):
        output = io.StringIO()
        with mock.patch.object(self.probe, "_run_both", return_value=None), \
                mock.patch.object(self.probe, "_genstatus_constructors",
                                  return_value=self.statuses), \
                mock.patch.object(self.probe.sys, "argv", ["probe", "--json"]), \
                mock.patch.object(self.probe.json, "dumps",
                                  wraps=self.probe.json.dumps) as dump, \
                contextlib.redirect_stdout(output):
            self.probe.main()
        self.assertEqual(dump.call_count, 1)
        results = dump.call_args.args[0]
        self.assertEqual(set(results), set(self.probe.GUARDS))
        for result in results.values():
            self.assertIs(result["verified"], False)
            self.assertIs(result["held"], False)
        self.assertIn("no-run", output.getvalue())
        self.assertNotIn("REGRESSION", output.getvalue())


if __name__ == "__main__":
    unittest.main()
