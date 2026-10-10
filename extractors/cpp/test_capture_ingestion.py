#!/usr/bin/env python3
"""Bounded same-byte capture ingestion checks; no C++ semantic admission.

LEANCPP_TEST_LEAN=1 enables the built Lean loader/parser checks. The successful
fixture is emitted by the capture runner using the existing synthetic frontend
helper; it is not a fabricated status-free receipt or a real compiler oracle.
The real compiler control additionally requires explicit matching LEANCPP_CLANG
and LEANCPP_PROBE_LIBRARY; LEANCPP_RUNTIME_LIBRARIES is an optional JSON array.
Every Lean subprocess has a 60-second timeout. No CI registration occurs here.
The Lake-selected executable and import path are materialized once per class;
no parser, loader, compiler result, or source artifact is cached.
"""

import copy
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import capture_probe
from test_capture_probe import SOURCE, fake_frontend_text
from test_evidence_ingestion import document, function_row


REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]


def observed_probe_bytes():
    first = function_row()
    second = copy.deepcopy(first)
    second["definition"] = True
    second["canonical"] = "0xdead"
    serialized = json.dumps(document([first, second]), ensure_ascii=False)
    return serialized.replace(
        '"inner": []', '"inner": [], "huge": 9007199254740993, "zero": -0',
    ).encode("utf-8") + b"\n"


def runner_fixture(root):
    source = root / "input.cpp"
    source.write_text(SOURCE, encoding="utf-8")
    header = root / "header.hpp"
    header.write_text("int header_value;\n", encoding="utf-8")
    plugin = root / "probe.so"
    plugin.write_bytes(b"synthetic-plugin")
    resource = root / "resource"
    resource.mkdir()
    compiler = root / "clang++"
    compiler.write_text(
        fake_frontend_text(resource, header, observed_probe_bytes(), "success"),
        encoding="utf-8",
    )
    compiler.chmod(0o755)
    with mock.patch.dict(os.environ, {}, clear=True):
        return capture_probe.capture(
            source, root / "bundle", clang=str(compiler), plugin=plugin,
            timeout=5, memory_mib=256,
        )


def changed_record(record, path, value):
    result = copy.deepcopy(record)
    selected = result
    for key in path[:-1]:
        selected = selected[key]
    selected[path[-1]] = value
    return result


def lean_launch(lake):
    result = subprocess.run(
        [lake, "env", "sh", "-c", 'printf "%s\\n" "$LEAN_PATH"; command -v lean'],
        cwd=REPO_ROOT, capture_output=True, text=True, timeout=60,
    )
    lines = result.stdout.splitlines()
    if result.returncode != 0 or len(lines) != 2 or not all(lines):
        raise RuntimeError("cannot materialize Lake Lean launcher: " + result.stdout + result.stderr)
    return lines[1], dict(os.environ, LEAN_PATH=lines[0])


class CaptureIngestionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if os.environ.get("LEANCPP_TEST_LEAN") != "1":
            raise unittest.SkipTest("set LEANCPP_TEST_LEAN=1 for built capture ingestion checks")
        cls.lake = shutil.which("lake")
        if cls.lake is None:
            raise RuntimeError("capture ingestion checks require lake on PATH")
        cls.lean, cls.lean_environment = lean_launch(cls.lake)
        cls.fixture_directory = tempfile.TemporaryDirectory(prefix="cpp-capture-ingestion-base-")
        cls.addClassCleanup(cls.fixture_directory.cleanup)
        cls.base = runner_fixture(pathlib.Path(cls.fixture_directory.name))
        cls.original = json.loads((cls.base / "capture.json").read_text(encoding="utf-8"))

    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="cpp-capture-ingestion-")
        self.addCleanup(directory.cleanup)
        self.root = pathlib.Path(directory.name)
        self.bundle = self.root / "bundle"
        shutil.copytree(self.base, self.bundle)
        self.receipt = copy.deepcopy(self.original)

    def write_receipt(self, contents=None):
        path = self.bundle / "capture.json"
        if contents is None:
            contents = json.dumps(self.receipt, ensure_ascii=False).encode("utf-8") + b"\n"
        path.write_bytes(contents)

    def run_lean(self, commands):
        lean_path = self.root / "Check.lean"
        lean_path.write_text(
            "import LeanModels.Cpp.CaptureLoad\nopen LeanModels.Cpp\n"
            "namespace CaptureIngestionFixture\n" + commands
            + "\nend CaptureIngestionFixture\n", encoding="utf-8",
        )
        return subprocess.run(
            [self.lean, str(lean_path)], cwd=REPO_ROOT,
            capture_output=True, text=True, timeout=60, env=self.lean_environment,
        )

    def run_loader(self, guards=""):
        return self.run_lean(
            "load_cpp_capture observed from " + json.dumps(str(self.bundle))
            + "\n" + guards,
        )

    def assert_accepts(self, guards=""):
        result = self.run_loader(guards)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def assert_refuses(self):
        result = self.run_loader()
        self.assertNotEqual(result.returncode, 0, "invalid capture bundle was admitted")
        self.assertIn("load_cpp_capture:", result.stdout + result.stderr)

    def assert_parser_refuses(self, records):
        paths = []
        for ordinal, record in enumerate(records):
            path = self.root / ("receipt-" + str(ordinal) + ".json")
            contents = record if isinstance(record, str) else json.dumps(record)
            path.write_text(contents, encoding="utf-8")
            paths.append(str(path))
        commands = "#eval do\n  let paths : List String := " + json.dumps(paths) + "\n"
        commands += """  for path in paths do
    let contents ← IO.FS.readFile ⟨path⟩
    match parseCaptureReceiptString contents with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"invalid receipt admitted: {path}")
"""
        result = self.run_lean(commands)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def rebind_payload(self, key, contents):
        binding = self.receipt["payloads"][key]
        (self.bundle / binding["path"]).write_bytes(contents)
        binding["sha256"] = hashlib.sha256(contents).hexdigest()
        binding["byte_count"] = len(contents)
        self.write_receipt()

    def test_runner_bundle_loads_as_literals_without_semantic_promotion(self):
        self.assert_accepts("""
#guard observed.probe.declarations.length == 2
#guard observed.probe.declarations.map (·.ordinal) == [0, 1]
#guard observed.probe.declarations.map (fun row => row.functionShape.map (·.definition)) ==
  [some false, some true]
#guard observed.probe.declarations.map (fun row => row.id.value) == ["0x2", "0x2"]
#guard observed.probe.declarations.map (fun row => row.canonical.value) == ["0x2", "0xdead"]
#guard observed.probe.ast.field "huge" == some (.number "9007199254740993")
#guard observed.probe.ast.field "zero" == some (.number "-0")
#guard observed.receipt.payloads.length == 14
#guard (observed.receipt.raw.field "closure_limits").bind (·.field "semantic_admission") ==
  some (.bool false)
#guard (observed.receipt.raw.field "closure_limits").bind (·.field "runtime_admission") ==
  some (.bool false)
""")

    def test_receipt_telemetry_decimal_exponent_lexemes_remain_exact(self):
        contents = json.dumps(self.receipt).replace(
            '"schema_version":', '"observational_telemetry":1.250e+02,"negative_zero":-0,"schema_version":',
            1,
        )
        self.write_receipt(contents.encode("utf-8"))
        self.assert_accepts("""
#guard observed.receipt.raw.field "observational_telemetry" == some (.number "1.250e+02")
#guard observed.receipt.raw.field "negative_zero" == some (.number "-0")
""")

    def test_schema_versions_and_required_groups_refuse(self):
        records = []
        for name in (
            "schema_version", "profile_id", "edition", "probe_schema", "producer",
            "payloads", "launch", "frontend", "source", "positive_inputs",
            "completion", "closure_limits",
        ):
            record = copy.deepcopy(self.receipt)
            del record[name]
            records.append(record)
        for name in ("schema_version", "profile_id", "edition", "probe_schema"):
            records.append(changed_record(self.receipt, [name], "wrong-version"))
        self.assert_parser_refuses(records)

    def test_duplicate_decoded_keys_at_every_depth_refuse(self):
        contents = json.dumps(self.receipt)
        self.assert_parser_refuses([
            '{"schema_version":"other",' + contents[1:],
            contents.replace('"semantic_admission": false',
                             '"semantic_admission":false,"semantic_admiss\\u0069on":false'),
            contents.replace('"argv": [', '"argv":[],"argv":['),
        ])

    def test_utf8_and_surrogate_receipts_refuse(self):
        for token in (b'"\xff"', b'"\\ud800"', b'"\\udfff"', b'"\\ud800x"'):
            with self.subTest(token=token):
                self.write_receipt(b'{"extra":' + token + b',' + json.dumps(self.receipt).encode()[1:])
                self.assert_refuses()

    def test_integer_payload_counts_and_hash_domain_are_exact(self):
        records = []
        for value in (-1, True, "12", None, [], {}):
            records.append(changed_record(self.receipt, ["payloads", "probe", "byte_count"], value))
        for value in ("", "f" * 63, "g" * 64, "A" * 64, True, None):
            records.append(changed_record(self.receipt, ["payloads", "probe", "sha256"], value))
        serialized = json.dumps(self.receipt)
        original = '"byte_count": ' + str(self.receipt["payloads"]["probe"]["byte_count"])
        for token in ("-0", "1.0", "1e0"):
            payload = json.dumps(self.receipt["payloads"]["probe"])
            changed = payload.replace(original, '"byte_count": ' + token)
            records.append(serialized.replace(payload, changed))
        self.assert_parser_refuses(records)

    def test_nonfinite_and_malformed_receipt_numbers_refuse(self):
        contents = json.dumps(self.receipt)
        self.assert_parser_refuses([
            '{"extra":' + token + ',' + contents[1:]
            for token in ("NaN", "Infinity", "-Infinity", "01", "1.", "1e+")
        ])

    def test_process_bounds_measurements_and_counter_domains_refuse(self):
        records = []
        process_path = ["completion", "processes", 5]
        for key, value in (
            ("elapsed_seconds", -1), ("max_rss_kib", -1),
            ("max_rss_kib", True), ("max_rss_kib", None),
        ):
            records.append(changed_record(self.receipt, process_path + [key], value))
        for key, value in (
            ("timeout_seconds", 0), ("timeout_seconds", -1),
            ("timeout_seconds", "5"), ("memory_mib", 0),
            ("memory_mib", True), ("file_size_bytes", 1024),
        ):
            records.append(changed_record(self.receipt, process_path + ["bounds", key], value))
        self.assert_parser_refuses(records)

    def test_unsafe_payload_paths_and_duplicate_paths_refuse(self):
        records = [changed_record(self.receipt, ["payloads", "probe", "path"], value)
                   for value in ("", "../probe.json", "/tmp/probe.json", "a/../probe.json", "a\\probe.json")]
        records.append(changed_record(self.receipt, ["payloads", "stderr", "path"], "probe.json"))
        self.assert_parser_refuses(records)

    def test_nonzero_timeout_signal_unlaunched_or_error_status_refuses(self):
        records = [changed_record(self.receipt, ["completion", key], value)
                   for key, value in (("exit_status", 1), ("timed_out", True))]
        for ordinal in range(len(self.receipt["completion"]["processes"])):
            for key, value in (
                ("exit_status", 1), ("timed_out", True), ("signal", 9),
                ("launched", False), ("observation_error", "child survived"),
            ):
                records.append(changed_record(self.receipt, ["completion", "processes", ordinal, key], value))
        self.assert_parser_refuses(records)

    def test_closure_guarantees_and_semantic_promotion_refuse(self):
        records = [changed_record(self.receipt, ["closure_limits", name], "established")
                   for name in ("input_world", "runtime_image_closure", "effective_cc1", "ordinary_source_profile")]
        records.extend(changed_record(self.receipt, ["closure_limits", name], True)
                       for name in ("semantic_admission", "runtime_admission"))
        records.append(changed_record(self.receipt, ["closure_limits", "guarantee"], "complete-source-world"))
        self.assert_parser_refuses(records)

    def test_manifest_path_hash_and_source_coherence_refuse(self):
        records = [changed_record(self.receipt, ["positive_inputs", name], False)
                   for name in ("paths_equal", "hashes_equal")]
        records.extend([
            changed_record(self.receipt, ["positive_inputs", "actual_manifest"], []),
            changed_record(self.receipt, ["positive_inputs", "after", 0, "sha256"], "f" * 64),
            changed_record(self.receipt, ["source", "sha256"], "f" * 64),
            changed_record(self.receipt, ["source", "path"], "/not/a/positive/input.cpp"),
            changed_record(self.receipt, ["source", "logical_command_path"], "different.cpp"),
        ])
        self.assert_parser_refuses(records)

    def test_launch_and_output_reference_coherence_refuse(self):
        records = [
            changed_record(self.receipt, ["launch", "argv"], ["other-frontend"]),
            changed_record(self.receipt, ["launch", "cwd"], "/unrelated"),
            changed_record(self.receipt, ["launch", "executable"], "/wrong-frontend"),
            changed_record(self.receipt, ["completion", "processes", 0, "stdout"], "unbound.stdout"),
            changed_record(self.receipt, ["completion", "processes", 0, "stderr"], "unbound.stderr"),
        ]
        self.assert_parser_refuses(records)

    def test_missing_payload_refuses(self):
        (self.bundle / "stderr.txt").unlink()
        self.assert_refuses()

    def test_tampered_payload_same_count_refuses(self):
        path = self.bundle / "probe.json"
        original = path.read_bytes()
        changed = original.replace(b'"huge": 9007199254740993', b'"huge": 9007199254740994')
        self.assertEqual(len(original), len(changed))
        self.assertNotEqual(original, changed)
        path.write_bytes(changed)
        self.assert_refuses()

    def test_payload_count_mismatch_refuses(self):
        self.receipt["payloads"]["probe"]["byte_count"] += 1
        self.write_receipt()
        self.assert_refuses()

    def test_whitespace_reserialization_does_not_preserve_same_byte_binding(self):
        path = self.bundle / "probe.json"
        path.write_text(json.dumps(json.loads(path.read_bytes()), indent=2), encoding="utf-8")
        self.assert_refuses()

    def test_payload_symlink_escape_refuses(self):
        path = self.bundle / "probe.json"
        external = self.root / "outside.json"
        path.rename(external)
        path.symlink_to(external)
        self.assert_refuses()

    def test_receipt_symlink_escape_refuses(self):
        path = self.bundle / "capture.json"
        external = self.root / "outside-capture.json"
        path.rename(external)
        path.symlink_to(external)
        self.assert_refuses()

    def test_symlink_bundle_directory_refuses(self):
        original = self.root / "ordinary-bundle"
        self.bundle.rename(original)
        self.bundle.symlink_to(original, target_is_directory=True)
        self.assert_refuses()

    def test_bound_invalid_utf8_and_duplicate_probe_keys_refuse(self):
        contents = (self.bundle / "probe.json").read_bytes()
        for malformed in (
            contents.replace(b'"inner": []', b'"inner": [], "extra":"\xff"'),
            contents.replace(b'"inner": []', b'"inner": [], "extra":1,"extra":2'),
        ):
            with self.subTest(malformed=malformed[-30:]):
                self.rebind_payload("probe", malformed)
                self.assert_refuses()

    def test_bound_malformed_probe_typed_row_refuses(self):
        probe = json.loads((self.bundle / "probe.json").read_bytes())
        probe["metadata"]["declarations"][0]["function_has_skipped_body"] = 0
        self.rebind_payload("probe", json.dumps(probe).encode("utf-8"))
        self.assert_refuses()

    def test_bound_decimal_probe_number_still_refuses(self):
        contents = (self.bundle / "probe.json").read_bytes().replace(b'"zero": -0', b'"zero": 0.0')
        self.rebind_payload("probe", contents)
        self.assert_refuses()

    def test_bound_probe_receipt_frontend_disagreement_refuses(self):
        probe = json.loads((self.bundle / "probe.json").read_bytes())
        probe["metadata"]["runtime_frontend"] = "clang version 21.1.8 different build"
        self.rebind_payload("probe", json.dumps(probe).encode("utf-8"))
        self.assert_refuses()

    def test_source_record_does_not_authenticate_current_external_source(self):
        source = pathlib.Path(self.receipt["source"]["path"])
        original = source.read_bytes()
        try:
            source.write_bytes(b"int later(int value) { return value + 100; }\n")
            self.assert_accepts()
        finally:
            source.write_bytes(original)

    def test_original_source_and_frontend_images_need_not_remain_installed(self):
        paths = [pathlib.Path(self.receipt["source"]["path"]),
                 pathlib.Path(self.receipt["frontend"]["compiler"]["resolved_path"]),
                 pathlib.Path(self.receipt["frontend"]["plugin"]["resolved_path"])]
        retained = []
        try:
            for path in paths:
                offline = path.with_name(path.name + ".offline")
                path.rename(offline)
                retained.append((path, offline))
                self.assertFalse(path.exists())
            self.assert_accepts()
        finally:
            for path, offline in reversed(retained):
                offline.rename(path)

    def test_existing_name_is_not_redeclared(self):
        commands = "def observed : Nat := 1\nload_cpp_capture observed from " + json.dumps(str(self.bundle))
        result = self.run_lean(commands)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("already declared", result.stdout + result.stderr)


class RealCaptureIngestionTests(unittest.TestCase):
    run_lean = CaptureIngestionTests.run_lean
    run_loader = CaptureIngestionTests.run_loader

    @classmethod
    def setUpClass(cls):
        if os.environ.get("LEANCPP_TEST_LEAN") != "1":
            raise unittest.SkipTest("set LEANCPP_TEST_LEAN=1 for built capture ingestion checks")
        cls.compiler = os.environ.get("LEANCPP_CLANG")
        cls.plugin = os.environ.get("LEANCPP_PROBE_LIBRARY")
        if not cls.compiler or not cls.plugin:
            raise unittest.SkipTest("set explicit matching LEANCPP_CLANG and LEANCPP_PROBE_LIBRARY for real capture control")
        cls.lake = shutil.which("lake")
        if cls.lake is None:
            raise RuntimeError("capture ingestion checks require lake on PATH")
        cls.lean, cls.lean_environment = lean_launch(cls.lake)
        cls.runtime_libraries = json.loads(os.environ.get("LEANCPP_RUNTIME_LIBRARIES", "[]"))
        if not isinstance(cls.runtime_libraries, list) or not all(isinstance(value, str) for value in cls.runtime_libraries):
            raise RuntimeError("LEANCPP_RUNTIME_LIBRARIES must be a JSON array of paths")

    def test_pinned_real_runner_capture_loads_exact_probe_bytes(self):
        directory = tempfile.TemporaryDirectory(prefix="cpp-real-capture-ingestion-")
        self.addCleanup(directory.cleanup)
        self.root = pathlib.Path(directory.name)
        source = self.root / "input.cpp"
        source.write_text(SOURCE, encoding="utf-8")
        self.bundle = capture_probe.capture(
            source, self.root / "bundle", clang=self.compiler, plugin=self.plugin,
            runtime_libraries=self.runtime_libraries, timeout=60, memory_mib=8192,
        )
        receipt = json.loads((self.bundle / "capture.json").read_bytes())
        payload = (self.bundle / "probe.json").read_bytes()
        self.assertEqual(hashlib.sha256(payload).hexdigest(), receipt["payloads"]["probe"]["sha256"])
        self.assertEqual(len(payload), receipt["payloads"]["probe"]["byte_count"])
        result = self.run_loader("""
#guard observed.probe.functions.length == 2
#guard observed.probe.functions.map (fun row => row.functionShape.map (·.definition)) ==
  [some false, some true]
#guard (observed.receipt.raw.field "closure_limits").bind (·.field "semantic_admission") ==
  some (.bool false)
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
