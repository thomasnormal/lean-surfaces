#!/usr/bin/env python3
"""Bounded observational-capture checks, not C++ semantic admission.

Synthetic frontends exercise refusal/publication behavior without LLVM. The
small real-frontend check requires explicit matching LEANCPP_CLANG and
LEANCPP_PROBE_LIBRARY selections; missing selections are an explicit skip.
LEANCPP_RUNTIME_LIBRARIES optionally supplies a JSON array of declared image
paths; those declarations never establish loaded-image closure.
"""

import copy
import hashlib
import json
import os
import pathlib
import shutil
import sys
import tempfile
import unittest
from unittest import mock


sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import capture_probe as capture
import capture_support as support


VERSION = "21.1.8"
SCHEMA = "cpp-canonical-probe-0.3"
SOURCE = "int later(int);\nint later(int value) { return value; }\n"


def probe_document():
    declaration = {
        "id": "0x2", "kind": "FunctionDecl", "name": "later",
        "canonical": "0x2", "previous": None,
        "semantic_context": "0x1", "lexical_context": "0x1",
        "implicit": False, "dependent_context": False, "owning_module": None,
        "definition": False,
    }
    definition = copy.deepcopy(declaration)
    definition["definition"] = True
    return {
        "metadata": {
            "schema_version": SCHEMA,
            "compiled_frontend": VERSION,
            "runtime_frontend": "clang version " + VERSION,
            "llvm_headers": VERSION,
            "declarations": [declaration, definition],
        },
        "ast": {"id": "0x1", "kind": "TranslationUnitDecl", "inner": []},
    }


def probe_bytes():
    serialized = json.dumps(probe_document(), ensure_ascii=False)
    return serialized.replace(
        '"inner": []', '"inner": [], "huge": 9007199254740993, "zero": -0',
    ).encode("utf-8") + b"\n"


def fake_frontend_text(resource, header, payload, mode):
    values = {
        "resource": str(resource), "header": str(header),
        "payload": payload, "mode": mode,
    }
    return "#!" + sys.executable + "\n" + """import pathlib
import sys
import time

values = VALUES
arguments = sys.argv[1:]
is_probe = "-plugin" in arguments
source = next((token for token in arguments if token.endswith(".cpp")), None)
if "--version" in arguments:
    print("clang version 21.1.8")
elif "-print-resource-dir" in arguments or "--print-resource-dir" in arguments:
    print(values["resource"])
elif "-dumpmachine" in arguments:
    print("x86_64-unknown-linux-gnu")
elif "-dM" in arguments:
    print("#define __cplusplus 202302L")
else:
    if "-MF" in arguments:
        depfile = pathlib.Path(arguments[arguments.index("-MF") + 1])
        inputs = [source, values["header"]]
        if is_probe and values["mode"] == "dependency-change":
            inputs = [source]
        escaped = [item.replace("\\\\", "\\\\\\\\").replace(" ", "\\\\ ") for item in inputs]
        depfile.write_text("cpp-input: " + " ".join(escaped) + "\\n", encoding="utf-8")
    if is_probe:
        mode = values["mode"]
        if mode == "timeout":
            time.sleep(2)
        if mode == "source-change":
            pathlib.Path(source).write_text("int changed;\\n", encoding="utf-8")
        if mode == "header-change":
            pathlib.Path(values["header"]).write_text("int changed;\\n", encoding="utf-8")
        if mode == "source-restore":
            original = pathlib.Path(source).read_bytes()
            pathlib.Path(source).write_text("int transient_change;\\n", encoding="utf-8")
            pathlib.Path(source).write_bytes(original)
        if mode == "negative-create":
            pathlib.Path(source).with_name("shadow.hpp").write_text("int shadow;\\n", encoding="utf-8")
        if mode == "compiler-change":
            with pathlib.Path(sys.argv[0]).open("a", encoding="utf-8") as stream:
                stream.write("\\n")
        if mode == "plugin-change":
            plugin_index = arguments.index("-load") + 2
            pathlib.Path(arguments[plugin_index]).write_bytes(b"changed-plugin")
        sys.stdout.buffer.write(values["payload"])
        sys.stderr.write("synthetic frontend diagnostic\\n")
        if mode == "nonzero":
            raise SystemExit(7)
""".replace("VALUES", repr(values))


class StrictProbeTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="cpp-capture-parser-")
        self.addCleanup(directory.cleanup)
        self.path = pathlib.Path(directory.name) / "probe.json"

    def parse(self, contents):
        self.path.write_bytes(contents)
        return support.strict_probe(self.path)

    def test_ordered_repeated_rows_and_large_integer_are_retained(self):
        parsed = self.parse(probe_bytes())
        self.assertEqual(parsed["metadata"]["schema_version"], SCHEMA)
        rows = parsed["metadata"]["declarations"]
        self.assertEqual(len(rows), 2)
        self.assertEqual([row["definition"] for row in rows], [False, True])
        self.assertEqual(rows[0]["id"], rows[1]["id"])
        self.assertEqual(str(parsed["ast"]["huge"]), "9007199254740993")
        self.assertEqual(str(parsed["ast"]["zero"]), "-0")
        self.assertEqual(self.path.read_bytes(), probe_bytes())

    def test_integer_lexemes_exceed_host_integer_conversion_limit(self):
        token = "9" * 6000
        contents = probe_bytes().replace(b"9007199254740993", token.encode("ascii"))
        parsed = self.parse(contents)
        self.assertEqual(str(parsed["ast"]["huge"]), token)
        self.assertEqual(self.path.read_bytes(), contents)

    def test_duplicate_keys_refuse_at_every_depth(self):
        for pair in (b'"extra":0,"extra":1', b'"extra":0,"ex\\u0074ra":1'):
            for prefix, suffix in ((b"", b""), (b'"nested":{', b"}")):
                with self.subTest(pair=pair, nested=bool(prefix)):
                    contents = probe_bytes().replace(
                        b'"inner": []', b'"inner": [], ' + prefix + pair + suffix,
                    )
                    with self.assertRaises(support.CaptureError):
                        self.parse(contents)

    def test_noninteger_numbers_and_nonfinite_constants_refuse(self):
        for token in (b"1.0", b"1e0", b"NaN", b"Infinity", b"-Infinity", b"01"):
            with self.subTest(token=token):
                contents = probe_bytes().replace(b'"zero": -0', b'"zero": ' + token)
                with self.assertRaises(support.CaptureError):
                    self.parse(contents)

    def test_invalid_unicode_and_utf8_refuse(self):
        for token in (b'"\\ud800"', b'"\\udfff"', b'"\\ud800x"', b'"\xff"'):
            with self.subTest(token=token):
                contents = probe_bytes().replace(b'"zero": -0', b'"extra": ' + token)
                with self.assertRaises(support.CaptureError):
                    self.parse(contents)

    def test_unicode_surrogate_pair_is_valid(self):
        contents = probe_bytes().replace(b'"zero": -0', b'"extra": "\\ud83d\\ude00"')
        parsed = self.parse(contents)
        self.assertEqual(parsed["ast"]["extra"], "😀")

    def test_foreign_handle_remains_unjoined_observation(self):
        document = probe_document()
        document["metadata"]["declarations"][1]["canonical"] = "0xdead"
        parsed = self.parse(json.dumps(document).encode("utf-8"))
        self.assertEqual(parsed["metadata"]["declarations"][1]["canonical"], "0xdead")

    def test_partial_or_trailing_json_refuses(self):
        for contents in (probe_bytes()[:-3], probe_bytes() + b"{}", probe_bytes() + b"tail"):
            with self.subTest(contents=contents[-15:]):
                with self.assertRaises(support.CaptureError):
                    self.parse(contents)

    def test_schema_and_runtime_mismatch_refuse(self):
        for field, value in (
            ("schema_version", "cpp-canonical-probe-0.2"),
            ("compiled_frontend", "21.1.80"),
            ("runtime_frontend", "clang version 21.1.80"),
            ("llvm_headers", "21.1.80"),
        ):
            with self.subTest(field=field):
                document = probe_document()
                document["metadata"][field] = value
                with self.assertRaises(support.CaptureError):
                    self.parse(json.dumps(document).encode("utf-8"))


class ControlledEnvironmentTests(unittest.TestCase):
    def test_absent_and_present_empty_are_distinct(self):
        absent = support.controlled_environment({})
        empty = support.controlled_environment({"CPATH": ""})
        self.assertNotIn("CPATH", absent)
        self.assertIn("CPATH", empty)
        self.assertEqual(empty["CPATH"], "")
        self.assertEqual(absent["SOURCE_DATE_EPOCH"], "0")

    def test_allowed_environment_values_are_exact(self):
        selected = {"CPATH": "/one:/two", "CPLUS_INCLUDE_PATH": "", "SOURCE_DATE_EPOCH": "123"}
        effective = support.controlled_environment(selected)
        for key, value in selected.items():
            self.assertEqual(effective[key], value)

    def test_driver_and_loader_overrides_refuse_even_when_empty(self):
        for key in ("CCC_OVERRIDE_OPTIONS", "CCC_ADD_ARGS", "LD_PRELOAD", "LD_LIBRARY_PATH"):
            for value in ("", "unsafe"):
                with self.subTest(key=key, value=value):
                    with self.assertRaises(support.CaptureError):
                        support.controlled_environment({key: value})


class ProcessBoundaryTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="cpp-capture-process-")
        self.addCleanup(directory.cleanup)
        self.root = pathlib.Path(directory.name)

    def run_script(self, script, timeout=3, label="process"):
        return support.run_process(
            [sys.executable, "-c", script], self.root,
            support.controlled_environment({}), self.root, label, timeout, 256,
        )

    def test_success_records_bytes_bounds_and_status(self):
        record = self.run_script("import sys; sys.stdout.buffer.write(b'exact\\x00bytes'); sys.stderr.write('error')")
        self.assertEqual((self.root / record["stdout"]).read_bytes(), b"exact\x00bytes")
        self.assertEqual((self.root / record["stderr"]).read_bytes(), b"error")
        self.assertEqual(record["exit_status"], 0)
        self.assertFalse(record["timed_out"])
        self.assertGreaterEqual(record["elapsed_seconds"], 0)
        self.assertGreater(record["max_rss_kib"], 0)
        self.assertEqual(record["bounds"]["timeout_seconds"], 3)
        self.assertEqual(record["bounds"]["memory_mib"], 256)

    def test_nonzero_exit_retains_output_and_refuses(self):
        with self.assertRaises(support.CaptureError):
            self.run_script("print('{}', flush=True); raise SystemExit(7)")
        self.assertEqual((self.root / "process.stdout").read_bytes(), b"{}\n")
        receipt = json.loads((self.root / "process.process.json").read_text(encoding="utf-8"))
        self.assertEqual(receipt["exit_status"], 7)
        self.assertFalse(receipt["timed_out"])

    def test_signal_refuses(self):
        with self.assertRaises(support.CaptureError):
            self.run_script("import os, signal; os.kill(os.getpid(), signal.SIGTERM)")
        receipt = json.loads((self.root / "process.process.json").read_text(encoding="utf-8"))
        self.assertEqual(receipt["signal"], 15)

    def test_successful_parent_with_surviving_descendant_refuses(self):
        script = (
            "import subprocess, sys; subprocess.Popen([sys.executable, '-c', "
            "\"import time; time.sleep(2); print('late writable output')\"]); "
            "print('parent output', flush=True)"
        )
        with self.assertRaises(support.CaptureError):
            self.run_script(script)
        receipt = json.loads((self.root / "process.process.json").read_text(encoding="utf-8"))
        self.assertEqual(receipt["exit_status"], 0)
        self.assertIsNotNone(receipt["observation_error"])

    def test_timeout_retains_partial_stdout_and_refuses(self):
        with self.assertRaises(support.CaptureError):
            self.run_script("import time; print('{}', flush=True); time.sleep(2)", timeout=0.2)
        self.assertEqual((self.root / "process.stdout").read_bytes(), b"{}\n")
        receipt = json.loads((self.root / "process.process.json").read_text(encoding="utf-8"))
        self.assertTrue(receipt["timed_out"])

    def test_invalid_bounds_and_labels_refuse_before_launch(self):
        for options in ({"timeout": 0}, {"timeout": float("nan")}, {"label": "../escape"}):
            with self.subTest(options=options):
                with self.assertRaises(support.CaptureError):
                    self.run_script("raise SystemExit('must not launch')", **options)
        self.assertEqual(list(self.root.iterdir()), [])

    def test_multithreaded_caller_refuses_before_launch_or_log_creation(self):
        with mock.patch("threading.active_count", return_value=2):
            with mock.patch.object(support.subprocess, "Popen") as launch:
                with self.assertRaises(support.CaptureError):
                    self.run_script("raise SystemExit('must not launch')")
                launch.assert_not_called()
        self.assertEqual(list(self.root.iterdir()), [])

    def test_existing_logs_never_overwrite(self):
        output = self.root / "process.stdout"
        output.write_bytes(b"original")
        with self.assertRaises(support.CaptureError):
            self.run_script("print('overwritten')")
        self.assertEqual(output.read_bytes(), b"original")


class AtomicPublicationTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="cpp-capture-publish-")
        self.addCleanup(directory.cleanup)
        self.root = pathlib.Path(directory.name)
        self.staging = self.root / "staging"
        self.staging.mkdir()
        (self.staging / "probe.json").write_bytes(probe_bytes())
        self.destination = self.root / "published"

    def test_publishes_complete_directory(self):
        support.atomic_publish(self.staging, self.destination)
        self.assertEqual((self.destination / "probe.json").read_bytes(), probe_bytes())
        self.assertFalse(self.staging.exists())

    def test_existing_destination_never_overwrites(self):
        self.destination.mkdir()
        marker = self.destination / "marker"
        marker.write_bytes(b"original")
        with self.assertRaises(support.CaptureError):
            support.atomic_publish(self.staging, self.destination)
        self.assertEqual(marker.read_bytes(), b"original")
        self.assertTrue(self.staging.exists())

    def test_symlink_destination_never_retargets_publication(self):
        target = self.root / "elsewhere"
        target.mkdir()
        self.destination.symlink_to(target, target_is_directory=True)
        with self.assertRaises(support.CaptureError):
            support.atomic_publish(self.staging, self.destination)
        self.assertEqual(list(target.iterdir()), [])

    def test_dangling_symlink_destination_is_not_overwritten(self):
        self.destination.symlink_to(self.root / "missing", target_is_directory=True)
        with self.assertRaises(support.CaptureError):
            support.atomic_publish(self.staging, self.destination)
        self.assertTrue(self.destination.is_symlink())


class SyntheticCaptureTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="cpp-capture-synthetic-")
        self.addCleanup(directory.cleanup)
        self.root = pathlib.Path(directory.name)
        self.source = self.root / "input.cpp"
        self.source.write_text(SOURCE, encoding="utf-8")
        self.header = self.root / "header.hpp"
        self.header.write_text("int header_value;\n", encoding="utf-8")
        self.plugin = self.root / "probe.so"
        self.plugin.write_bytes(b"synthetic-plugin")
        self.resource = self.root / "resource"
        self.resource.mkdir()
        self.compiler = self.root / "clang++"
        self.destination = self.root / "bundle"
        self.configure()

    def configure(self, mode="success", payload=None):
        contents = fake_frontend_text(
            self.resource, self.header, probe_bytes() if payload is None else payload, mode,
        )
        self.compiler.write_text(contents, encoding="utf-8")
        self.compiler.chmod(0o755)

    def run_capture(self, **options):
        environment = options.pop("environment", {})
        with mock.patch.dict(os.environ, environment, clear=True):
            return capture.capture(
                self.source, self.destination, clang=str(self.compiler), plugin=self.plugin,
                timeout=options.pop("timeout", 5), memory_mib=options.pop("memory_mib", 256), **options,
            )

    def assert_unpublished(self):
        self.assertFalse(self.destination.exists(), "refusal published a success bundle")
        for staging in self.root.glob(".bundle.staging.*"):
            failure = json.loads((staging / "failure.json").read_text(encoding="utf-8"))
            self.assertEqual(failure["state"], "failed")
            self.assertFalse(failure["successful_publication"])

    def test_success_binds_exact_payloads_and_observational_limits(self):
        published = self.run_capture()
        self.assertEqual(pathlib.Path(published), self.destination)
        self.assertEqual((published / "probe.json").read_bytes(), probe_bytes())
        receipt = json.loads((published / "capture.json").read_text(encoding="utf-8"))
        self.assertEqual(receipt["schema_version"], "cpp-probe-capture-0.1")
        self.assertEqual(receipt["profile_id"], "cpp23-clang-probe-capture-0.1")
        self.assertEqual(receipt["probe_schema"], SCHEMA)
        for group in (
            "producer", "payloads", "launch", "frontend", "source",
            "positive_inputs", "completion", "closure_limits",
        ):
            self.assertIn(group, receipt)
        for kind, filename in (("probe", "probe.json"), ("stderr", "stderr.txt"), ("dependencies", "inputs.d")):
            artifact = published / filename
            self.assertTrue(artifact.is_file())
            contents = artifact.read_bytes()
            self.assertEqual(receipt["payloads"][kind], {
                "path": filename, "byte_count": len(contents),
                "sha256": hashlib.sha256(contents).hexdigest(),
            })
        self.assertIn("unestablished", json.dumps(receipt["closure_limits"]))

    def test_ordered_flags_cwd_and_empty_environment_are_recorded(self):
        flags = ("-DORDER=one", "-DORDER=two")
        published = self.run_capture(flags=flags, environment={"CPATH": ""})
        receipt = json.loads((published / "capture.json").read_text(encoding="utf-8"))
        launch = receipt["launch"]
        self.assertEqual(launch["cwd"], str(pathlib.Path.cwd()))
        self.assertLess(launch["argv"].index(flags[0]), launch["argv"].index(flags[1]))
        self.assertEqual(launch["environment"]["CPATH"], "")
        self.assertNotIn("HOME", launch["environment"])

    def test_generator_flags_are_materialized_once(self):
        tokens = ("-DORDER=one", "-DORDER=two")
        flags = (token for token in tokens)
        published = self.run_capture(flags=flags)
        receipt = json.loads((published / "capture.json").read_text(encoding="utf-8"))
        command = receipt["launch"]["argv"]
        for token in tokens:
            self.assertEqual(command.count(token), 1)
        self.assertLess(command.index(tokens[0]), command.index(tokens[1]))

    def test_invalid_timeout_values_refuse_before_launch(self):
        for timeout in (True, False, 0, -1, float("nan"), float("inf"), "1", None):
            with self.subTest(timeout=timeout):
                with self.assertRaisesRegex(support.CaptureError, "positive finite"):
                    self.run_capture(timeout=timeout)
                self.assert_unpublished()
        self.assertEqual(list(self.root.glob(".bundle.staging.*")), [])

    def test_memory_bound_requires_an_exact_positive_integer(self):
        for memory in (True, False, 0, -1, 256.0, "256", None):
            with self.subTest(memory=memory):
                with self.assertRaises(support.CaptureError):
                    self.run_capture(memory_mib=memory)
                self.assert_unpublished()
        self.assertEqual(list(self.root.glob(".bundle.staging.*")), [])

    def test_option_response_file_and_stdin_source_tokens_refuse(self):
        for token in ("-", "-input.cpp", "@input.cpp"):
            with self.subTest(token=token):
                self.source = token
                with self.assertRaisesRegex(support.CaptureError, "source argument cannot"):
                    self.run_capture()
                self.assert_unpublished()

    def test_version_observation_disables_default_driver_configuration(self):
        published = self.run_capture()
        receipt = json.loads((published / "capture.json").read_text(encoding="utf-8"))
        version = next(record for record in receipt["completion"]["processes"]
                       if "--version" in record["argv"])
        self.assertIn("--no-default-config", version["argv"])

    def test_declared_library_images_do_not_establish_loader_closure(self):
        library = self.root / "runtime.so"
        library.write_bytes(b"declared-library-image")
        published = self.run_capture(runtime_libraries=(library,))
        receipt = json.loads((published / "capture.json").read_text(encoding="utf-8"))
        recorded = receipt["frontend"]["declared_runtime_libraries"]
        self.assertEqual(len(recorded), 1)
        self.assertEqual(recorded[0]["resolved_path"], str(library.resolve()))
        self.assertEqual(recorded[0]["sha256"], hashlib.sha256(library.read_bytes()).hexdigest())
        self.assertEqual(receipt["closure_limits"]["runtime_image_closure"], "unestablished")

    def test_raw_source_forms_do_not_gain_a_module_exclusion_claim(self):
        self.source.write_text("export module sample;\n", encoding="utf-8")
        document = probe_document()
        document["ast"]["inner"] = [{"kind": "ModuleDecl", "name": "sample"}]
        payload = json.dumps(document).encode("utf-8")
        self.configure(payload=payload)
        published = self.run_capture()
        receipt = json.loads((published / "capture.json").read_text(encoding="utf-8"))
        self.assertEqual((published / "probe.json").read_bytes(), payload)
        self.assertEqual(receipt["closure_limits"]["ordinary_source_profile"], "unestablished")
        self.assertFalse(receipt["closure_limits"]["semantic_admission"])

    def test_tampered_payload_digest_refuses_before_publication(self):
        original_write = capture.write_record

        def tamper_after_receipt(path, record):
            original_write(path, record)
            if path.name == "capture.json":
                (path.parent / "probe.json").write_bytes(b"tampered")

        with mock.patch.object(capture, "write_record", side_effect=tamper_after_receipt):
            with self.assertRaises(support.CaptureError):
                self.run_capture()
        self.assert_unpublished()

    def test_nonzero_output_is_not_success_even_when_json_parses(self):
        self.configure("nonzero")
        with self.assertRaises(support.CaptureError):
            self.run_capture()
        self.assert_unpublished()

    def test_timeout_output_is_not_success(self):
        self.configure("timeout")
        with self.assertRaises(support.CaptureError):
            self.run_capture(timeout=0.2)
        self.assert_unpublished()

    def test_mutated_positive_inputs_and_images_refuse(self):
        for mode in ("source-change", "header-change", "compiler-change", "plugin-change"):
            with self.subTest(mode=mode):
                self.source.write_text(SOURCE, encoding="utf-8")
                self.header.write_text("int header_value;\n", encoding="utf-8")
                self.plugin.write_bytes(b"synthetic-plugin")
                self.configure(mode)
                reason = "declared tool image changed" if mode in ("compiler-change", "plugin-change") else "positive translation inputs changed"
                with self.assertRaisesRegex(support.CaptureError, reason):
                    self.run_capture()
                self.assert_unpublished()

    def test_changed_dependency_set_refuses(self):
        self.configure("dependency-change")
        with self.assertRaisesRegex(support.CaptureError, "positive translation inputs changed"):
            self.run_capture()
        self.assert_unpublished()

    def test_change_then_restore_is_not_mislabeled_as_closed(self):
        self.configure("source-restore")
        published = self.run_capture()
        self.assertEqual(self.source.read_text(encoding="utf-8"), SOURCE)
        receipt = json.loads((published / "capture.json").read_text(encoding="utf-8"))
        self.assertEqual(receipt["closure_limits"]["input_world"], "unestablished")
        self.assertEqual(receipt["closure_limits"]["guarantee"], "observed-positive-input-stability")

    def test_unmanifested_lookup_change_is_not_mislabeled_as_closed(self):
        self.configure("negative-create")
        published = self.run_capture()
        self.assertTrue((self.root / "shadow.hpp").exists())
        receipt = json.loads((published / "capture.json").read_text(encoding="utf-8"))
        self.assertEqual(receipt["closure_limits"]["input_world"], "unestablished")
        self.assertFalse(receipt["closure_limits"]["semantic_admission"])
        self.assertFalse(receipt["closure_limits"]["runtime_admission"])

    def test_zero_exit_malformed_probe_refuses(self):
        for payload in (probe_bytes()[:-3], probe_bytes() + b"{}", b'{"metadata":{}}'):
            with self.subTest(payload=payload[-20:]):
                self.configure(payload=payload)
                with self.assertRaises(support.CaptureError):
                    self.run_capture()
                self.assert_unpublished()

    def test_zero_exit_duplicate_probe_key_refuses(self):
        payload = probe_bytes().replace(b'"inner": []', b'"inner": [], "extra": 1, "ex\\u0074ra": 2')
        self.configure(payload=payload)
        with self.assertRaises(support.CaptureError):
            self.run_capture()
        self.assert_unpublished()

    def test_existing_output_refuses_without_overwriting(self):
        self.destination.mkdir()
        marker = self.destination / "marker"
        marker.write_bytes(b"original")
        with self.assertRaises(support.CaptureError):
            self.run_capture()
        self.assertEqual(marker.read_bytes(), b"original")

    def test_source_output_alias_refuses_without_changing_source(self):
        self.destination = self.source
        before = self.source.read_bytes()
        with self.assertRaises(support.CaptureError):
            self.run_capture()
        self.assertEqual(self.source.read_bytes(), before)

    def test_disallowed_flags_refuse_without_publication(self):
        for flags in (("@flags.rsp",), ("-std=c++20",), ("other.cpp",), ("-fmodules",)):
            with self.subTest(flags=flags):
                with self.assertRaises(support.CaptureError):
                    self.run_capture(flags=flags)
                self.assert_unpublished()


class PinnedFrontendCaptureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        selected = os.environ.get("LEANCPP_CLANG")
        library = os.environ.get("LEANCPP_PROBE_LIBRARY")
        if not selected or not library:
            raise unittest.SkipTest("set matching LEANCPP_CLANG and LEANCPP_PROBE_LIBRARY for capture")
        cls.clang = shutil.which(selected)
        cls.plugin = pathlib.Path(library).resolve()
        if cls.clang is None or not cls.plugin.is_file():
            raise unittest.SkipTest("selected matching frontend/plugin inputs are unavailable")
        declared = json.loads(os.environ.get("LEANCPP_RUNTIME_LIBRARIES", "[]"))
        if not isinstance(declared, list) or any(not isinstance(path, str) for path in declared):
            raise RuntimeError("LEANCPP_RUNTIME_LIBRARIES must be a JSON array of image paths")
        cls.runtime_libraries = tuple(pathlib.Path(path).resolve(strict=True) for path in declared)

    def test_real_frontend_exact_payload_and_binding(self):
        with tempfile.TemporaryDirectory(prefix="cpp-capture-pinned-") as directory:
            root = pathlib.Path(directory)
            source = root / "input.cpp"
            source.write_text(SOURCE, encoding="utf-8")
            destination = root / "bundle"
            with mock.patch.dict(os.environ, {}, clear=True):
                published = capture.capture(
                    source, destination, clang=self.clang, plugin=self.plugin,
                    runtime_libraries=self.runtime_libraries, timeout=30, memory_mib=16384,
                )
            self.assertEqual(published, destination)
            probe = support.strict_probe(published / "probe.json")
            self.assertEqual(probe["metadata"]["schema_version"], SCHEMA)
            declarations = [row for row in probe["metadata"]["declarations"]
                            if row.get("kind") == "FunctionDecl" and row.get("name") == "later"]
            self.assertGreaterEqual(len(declarations), 2)
            receipt = json.loads((published / "capture.json").read_text(encoding="utf-8"))
            digest = hashlib.sha256((published / "probe.json").read_bytes()).hexdigest()
            self.assertIn(digest, json.dumps(receipt["payloads"]))
            self.assertIn("unestablished", json.dumps(receipt["closure_limits"]))
            declared_paths = [entry["resolved_path"] for entry in receipt["frontend"]["declared_runtime_libraries"]]
            self.assertEqual(declared_paths, [str(path) for path in self.runtime_libraries])
            self.assertEqual(receipt["closure_limits"]["runtime_image_closure"], "unestablished")
            self.assertEqual(receipt["closure_limits"]["ordinary_source_profile"], "unestablished")

    def test_negative_include_lookup_prevents_replay_closure_claim(self):
        with tempfile.TemporaryDirectory(prefix="cpp-capture-lookup-") as directory:
            root = pathlib.Path(directory)
            source = root / "input.cpp"
            source.write_text(
                '#if __has_include("optional.hpp")\n#include "optional.hpp"\n'
                '#else\nint absent();\n#endif\n', encoding="utf-8",
            )
            header = root / "optional.hpp"
            with mock.patch.dict(os.environ, {}, clear=True):
                first = capture.capture(source, root / "first", clang=self.clang,
                                        plugin=self.plugin, timeout=30, memory_mib=16384)
                header.write_text("int present();\n", encoding="utf-8")
                second = capture.capture(source, root / "second", clang=self.clang,
                                         plugin=self.plugin, timeout=30, memory_mib=16384)
            before = json.loads((first / "capture.json").read_text(encoding="utf-8"))
            after = json.loads((second / "capture.json").read_text(encoding="utf-8"))
            self.assertEqual(before["source"]["sha256"], after["source"]["sha256"])
            self.assertNotIn(str(header), before["positive_inputs"]["actual_manifest"])
            self.assertIn(str(header), after["positive_inputs"]["actual_manifest"])
            self.assertEqual(before["closure_limits"]["input_world"], "unestablished")
            self.assertEqual(after["closure_limits"]["input_world"], "unestablished")


if __name__ == "__main__":
    unittest.main()
