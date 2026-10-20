#!/usr/bin/env python3
"""Original TinyXML-2 byte-helper differential against the generated Lean body.

Opt in with LEANCPP_TINYXML2_DIR and LEANCPP_CLANG. Sources remain read-only;
this is a complete 8-bit input-domain check, not whole-library execution.
"""

import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
EXAMPLE = ROOT / "Examples/cpp/tinyxml2"


class TinyXmlArtifactTests(unittest.TestCase):
    def test_original_high_bit_helper_matches_both_evaluators(self):
        directory = os.environ.get("LEANCPP_TINYXML2_DIR")
        requested = os.environ.get("LEANCPP_CLANG")
        if not directory or not requested:
            self.skipTest("set LEANCPP_TINYXML2_DIR and LEANCPP_CLANG")
        clang, lake = shutil.which(requested), shutil.which("lake")
        self.assertIsNotNone(clang)
        self.assertIsNotNone(lake)
        corpus = pathlib.Path(directory).resolve()
        manifest = json.loads((EXAMPLE / "provenance.json").read_text(encoding="utf-8"))
        for name, expected in manifest["source_sha256"].items():
            self.assertEqual(hashlib.sha256((corpus / name).read_bytes()).hexdigest(), expected)
        literal = (EXAMPLE / "IsUTF8Continuation.lean").read_bytes()
        self.assertEqual(hashlib.sha256(literal).hexdigest(), manifest["literal_sha256"])
        version = subprocess.run([clang, "--version"], capture_output=True, text=True, timeout=10)
        self.assertEqual(version.returncode, 0, version.stderr)
        self.assertTrue(version.stdout.startswith("clang version 21.1.8 "), version.stdout)
        environment = dict(os.environ)
        environment.pop("CCC_OVERRIDE_OPTIONS", None)
        environment.pop("CCC_ADD_ARGS", None)
        environment["SOURCE_DATE_EPOCH"] = "0"
        with tempfile.TemporaryDirectory(prefix="cpp-tinyxml2-") as temporary:
            work = pathlib.Path(temporary)
            oracle = work / "oracle.cpp"
            oracle.write_text('''#include <climits>
#include <iostream>
#include "tinyxml2.h"
static_assert(CHAR_BIT == 8 && CHAR_MIN == -128 && sizeof(short) == 2 &&
              sizeof(int) == 4 && sizeof(long) == 8 && sizeof(long long) == 8);
int main() {
  for (int value = -128; value < 128; ++value)
    std::cout << tinyxml2::XMLUtil::IsUTF8Continuation(static_cast<char>(value)) << '\\n';
}
''', encoding="utf-8")
            outputs = []
            for optimization in ("-O0", "-O2"):
                binary = work / optimization[1:]
                compiled = subprocess.run([
                    clang, "--no-default-config", "-std=c++23", "-pedantic-errors", optimization,
                    "-fsanitize=undefined", "-fno-sanitize-recover=all",
                    "-static-libstdc++", "-static-libgcc", "-I", str(corpus),
                    str(oracle), "-o", str(binary),
                ], cwd=work, env=environment, capture_output=True, text=True, timeout=60)
                self.assertEqual(compiled.returncode, 0, compiled.stderr)
                executed = subprocess.run([str(binary)], cwd=work, env=environment,
                                          capture_output=True, text=True, timeout=30)
                self.assertEqual(executed.returncode, 0, executed.stderr)
                values = [int(value) for value in executed.stdout.splitlines()]
                self.assertEqual(len(values), 256)
                self.assertTrue(all(value in (0, 1) for value in values))
                outputs.append(values)
            self.assertEqual(outputs[0], outputs[1])
            pairs = ", ".join(f"({value}, {expected})" for value, expected in
                              zip(range(-128, 128), outputs[0]))
            check = work / "Check.lean"
            check.write_text(literal.decode("utf-8") + '''
open LeanModels.Cpp LeanModels.Cpp.CallableObjectEvaluation
open Examples.cpp.tinyxml2.IsUTF8Continuation
set_option maxRecDepth 100000
''' + f"def cases : List (Int × Int) := [{pairs}]\n" + '''
#guard cases.all (fun (input, expected) =>
  (match evaluateCallable 32 .lp64 function [⟨.signed 8, input⟩] with
   | .ok (.ok ⟨.boolean, value⟩) => value == expected
   | _ => false) &&
  (match CallableObjectFrame.start .lp64 function [⟨.signed 8, input⟩] with
   | .ok callable =>
       let outcome := evaluateCallableObjectInFrame 32 callable
       outcome.frame.scopes.isEmpty &&
         outcome.frame.store.objects.objects.length == 1 &&
         outcome.frame.store.objects.objects.all (fun object => object.phase == .ended) &&
         (match outcome.result with
          | .ok (.ok ⟨.boolean, value⟩) => value == expected
          | _ => false)
   | _ => false))
''', encoding="utf-8")
            checked = subprocess.run([lake, "env", "lean", "-j", "1", str(check)], cwd=ROOT,
                                     env=environment, capture_output=True, text=True, timeout=180)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        print("TinyXML-2 original IsUTF8Continuation: 256 rows, both evaluators, -O0/-O2 under UBSan")


if __name__ == "__main__":
    unittest.main()
