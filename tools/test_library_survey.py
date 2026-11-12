#!/usr/bin/env python3
"""Regression checks for the pinned library-mode manifest and call admission."""
import json
import os
import tempfile
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'harness'))
import library_survey as survey  # noqa: E402


def main():
    assert survey.pinned_stdlib_file('bisect')
    manifest = json.loads((ROOT / 'harness/library_corpus.json').read_text())
    assert len(manifest['modules']) == 183
    assert manifest['cpython'] == '3.9.25'
    census = [m for m in manifest['modules'] if m['provenance'] == 'census:library']
    assert len(census) == 141
    assert all(os.path.isfile(m['file']) and len(m['sha256']) == 64 for m in census)
    # A guarded C accelerator must be visible as an explicit skipped
    # function, never compared against the file's pure-Python definition.
    with tempfile.TemporaryDirectory() as td:
        oracle = survey.run_oracle(
            sys.executable, 'operator', survey.pinned_stdlib_file('operator'),
            True, 1, 10.0, td)
        index = next(f for f in oracle['functions'] if f['name'] == 'index')
        assert index['impl'].startswith('override:')
        assert 'accelerator override' in index['skipped']
    print('library_survey: pinned manifest self-test passed (183 modules, 141 stdlib hashes)')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
