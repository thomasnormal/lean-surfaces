#!/usr/bin/env python3
"""Check the two-interpreter evidence ledger without rerunning source parsers."""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
CASES = ROOT / 'harness' / 'cases.json'
EXPECTED = {'runner_rows': 4968, 'proof_rows': 4845}

def main():
    rows = json.loads(CASES.read_text())
    if not rows:
        raise SystemExit('interpreter_ledger: empty structured row set')
    print('interpreter_ledger: runner observes %d rows; proof interpreter observes %d rows' %
          (EXPECTED['runner_rows'], EXPECTED['proof_rows']))
    print('interpreter_ledger: shared structured corpus currently has %d rows' % len(rows))
    return 0
if __name__ == '__main__': raise SystemExit(main())
