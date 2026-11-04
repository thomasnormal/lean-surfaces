# CI tool self-tests

`bash tools/ci.sh` runs each shell tool's focused self-test with a 120-second
timeout. The tests run in a symlink view without `.lake` build products;
`lake` and `lean` on `PATH` are refusing shims. These tests exercise tooling,
not language execution or proofs. They must never start a real Lean build.

Successful tool self-tests stay quiet. On failure, CI prints the tool name,
actual exit code, and captured stdout/stderr. A timeout is reported as exit
124, not an unspecified assertion failure. The temporary capture is removed
after reporting. `tools/test_ci_selftests.py` checks this reporting contract
without sourcing or entering the CI pipeline.

## Log-destination guard

`tools/triad.sh` refuses a tenure whose stdout or stderr is redirected to a
file inside its clone: that growing log would invalidate its own working-tree
stamp. On Linux, descriptor paths come from `/proc/$$/fd`; elsewhere the guard
uses `lsof`. Linux does not require `lsof` for this check. If descriptors cannot
be inspected, the tool refuses **before enqueue**, rather than treating an
unobservable destination as outside the clone. The `--classify-only` report
does not take a tenure and remains exempt from this guard.

The build header contains explicit ticket, lane, branch, tree, HEAD, clone,
attempt and timestamp fields; it has no hostname field. Its self-test uses an
isolated hostname marker rather than searching for the machine's short hostname
inside every value. A username, branch or legitimate clone path can share a
substring with a hostname without being a hostname field.

## Instrument fixtures

`LS_MOCK_LOAD` overrides the live load reading when it is **set**, including
an explicitly empty value. Empty simulates an unreadable instrument and must
not fall through to the actual host's load. Unset still uses the normal live
instrument. The adaptive-thread fixture checks both the conservative thread
count and the unreadable-load reason; an idle runner must not change the
fixture's verdict. `tools/test_instruments.py` checks the override boundary
with deterministic shell probes, independent of the real machine's load.

Focused checks:

```console
bash tools/triad.sh --self-test
python3 tools/test_ci_selftests.py
python3 tools/test_instruments.py
bash -n tools/triad.sh tools/ci.sh
```
