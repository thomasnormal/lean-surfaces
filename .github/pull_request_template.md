## What this changes

## Checked

- [ ] `lake build` of the affected targets is green (no `sorry`, no `admit`)
- [ ] `python3 harness/diff_test.py` exits 0 (new behaviour has rows in `harness/cases.json`)
- [ ] `python3 tools/docs_check.py` (if docs changed)
- [ ] `python3 harness/coverage_page.py --check` (regenerated if coverage moved)
- [ ] CHANGELOG.md `[Unreleased]` entry (if user-visible)
- [ ] No theorem statement weakened, no `"expect": "unsupported"` row added to hide a mismatch
