---
name: Semantics mismatch (Python)
about: The Lean model answers differently from CPython 3.9
title: "mismatch: "
labels: python, semantics
---

**Smallest program that shows it**

```python
# paste a complete .py file
```

**What CPython 3.9 does** (stdout, exit status, exception if any)

**What the model does**

Output of `tools/leanpy --compare FILE.py`, or for a single function
`leanmodels-run FILE.json FUNC ARGS...`:

```
```

**Commit** (`git rev-parse --short HEAD`):

A loud refusal (`unsupported`, exit code 3) is not a mismatch. For those,
check docs/python-coverage.md, then use the *Refusal* template.
