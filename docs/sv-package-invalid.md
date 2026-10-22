# Invalid package compilations — repricing boundary

IEEE §26 requires package imports, exports and timeunit declarations to satisfy
scope and consistency rules before elaboration. A repeated package timeunit
must match; explicit and wildcard imports obey visibility and collision rules;
an export must name a declaration imported from the corresponding package.

## Why invalid package compilations remain a boundary

`Package:invalid-compilation` is a design-level diagnostic marker emitted when
the frontend rejects a source containing a package. The envelope has no
diagnostic provenance, package scope graph or partial-elaboration contract.
Dropping the package, keeping unrelated declarations, or selecting the first
import would execute a design that IEEE requires to fail compilation. The
public tier therefore retains the marker and introduces no recovery elaborator
or scheduler.

## 2026-10-22 census and decision

The fresh 22,043-path census records `Package:invalid-compilation` in **146**
files: **24** are invalid-package-only and **122** co-occurring. Repricing the
sole files finds **24** diagnostic spans: **3** repeated-timeunit declarations,
**19** import cases, **10** files with multiple imports, **9** wildcard imports,
**8** export cases, **6** combined import/export cases, **1** `export *::*` case
and **2** exports without a corresponding import (features overlap). Reproduce
the table with:

```text
python3.9 extractors/sv/package_invalid_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it classifies source diagnostics without
salvaging declarations or changing package resolution.
