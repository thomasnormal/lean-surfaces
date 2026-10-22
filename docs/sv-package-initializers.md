# Package initializers — repricing boundary

IEEE §26.2 initializes package variables before any `initial` or `always`
procedure starts. Initializers execute in declaration order and may use names
made visible by package imports and exports. Their values become shared package
storage for later module processes.

## Why package initializers remain a boundary

The admitted package-storage slice only carries closed pure integral
initializers. The envelope has no dependency graph or initialization phase for
runtime variable reads, imported/exported names, calls or effects. Treating a
dependent initializer as a constant, dropping it, or running it as a module
process changes declaration order and the values visible at time zero. The
public tier therefore keeps every `Package:initializer` loud and adds no second
initialization scheduler.

## 2026-10-22 census and decision

The fresh 22,043-path census records `Package:initializer` in **41** files:
**25** are initializer-only and **16** co-occurring. Repricing the sole files
finds **35** spans: all **35** contain a runtime variable reference, **14** use
arithmetic in **11** files, **6** contain multiple referenced identifiers,
**1** uses a qualified package reference, and **19** occur in **9** files with
multiple initializers (features overlap). Export contexts occur in **24** spans
across **17** files, including **9** wildcard-export spans in **5** files.
Reproduce the table with:

```text
python3.9 extractors/sv/package_initializer_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it reports initializer shapes without evaluating
dependencies or changing package storage.
