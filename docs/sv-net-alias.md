# Net aliases — repricing boundary

IEEE §10.11 and §6.7.2 let an `alias` declaration make two or more net
expressions refer to the same physical net. The relationship is bidirectional:
a driver or resolved value observed through one name is visible through every
aliased name. Alias declarations can be chained, cumulative, selected by
constant bit or part ranges, and placed in generated module items.

## Why net aliases remain a boundary

The envelope has no alias graph or resolved-driver topology. Treating an alias
as a one-way assignment, erasing it, or copying one initial value loses
bidirectional updates, cumulative overlays, width checks and net resolution.
The public tier therefore keeps every `NetAliasSymbol:NetAlias` loud and does
not add a second elaborator or scheduler.

## 2026-10-22 census and decision

The fresh 22,043-path census records `NetAliasSymbol:NetAlias` in **35** files:
**25** are alias-only and **10** co-occurring. Repricing the sole files finds
**31** spans: **11** indexed-select spans in **7** files, **4** chained aliases,
**12** declarations in **6** files with multiple alias statements, **4** alias
spans in **3** generated placements and **1** protected-region span (features
overlap). Reproduce the table with:

```text
python3.9 extractors/sv/net_alias_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it reports source shapes without constructing an
alias relation or changing driver resolution.
