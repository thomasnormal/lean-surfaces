# `Examples/c/sunfish` — the C twin, ingested

The C tier's flagship corpus. Unlike every other `Examples/` directory,
**the source is not here**: `tools/ctwin/sunfish.c` lives in the SUNFISH
repository, where it is kept node-identical to classic `sunfish.py` by a
continuously-enforced fidelity gate (`make gate`, TESTING.md rule 14).
That is what makes it a semantics corpus rather than a second engine, and
it is why this directory holds an envelope and its guards but no `.c`.

| file | what it is |
| --- | --- |
| `sunfish.json` | the `c-0.1` envelope, 153 top-level decls, 27 externals, 0 `Unsupported` |
| `guards.lean` | M1's capstone: the corpus ingests, and the term agrees with the census |

## Regenerating the envelope

```
python3 extractors/c/extract.py <path-to>/tools/ctwin/sunfish.c \
    --source-name tools/ctwin/sunfish.c \
    -o Examples/c/sunfish/sunfish.json
```

`--source-name` exists precisely because the corpus is cross-repo: a path
relative to THIS root would be a fiction, so the envelope records the
corpus's own path in its own repository.

The pin, checked by `guards.lean` itself: sha256
`7d5e0ff8782f804844f383d6f72314dbf948f8e3a26f4033794d6357140b77d7`,
profile `c-profile-0.1`, flags `-std=c23 -D_FORTIFY_SOURCE=0`. Both twins
have been stable since sunfish engine commit `e670434`.

## When the corpus moves

It will; §L35 of `docs/backlog.md` is the entry where it already had.
`harness/c_construct_census.py --compare docs/c-construct-census.json`
says whether the SURFACE moved (a new node kind or libc name is a tier
decision) or only the counts did. Re-extract, re-run `guards.lean`, and
update the numbers the guards pin — they are deliberately exact so that a
moved corpus is a red check rather than a quiet drift.
