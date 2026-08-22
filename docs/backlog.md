# Backlog — MOVED

**This file is a redirect, and it is FROZEN. Do not append to it.**

`docs/family-architecture.md` §9.5 retired the single-file backlog:

* **your lane's entries go in `docs/backlog/<lane>.md`**, appended only by
  that lane, with ids `YYYY-MM-DD-<lane>-<n>` that need no reservation;
* the single view across every lane is
  [`docs/backlog/INDEX.md`](backlog/INDEX.md), **generated** by
  `tools/backlog-index.sh` and never hand-maintained (§5.5);
* everything written before the split is in
  [`docs/backlog-archive.md`](backlog-archive.md), frozen, where **every
  `§Lnn` reference still resolves at the heading it always had.**

This stub exists because **111 tracked files cite `docs/backlog.md`** —
including `.lean` files, whose edit would make a docs landing tier-class. A
big-bang sweep is exactly what §9.2 forbids; the old spelling is retired **by
touch**. Until then, a citation that lands here is one hop from its target.

`tools/backlog-index.sh --check` asserts the index is in sync, and
`tools/docs_check.py` reports it when it drifts.
