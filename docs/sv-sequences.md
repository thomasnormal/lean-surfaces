# Concurrent sequence declarations — retained boundary

IEEE 1800-2023 clause 16 defines sequence declarations for concurrent
assertions. A sequence carries sampled clock events, temporal concatenation
and repetition, endpoint matching, formal/local scope, and diagnostic rules
for multiclock operators and illegal local types. Its evaluation creates and
advances sequence attempts across simulation ticks.

The existing envelope has no sequence table, sampled-value history, temporal
attempt state, local/formal frame or endpoint automaton. A sequence cannot be
rewritten as a Boolean expression or an immediate assertion without changing
when it samples and how it matches. `SequenceSymbol:Sequence` therefore
remains loud; no assertion engine or second scheduler is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `SequenceSymbol:Sequence` in **284**
files; **12** are sequence-only and 272 co-occur. The independent read-only
repricer finds **15** sequence spans in the sole files (several files declare
more than one sequence). Features overlap:

| feature | spans | files |
|---|---:|---:|
| local variable | 5 | 4 |
| formal argument | 4 | 4 |
| multiclock | 7 | 7 |
| intersect | 1 | 1 |
| temporal concatenation | 9 | 7 |
| matched endpoint | 2 | 1 |
| end label | 1 | 1 |
| event/local diagnostic | 1 | 1 |
| sequence-typed formal | 2 | 1 |
| sampled-value function | 2 | 1 |

Reproduce the table with:

```text
python3.9 extractors/sv/sequence_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it verifies the sole marker and reports source
features without evaluating a temporal attempt or registering a sampled wait.
