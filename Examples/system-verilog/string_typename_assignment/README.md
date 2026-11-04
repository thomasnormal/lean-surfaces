# `$typename` string assignment

The legacy self-check extractor replays a blocking assignment from the
metadata-only `$typename(int)` query through its source-pure string history.
Effectful expression arguments, dynamic type-name sources, timed writes, and
nonblocking writes remain loud.
