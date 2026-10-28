# Qualified if fallback

The legacy self-check tier lowers a `priority if` chain with a final `else`
to its ordinary first-match conditional because the qualifier has no possible
no-match diagnostic. It also lowers a `unique if` chain when its named
conditions are distinct literal equalities over one integral variable and the
final `else` covers the no-match path. Overlapping, dynamic, and missing
fallback cases remain loud because their qualifier diagnostics are observable.
