# Priority case fallback

The legacy self-check tier lowers `priority case` and `priority casez` when an
explicit `default` covers the qualifier's no-match path. The existing case
subject and pattern purity checks remain in force; cases without a fallback,
dynamic effects, and scheduler-facing forms remain loud.
