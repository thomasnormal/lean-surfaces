"""leanpy corpus: PRINTING A SET is loud (telemetry row).

Containers render exactly since 2026-08-13, but a set's `repr` is its
HASH ORDER, which the model deliberately never guesses (the order
doctrine: first-seen order is unobservable, so nothing may depend on it).
Loud, never a plausible-looking wrong line.
"""

s = set([1, 2, 3])
print(len(s))
print(s)
