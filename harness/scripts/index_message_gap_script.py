"""leanpy corpus: exact `IndexError` text for a list read.

The condition-specific constructors preserve CPython's message at the
runner boundary, so this row checks the complete uncaught-exception line,
not just its class.
"""

xs = [1, 2]
print(len(xs))
print(xs[5])
