"""leanpy corpus: the %-format MINILANGUAGE is a second tier — LOUD.

Flags, widths, precisions, length modifiers and `%(key)s` mapping keys
are not modelled; only the bare `%s`/`%r`/`%d`/`%%` conversions are
(docs/memory-model.md §`%`-formatting on strings). CPython prints
`[    3]` here; the model refuses rather than guessing the padding.
"""

print("[%5d]" % (3,))
