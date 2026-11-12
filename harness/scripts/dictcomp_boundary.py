"""A direct CPython 3.9 DictComp row for the next P3 price.

The approved AST extractor preserves this node, while the current tier has no
native dictionary-comprehension evaluator.  The row keeps the exact oracle
answer visible while the measured token.py payoff is assessed separately.
"""

print({x: x * x for x in (1, 2, 3)})
