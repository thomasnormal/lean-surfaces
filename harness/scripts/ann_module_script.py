# Module-scope annotations of unshadowed builtin type names are pure in the
# tier: the assignment is retained and the implicit annotation-table update
# is unobservable. Effectful and shadowed annotations remain loud in the
# companion fixtures.
x: int = 3
print(x)
