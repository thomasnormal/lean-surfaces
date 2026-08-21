# §L49 rung 2: a MODULE-scope annotated assignment stays LOUD. CPython
# evaluates the annotation here (and writes `__annotations__`) AFTER
# storing the value, so rewriting it to a plain assign would skip an
# observable evaluation -- the function-body rewrite is sound precisely
# because PEP 526 does NOT evaluate there.
x: int = 3
print(x)
