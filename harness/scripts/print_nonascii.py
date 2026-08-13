"""leanpy corpus: a NON-ASCII string inside a container is loud.

`print("héllo")` is fine — `str()` of a str is the string itself. Inside
a container CPython applies `repr()`, which escapes by Unicode
PRINTABILITY, a table this model never guesses (the same doctrine that
keeps `.swapcase()` ASCII-only). Loud rather than plausible.
"""

print("héllo")
print(["héllo"])
