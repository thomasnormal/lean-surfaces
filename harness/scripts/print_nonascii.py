"""leanpy corpus: a Latin-1 string inside a container uses direct repr.

`print("héllo")` is fine — `str()` of a str is the string itself. Inside
a container CPython applies `repr()`, which escapes by Unicode
PRINTABILITY, and the admitted Latin-1 intervals are exact. Unicode outside
that table remains loud.
"""

print("héllo")
print(["héllo"])
