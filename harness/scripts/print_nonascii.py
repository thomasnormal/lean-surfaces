"""leanpy corpus: Unicode strings inside a container use CPython repr.

`print("héllo")` is fine — `str()` of a str is the string itself. Inside
a container CPython applies `repr()`, which escapes by Unicode
PRINTABILITY. The model pins the CPython 3.9 Unicode 13.0 table, so printable
Greek and emoji stay direct while format characters use `\\u` escapes.
"""

print("héllo")
print(["héllo"])
print("λ😀")
print(["λ😀"])
print(["\u200b"])
