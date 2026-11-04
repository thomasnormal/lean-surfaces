"""Assert content extracted from CPython 3.9.19 Lib/test (the official
leanpy bench, stage 1 — docs/backlog.md): values printed rather than
asserted (`assert` is outside the tier); slice/repr lines dropped.

from: Lib/test/list_tests.py CommonTest.test_getitem (index/negative/IndexError shapes)
from: Lib/test/test_list.py ListTest.test_basic (equality/len lines)
from: Lib/test/list_tests.py CommonTest.test_setitem (in-place store)
"""

a = [0, 1, 2, 3, 4]
print(len(a))
print(a[0])
print(a[4])
print(a[-1])
print(a[-5])
print(a == [0, 1, 2, 3, 4])
print(a == [0, 1, 2, 3])
b = a
b[2] = 99
print(a[2])
b.append(5)
print(len(a))
print(4 in a)
print(2 in a)
