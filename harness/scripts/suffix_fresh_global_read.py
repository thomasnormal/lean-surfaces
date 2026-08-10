"""Refusal row (the fake-NameError hazard, pinned by the 2026-08-10
prefix-view fix): the live suffix binds a FRESH module global a function
body reads. CPython makes `w = 7` a module global, so readw() answers 7;
under the prefix view the name is absent from an always-analysable G1
table, so running this would raise a fake NameError inside the call —
`suffixConsistent` refuses the whole script loudly."""


def readw():
    return w


print(1)
w = 7
print(readw())
