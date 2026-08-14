# module scope: locals ARE the globals (the publish), so the del removes
# the module global and the later read is CPython's faithful NameError.
b = 5
print(b)
del b
print(b)
