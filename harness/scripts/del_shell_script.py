# a module-scope del INSIDE a control shell (the `if` shell publishes
# per statement): removes the global on the taken path, then rebinding
# and reading are ordinary global traffic.
x = 1
if x > 0:
    del x
x = 2
print(x)
