"""leanpy corpus: first-class dictionary views stay live after mutation."""

d = {"a": 1}
keys = d.keys()
d["b"] = 2
print(len(keys))
print(list(keys))

values = d.values()
d["a"] = 3
print(list(values))

items = d.items()
d["c"] = 4
print(list(items))
