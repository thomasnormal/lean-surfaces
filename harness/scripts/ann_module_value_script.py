def mark(value):
    print(value)
    return value


x: "int" = 3

if True:
    y: "int" = 4

print(x + y)
target: "int" = mark(8)
print(target)

try:
    kept: None = mark(9)
    1 // 0
except ZeroDivisionError:
    print(kept)

for index in range(2):
    item: True = index
    print(item)

numeric: 42 = 10
print(numeric)
