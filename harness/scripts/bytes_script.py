data = b"a\n\x00\xff"
print(data, repr(data), str(data))
total = 0
for element in data:
    total += element
print(total)
print(tuple(data), list(data))
print(data[::-1], b"\xff" in data, 255 in data)
