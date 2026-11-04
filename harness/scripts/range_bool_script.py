print(range(False))
print(range(True))
print(range(False, True))
print(range(True, False))
print(range(True, 5, True))
print(range(True, False, -1))
print([range(False), range(True), range(False, True), range(True, 5, 2)])
print((range(False, True, True), range(True, False, -1)))
print({"bounds": range(True, 5, 2)})
print(len(range(True)), list(range(False, 5, True)), tuple(range(True, 5, 2)))
try:
    range(False, True, False)
except ValueError:
    print("zero Boolean step")
