def repeat(text, count):
    return text * count


def augmented(text, count):
    text *= count
    return text


text = "ab"
text *= 3
print(text)
print(3 * "xy")
print(repeat("λ😀", 2))
print(augmented("a\x00b", 2))
print("[" + "abc" * 0 + "]")
print("[" + -3 * "abc" + "]")
print(repeat("xy", True))
print(repeat("xy", False))
print(True * "xy")
print(False * "xy")
print(augmented("λ", True))
print(len("ab" * 3))
