"""Oversized sequence multiplication is loud until materialization is modeled."""

print(len("ab" * (2 ** 62)))
