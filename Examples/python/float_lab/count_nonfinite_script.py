from itertools import count

nan_values = count(float("nan"), 1.0)
print(next(nan_values))
print(next(nan_values))

infinite_values = count(float("inf"), 1.0)
print(next(infinite_values))
print(next(infinite_values))
