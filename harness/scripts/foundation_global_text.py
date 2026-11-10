"""Structured-global confirmation witness with a declaration over 200 chars."""

alpha_counter_one = 0
alpha_counter_two = 0
alpha_counter_three = 0
alpha_counter_four = 0
alpha_counter_five = 0
alpha_counter_six = 0
alpha_counter_seven = 0
alpha_counter_eight = 0
alpha_counter_nine = 0
alpha_counter_ten = 0
alpha_counter_eleven = 0


def bump():
    global alpha_counter_one, alpha_counter_two, alpha_counter_three, alpha_counter_four, alpha_counter_five, alpha_counter_six, alpha_counter_seven, alpha_counter_eight, alpha_counter_nine, alpha_counter_ten, alpha_counter_eleven
    alpha_counter_eleven += 5


bump()
print(alpha_counter_eleven)
