"""Global declarations are carried as AST names, without text reparsing."""

counter_one = 0
counter_two = 0
counter_three = 0
counter_four = 0
counter_five = 0
counter_six = 0
counter_seven = 0
counter_eight = 0
counter_nine = 0
counter_ten = 0
counter_eleven = 0


def set_counter():
    global counter_one, counter_two, counter_three, counter_four, counter_five, counter_six, counter_seven, counter_eight, counter_nine, counter_ten, counter_eleven
    counter_eleven = 5


set_counter()
print(counter_eleven)
