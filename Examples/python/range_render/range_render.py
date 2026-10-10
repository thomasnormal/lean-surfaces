def stop_str(value):
    return str(range(value))


def bounds_str(start, stop):
    return str(range(start, stop))


def step_str(start, stop, step):
    return str(range(start, stop, step))


def stop_fstring(value):
    return f"{range(value)}"


def bounds_fstring(start, stop):
    return f"{range(start, stop)}"


def step_fstring(start, stop, step):
    return f"{range(start, stop, step)}"


def list_str(start, stop, step):
    return str([range(start, stop, step)])


def tuple_str(start, stop, step):
    return str((range(start, stop, step),))


def dict_str(start, stop, step):
    return str({"bounds": range(start, stop, step)})


def stop_numeric(value):
    return len(range(value)), list(range(value)), tuple(range(value))


def bounds_numeric(start, stop, step):
    return len(range(start, stop, step)), list(range(start, stop, step)), tuple(range(start, stop, step))


def index(start, stop, step, position):
    return tuple(range(start, stop, step))[position]


def loop_sum(start, stop, step):
    total = 0
    for value in range(start, stop, step):
        total += value
    return total
