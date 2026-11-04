try:
    try:
        raise BaseException
    except Exception:
        print("wrong")
except BaseException:
    print("base")
try:
    raise RecursionError
except RuntimeError:
    print("runtime")
try:
    try:
        try:
            try:
                raise ValueError
            except ArithmeticError:
                print("wrong arithmetic")
        except LookupError:
            print("wrong lookup")
    except RuntimeError:
        print("wrong runtime")
except ValueError:
    print("value")
