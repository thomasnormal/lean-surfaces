def unused_import():
    import typing
    return 1

def unused_from_import():
    from typing import Tuple
    return 2

def unused_dotted_from_import():
    from email.encoders import encode_7or8bit
    return 4

def opaque_attribute():
    import typing
    return typing.Tuple

def opaque_call():
    import typing
    return typing.Tuple()

def opaque_truth():
    import typing
    return bool(typing)

def opaque_print():
    import typing
    print(typing)
    return 3

def opaque_argument():
    import typing
    return len(typing)

def unallowlisted_import():
    import os
    return 4
