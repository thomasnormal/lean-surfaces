"""Acceptance battery for `JoinedStr` (f-strings) — the tail batch,
construct 2. Pinned against CPython 3.9 BEFORE anything is built.

Every function here is a diff_test row: it returns a value the harness
compares against CPython. The battery is written to catch the ways a
model could be WRONG rather than to demonstrate that it is right, so the
refusal cases are as load-bearing as the matching ones.

The design claim under test: an f-string's `{x}` with no conversion and
no format spec is exactly `str(x)` — the SAME operation `print` applies
to one argument and `assert` applies to its message, i.e. `printOne`.
If that is true, f-strings inherit the two-level rule and its pinned
refusals for free, and no new renderer is written.
"""


# ---------------------------------------------------------------- basics


def plain(n):
    # no interpolation at all: an f-string with no fields is just a string
    return f"plain"


def one_field(n):
    return f"{n}"


def text_around(n):
    return f"a{n}b"


def two_fields(n):
    return f"{n}{n}"


def adjacent_text(n):
    return f"x={n}, y={n + 1}!"


def expr_inside(n):
    # an arbitrary expression, not just a name
    return f"{n * 2 + 1}"


def call_inside(n):
    return f"{abs(n)}"


def empty_fstring(n):
    return f""


# ------------------------------------------------- the two-level rule


def str_field(n):
    # THE decisive row: a str field uses str(), NOT repr() -- so no quotes.
    # This is the same property that made assert's non-ASCII message a
    # MATCH rather than a refusal (2026-08-13 measured correction).
    s = "hi"
    return f"[{s}]"


def str_field_with_quote(n):
    s = "it's"
    return f"[{s}]"


def list_field(n):
    # a container: str() of a list applies repr() to the ELEMENTS, so the
    # strings inside DO get quotes. One level down from str_field.
    xs = ["a", "b"]
    return f"{xs}"


def tuple_field(n):
    return f"{(1, 2)}"


def none_field(n):
    return f"{None}"


def bool_field(n):
    return f"{True}/{False}"


def int_negative(n):
    return f"{-n}"


# -------------------------------------------------------- literal braces


def literal_braces(n):
    # `{{` and `}}` are escapes for single braces -- NOT interpolation
    return f"{{{n}}}"


def only_braces(n):
    return f"{{}}"


# ------------------------------------------- non-ASCII (measure, do not predict)


def nonascii_text(n):
    # literal non-ASCII in the TEXT of an f-string
    return f"héllo {n}"


def nonascii_field(n):
    s = "héllo"
    return f"[{s}]"


# ------------------------------------------------- expected REFUSALS


def conversion_repr(n):
    # !r asks for repr() explicitly -- a different operation from str()
    s = "hi"
    return f"{s!r}"


def conversion_str(n):
    s = "hi"
    return f"{s!s}"


def format_spec(n):
    # a format spec is a whole mini-language (fill/align/width/precision)
    return f"{n:>5}"


def format_spec_num(n):
    return f"{n:03d}"


def debug_spec(n):
    # 3.8+ `=` specifier: emits the SOURCE TEXT plus the value
    return f"{n=}"


def set_field(n):
    # inherits printOne's set refusal (hash order is never guessed)
    return f"{ {1, 2} }"


def nested_fstring(n):
    return f"{f'{n}'}"
