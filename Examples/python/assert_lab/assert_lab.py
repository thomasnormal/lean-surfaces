"""assert_lab -- the `assert` acceptance set (docs/memory-model.md
paragraph "the assert statement", the tail batch construct 1).

`assert test` and `assert test, msg` are what CPython compiles to
`if not test: raise AssertionError(msg)` under `__debug__`. The model
runs without `-O`, so the test is ALWAYS evaluated and the statement is
never compiled away; `__debug__` itself stays a loud module dunder.

Two things this battery exists to pin, because both are observable and
neither is guessable:

* THE MESSAGE IS LAZY. CPython evaluates it only when the test is falsy,
  so a message with an effect must not fire on the passing path
  (`lazy_pass` vs `lazy_fail` -- the same function, the two paths).
* THE MESSAGE IS `str()` OF THE VALUE, which is exactly the rendering
  `print` already applies to one argument (CPython's two-level rule:
  `str()` on the argument, `repr()` inside a container). So
  `assert 0, 5` says `AssertionError: 5` and `assert 0, [1, 2]` says
  `AssertionError: [1, 2]`, and the refusals come along for free -- a
  set (hash order), an instance (identity), a non-ASCII string (Unicode
  printability is never guessed) are LOUD, never a guessed repr.

RECORDED GAP, pinned by `catch_assert`: an `AssertionError` can be
RAISED but not CAUGHT. The v0 `try`/`except` tier matches on the class
identity of an admitted `class N(Exception): pass` only, so a handler
naming `AssertionError` refuses loudly exactly as one naming
`ZeroDivisionError` does. That is the existing except-tier boundary, not
a new one, and it is asymmetric on purpose: a loud refusal beats a
handler that silently matches nothing.
"""


def guard_pass(n):
    # the ordinary passing assert: the test is evaluated, nothing raised
    assert n > 0
    return n * 10


def guard_fail(n):
    # the same statement on the failing path: a bare AssertionError, and
    # CPython prints the class name with no message at all
    assert n > 0
    return n * 10


def msg_str(n):
    assert n > 0, "must be positive"
    return n


def msg_int(n):
    # a non-str message: CPython's AssertionError(5) renders as `5`
    assert n > 0, n
    return n


def msg_expr(n):
    # the message is an arbitrary expression, evaluated on the failing path
    assert n > 0, "got " + str(n)
    return n


def talk():
    print("evaluated")
    return "boom"


def lazy_pass(n):
    # the message must NOT be evaluated when the test holds -- the print
    # is the observable, and a strict model would emit it here
    assert n > 0, talk()
    return n


def lazy_fail(n):
    # ... and it MUST be evaluated when the test fails: same source, the
    # other path, so the pair brackets the laziness exactly
    assert n < 0, talk()
    return n


def falsy_list(n):
    # truthiness is the ordinary tier's: an empty list is falsy
    xs = []
    if n > 0:
        xs.append(n)
    assert xs
    return len(xs)


def tuple_test(n):
    # `assert (a, b)` is CPython's classic always-true bug (it warns at
    # compile time and runs); a non-empty tuple is truthy, so this passes
    # for every n and the model must agree rather than special-case it
    assert (n > 0, "never checked")
    return n


def in_loop(n):
    total = 0
    i = 0
    while i < n:
        assert i < 3, "loop guard"
        total = total + i
        i = i + 1
    return total


def after_effect(n):
    # the retained-state question for a RAISE out of a function: the
    # append happened, the frame is gone, the caller sees the exception
    xs = [1]
    xs.append(2)
    assert n > 0
    return len(xs)


def nested_call(n):
    # an assert failing in a callee unwinds the caller too
    return guard_pass(n) + 1


# ---- the refusal battery (each whitelisted-unsupported) ----


def msg_set(n):
    # a set message: hash order is never guessed, so the RENDERING is
    # loud -- the print tier's refusal, reused rather than re-decided
    assert n > 0, {1, 2}
    return n


def msg_nonascii(n):
    assert n > 0, "héllo"
    return n


def catch_assert(n):
    # WAS the recorded gap ("AssertionError is not an admitted handler
    # class") until §except-builtin admitted it. A comment describing a
    # LIMITATION, expiring with the inch that lifted it -- the fourth of
    # that shape this lane has hit, and the first found in a WITNESS
    # rather than in a docstring or a proof.
    try:
        assert n > 0
    except AssertionError:
        return -1
    return n
