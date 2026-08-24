"""exc_lab -- the exceptions acceptance set (docs/memory-model.md
paragraph "exceptions", BUILT pass 4).

The admitted surface, each row differential against CPython:
`class N(Exception): pass` as a raisable class NAME (class identity, no
payload), `raise N`, and the v0 single-handler `try`/`except N:` on the
retained-state covenant -- mutations up to the raise stay visible in the
handler, a non-matching class propagates (out of nested tries and out of
the whole call), a raise UNWINDS nested calls, and an exception
propagating through a generator RESUME closes the generator (the
gen_lab status pin's differential twin, observable now that a handler
can survive the raise).

The deadline capstone is the shape sunfish's Stop serves, with the wall
clock replaced by a node counter: MiniSearcher.walk raises Stop from a
resumed generator frame when its budget passes, and the driver's
try/except catches it mid-iteration -- raise-through-resume-into-handler
end to end.

The refusal battery (whitelisted rows + raw #guards in spec.lean) pins
the loud frontier: `as` bindings, `finally`, `else`, bare except,
multiple handlers, tuple patterns, `except Exception`, builtin-name
matching, raise with arguments, bare raise, value raise, raise-from,
shadowed names, exception classes as values, and yield-under-try.

The WALL-CLOCK battery (docs/memory-model.md "Wall-clock time", as
AMENDED by pass 6's trace clock): `time_dead` proves the shipped
guard's short-circuit keeps the clock dead (deadline None,
differential MATCH -- nothing is popped), `time_live` proves the
moment a deadline makes the clock live, evaluation under this
harness's EMPTY trace refuses loudly (the underrun -- pass 6 moved
the refusal from the poisoned binding to the trace pop; the full
live-clock battery is `clock_lab`).
"""

import time


class Stop(Exception): pass


class Other(Exception):
    pass


def catch_ret(n):
    # the raise-catch roundtrip; the untouched path returns through the body
    try:
        if n > 0:
            raise Stop
        return 1
    except Stop:
        return 2


def catch_state(n):
    # the retained-state covenant, OBSERVABLE: mutations before the raise
    # survive into the handler (no rollback -- CPython's unwinding)
    acc = []
    try:
        acc.append(1)
        if n > 0:
            raise Stop
        acc.append(2)
    except Stop:
        acc.append(30)
    return len(acc) * 100 + acc[-1]


def wrong_class(n):
    # a non-matching class PROPAGATES out of the whole call
    try:
        if n > 0:
            raise Stop
        return 0
    except Other:
        return -1


def nested_try(n):
    # nested try: the inner handler does not match, the outer does
    try:
        try:
            raise Stop
        except Other:
            return -1
    except Stop:
        return 7


def raise_flows(n):
    # flow THROUGH a handler: break inside except routes as ordinary flow
    total = 0
    i = 0
    while i < n:
        try:
            if i == 3:
                raise Stop
            total = total + i
        except Stop:
            break
        i = i + 1
    return total


def helper(n):
    if n > 0:
        raise Stop
    return n * 10


def through_call(n):
    # a raise UNWINDS the callee frame; the caller's handler catches
    try:
        return helper(n)
    except Stop:
        return 99


def gen_raises(n):
    yield 1
    if n == 0:
        raise Stop
    yield 2 // n
    yield 3


def gen_closes(n):
    # an exception through a RESUME closes the generator: after the
    # caught raise, the next step is exhaustion (StopIteration out of
    # the call for n = 0 -- the differential pin of the close decision)
    g = gen_raises(n)
    a = next(g)
    try:
        a = a + next(g)
    except Stop:
        a = a + 100
    return a * 10 + next(g, -5)


def gen_closes_hard(n):
    # same, but the post-close next() has NO default: n = 0 must raise
    # StopIteration (a closed frame), never "already executing"
    g = gen_raises(n)
    next(g)
    try:
        next(g)
    except Stop:
        pass
    return next(g)


def for_over_raising(n):
    # the raise escapes a for-over-generator into the loop's enclosing
    # handler; the loop does not resume
    total = 0
    try:
        for x in gen_raises(n):
            total = total + x
    except Stop:
        total = total + 1000
    return total


class MiniSearcher:
    def __init__(self, limit):
        self.nodes = 0
        self.limit = limit

    def walk(self, n):
        # bound()'s deadline shape with the wall clock replaced by the
        # node counter: the raise fires INSIDE a resumed frame
        i = 0
        while i < n:
            self.nodes = self.nodes + 1
            if self.nodes > self.limit:
                raise Stop
            yield i
            i = i + 1

    def run(self, n):
        best = 0
        try:
            for x in self.walk(n):
                best = best + x
        except Stop:
            return -best
        return best


def deadline_capstone(n, limit):
    # raise-through-resume-into-handler, end to end; the node budget is
    # the deadline (docs/memory-model.md paragraph "exceptions": the
    # capstone leaves time.time() exactly where it is)
    s = MiniSearcher(limit)
    r = s.run(n)
    return r * 1000 + s.nodes


def time_dead(n):
    # the SHIPPED guard shape under deadline = None: the and-chain
    # short-circuits at its first conjunct, so the wall clock is never
    # evaluated -- a differential MATCH row (the soundness half of the
    # recorded time.time() abstraction)
    deadline = None
    nodes = 0
    total = 0
    i = 0
    while i < n:
        nodes = nodes + 1
        if deadline is not None and nodes % 2 == 0 and time.time() > deadline:
            return -1
        total = total + i
        i = i + 1
    return total


def time_live(n):
    # deadline SET: evaluation reaches time.time() -- under this row's
    # EMPTY trace that is the loud underrun refusal (pass 6: the pop
    # replaced the poisoned-binding wall) -- whitelisted row
    deadline = 5
    nodes = 0
    while nodes < n:
        nodes = nodes + 1
        if deadline is not None and nodes % 2 == 0 and time.time() > deadline:
            return -1
    return nodes


# ---- the refusal battery (each function whitelisted-unsupported) ----


def as_binding(n):
    try:
        raise Stop
    except Stop as e:
        return n


def finally_clause(n):
    try:
        return n
    finally:
        pass


def else_clause(n):
    try:
        n = n + 1
    except Stop:
        return 0
    else:
        return n


def bare_except(n):
    try:
        return 1 // n
    except:
        return -1


def multi_handler(n):
    try:
        raise Stop
    except Stop:
        return 1
    except Other:
        return 2


def tuple_handler(n):
    try:
        raise Stop
    except (Stop, Other):
        return 1


def except_exception(n):
    try:
        raise Stop
    except Exception:
        return 1


def except_builtin(n):
    try:
        return 1 // n
    except ZeroDivisionError:
        return -1


def raise_args(n):
    raise Stop("with a message")


def raise_bare(n):
    try:
        raise Stop
    except Stop:
        raise


def raise_value(n):
    raise n


def raise_from(n):
    raise Stop from None


def raise_shadowed(n):
    Stop = n
    raise Stop


def exc_as_value(n):
    x = Stop
    return n


def yield_under_try(n):
    try:
        yield n
    except Stop:
        pass


def drive_yield_under_try(n):
    total = 0
    for x in yield_under_try(n):
        total = total + x
    return total


def except_ancestor_still_loud(n):
    # §except-builtin THE FRONTIER, and it is falsifiable: ArithmeticError is
    # ZeroDivisionError's CPython ancestor, so CPython answers -1 here.
    # Admitting it would claim a catch set this tier has never enumerated, so
    # it is refused BY NAME rather than derived from a hierarchy. The day an
    # inch needs it, this row flips and the pair below stays put.
    try:
        return 1 // n
    except ArithmeticError:
        return -1

