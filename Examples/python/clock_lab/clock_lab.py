"""clock_lab — the TRACE-CLOCK battery (docs/memory-model.md §the trace
clock).

Time is an INPUT: the model threads a clock trace through the world and
`time.time()` pops the next reading; an empty trace is the loud underrun
refusal. The differential rows run under record-replay: the CPython side
of each row binds this module's `time` name to a stub replaying (or
recording) the same integer trace the model consumes — both sides see
literally the same readings.

The battery's shape mirrors the shipped file's single in-tier clock
consumer (`sunfish.py` line 328) at lab modulus: MiniSearcher checks the
clock every 4th node against `self.deadline` (init `1 << 63`, the
post-#158 dead-clock regime) and raises `Stop` when a reading exceeds
it — the raise-through-resume-into-handler path of the exceptions tier,
now reachable through the clock.

Rows: happy pops (`read_clock`, `read_twice` — subtraction on readings),
the dead-clock run (`dead_clock`: readings consumed, never binding),
the armed run (`armed`: Stop mid-loop at the exact reading CPython
stops), the underrun refusal (short trace), and the admission's edges
(`shadowed` — a local `time` never pops; `call_with_arg` —
`time.time(1)` refuses loudly; `pure_sum` — no clock at all, the
lab-scale trace-independence theorem's subject).
"""

import time


class Stop(Exception):
    pass


class MiniSearcher:
    def __init__(self):
        self.nodes, self.deadline = 0, 1 << 63

    def run(self, n):
        # the shipped guard's shape (sunfish.py line 328) at lab modulus
        total = 0
        while self.nodes < n:
            self.nodes += 1
            if self.nodes % 4 == 0 and time.time() > self.deadline:
                raise Stop
            total += self.nodes
        return total


def read_clock():
    # one pop, verbatim
    return time.time()


def read_twice():
    # readings are opaque ints: comparison and subtraction are exact
    a = time.time()
    b = time.time()
    return (a, b, b - a)


def dead_clock(n):
    # deadline stays 1 << 63: readings are consumed but never bind
    s = MiniSearcher()
    try:
        v = s.run(n)
    except Stop:
        return (-1, s.nodes)
    return (v, s.nodes)


def armed(deadline, n):
    # the deadline binds mid-run: Stop propagates into the driver's handler
    s = MiniSearcher()
    s.deadline = deadline
    try:
        v = s.run(n)
    except Stop:
        return (-1, s.nodes)
    return (v, s.nodes)


def shadowed():
    # a LOCAL `time` shadows the clock: no pop — the ordinary loud
    # method-call refusal (CPython: AttributeError on the int)
    time = 3
    return time.time()


def call_with_arg():
    # CPython evaluates the arg then raises TypeError; the model refuses
    # loudly (never fakes what it can refuse)
    return time.time(1)


def pure_sum(n):
    # never consults the clock: the lab-scale subject of the first
    # trace-quantified theorem (result identical for ALL traces)
    total = 0
    i = 1
    while i <= n:
        total += i
        i += 1
    return total
