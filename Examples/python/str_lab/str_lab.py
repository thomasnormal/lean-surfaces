"""The H5 string-tier acceptance set: slices (both step directions,
omitted/negative/clamped bounds, CPython's step-first validation order)
and the method trio swapcase/isupper/index — every function here runs
differentially against CPython 3.9 (harness/cases.json). The loud
frontier (non-ASCII case mapping, out-of-tier str methods, list slices,
index start/end arguments) is pinned by whitelisted rows."""


def rev(s):
    return s[::-1]


def mid(s, a, b):
    return s[a:b]


def head(s, n):
    return s[:n]


def tail(s, n):
    return s[n:]


def every_second(s):
    return s[::2]


def back_step(s, a, b):
    return s[a:b:-2]


def copy_all(s):
    return s[:]


def swap(s):
    return s.swapcase()


def isup(s):
    return s.isupper()


def idx(s, t):
    return s.index(t)


def board_flip(s):
    # Position.rotate's exact string chain (sunfish.py line 231)
    return s[::-1].swapcase()


def put(board, i, p):
    # Position.move's put lambda, as a def (sunfish.py line 238)
    return board[:i] + p + board[i + 1 :]


def slice_of_int(n):
    return n[0:2]


def step_zero(s):
    return s[::0]


def bad_lower(s, t):
    return s[t:]


def order_probe(s, t):
    # the step validates FIRST (PySlice_Unpack): ValueError, not the
    # lower bound's TypeError
    return s[t::0]


def swap_arg_raises(s):
    return s.swapcase(1)


def idx_arg_raises(s, n):
    return s.index(n)


def upper_of(s):
    # LIVE since H6 (`value()`'s capture lookup needs it); non-ASCII
    # stays loud
    return s.upper()


def lower_flag(s):
    return s.islower()


def list_slice_is_loud():
    return [1, 2, 3][::-1]


def idx_start_is_loud(s, t, a):
    return s.index(t, a)


def cast_int(s):
    # pass 8 (docs/memory-model.md §the cast tier): int(<str>) -- the
    # honest ASCII subset; exotic acceptances (underscores, Unicode
    # digits) refuse loudly, malformed safe-alphabet strings raise the
    # faithful ValueError
    return int(s)


def cast_str(n):
    # str(...) value-only: exact decimals, True/False, identity, None
    return str(n)


# `%`-formatting (docs/memory-model.md §`%`-formatting on strings): the
# admitted tier is BARE %s/%r/%d/%% over the scalar inventory, CPython's
# single left-to-right pass, both arity TypeErrors faithful. The
# minilanguage and every other conversion character stay loud.


def fmt_opcode(op):
    # opcode.py line 36 verbatim: a %r of an int inside a 1-tuple
    return "<%r>" % (op,)


def fmt_repr(v):
    return "%r" % (v,)


def fmt_bare(v):
    # a NON-tuple right operand is one argument -- same answer as (v,)
    return "%r" % v


def fmt_str(v):
    return "%s" % (v,)


def fmt_dec(v):
    # bool coerces (%d of True is '1' where %s of it is 'True'); a
    # non-number is the faithful TypeError
    return "%d" % (v,)


def fmt_pair(a, b):
    return "%s=%d" % (a, b)


def fmt_pct(n):
    # %% emits one '%' and consumes NO argument
    return "%d%% done" % (n,)


def fmt_noargs():
    return "abc" % ()


def fmt_leftover(v):
    # no conversion at all: the argument is left over -> TypeError
    return "abc" % (v,)


def fmt_short(a):
    # two conversions, one argument -> TypeError
    return "%d %d" % (a,)


def fmt_order(a, b):
    # ONE left-to-right pass: the first conversion's TypeError is raised
    # before the arity of the rest is ever considered
    return "%d %d" % (a, b)


def fmt_nonascii_s():
    return "%s" % ("héllo",)


def fmt_nonascii_r():
    # repr escapes by Unicode PRINTABILITY -- never guessed, so loud
    return "%r" % ("héllo",)


def fmt_width(n):
    # the format minilanguage is a second tier: loud
    return "%5d" % (n,)


def fmt_hex(n):
    # a conversion character CPython supports and this tier does not
    return "%x" % (n,)


def fmt_bad(n):
    # CPython raises ValueError: unsupported format character 'q'; the
    # model refuses LOUDLY rather than inventing the ValueError
    return "%q" % (n,)


def fmt_trailing(n):
    # CPython raises ValueError: incomplete format -- loud here too
    return "%d%" % (n,)


def fmt_container():
    # a container argument's repr is the heap-recursive walk; this
    # operator cannot see the heap, so it refuses instead of guessing
    return "%s" % ((1, 2),)


def fmt_mapping():
    # the %(key)s mapping protocol: the heap-operand refusal fires first
    return "%(k)s" % {"k": 1}


# The MAPPING right operand (docs/memory-model.md §`%`-formatting on
# strings, "the mapping right operand"). PyUnicode_Format sets ctx.dict
# when PyMapping_Check(args) passes and args is neither a tuple nor a
# str -- a LIST and a RANGE both pass -- and the trailing "not all
# arguments converted" check is guarded on !ctx.dict. So a leftover is
# an error for an int and NOT an error for a list.


def fmt_bare_leftover(v):
    # no conversion at all. A non-mapping v is the leftover TypeError; a
    # list or a range comes back as the format string, UNCHANGED
    return "abc" % v


def fmt_seq_arg(v):
    # the mapping is still the ONE positional argument (arglen == -1), so
    # %s consumes it -- and a container's repr is the heap walk this
    # operator cannot see, so the tier refuses where CPython prints '[1]'
    return "%s" % v


def fmt_dec_seq(v):
    # the one argument reaching %d is the WHOLE mapping, so this is the
    # faithful `%d format: a number is required, not list` -- and it is
    # raised on the FIRST conversion, before the second one's arity is
    # ever considered (a non-mapping v takes the same row to
    # `not enough arguments`, which ctx.dict never suppresses)
    return "%d %d" % v


def fmt_range_leftover():
    # range passes PyMapping_Check too: the skip is not list-specific
    return "abc" % range(3)


def fmt_dict_leftover():
    # a dict is the mapping CPython's ctx.dict was named for, and it is
    # LOUD here rather than 'abc': the heap-operand refusal fires before
    # the operator arm, and that is the declared boundary
    return "abc" % {"k": 1}
