"""leanpy v0 corpus: the genuinely order-sensitive interleaving — a call
site textually before the def. CPython: NameError; leanpy: loud refusal
(the static function table would bind it early — silently wrong)."""
print(f())


def f():
    return 1
