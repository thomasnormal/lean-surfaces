"""CPython statistics.median/median_low/median_high, vendored verbatim for
the Lean verification benchmark (Band C marker: sorted() and float division).

Provenance:
  package : CPython standard library, module `statistics`
  version : Python 3.9.25 (system interpreter of this repo's toolchain)
  file    : /usr/lib64/python3.9/statistics.py, sha256
            8dd0406ee8988d42bcb41577e4e45c61bf78423d5158738ce765df96b99b3c23
  license : PSF License Agreement for Python 3.9.25 (PSF-2.0);
            Copyright (c) 2001-2026 Python Software Foundation.

Vendoring rules (python benchmark, Examples/python/bench_statistics):
  * median, median_low and median_high are BYTE-VERBATIM copies of
    statistics.py 3.9.25 lines 414-435, 438-457 and 460-476 (sha256 of
    the three segments:
    a080def79e00b8e0ebfc97c939f0de4da98ffc4e0f2175b3368d5f4a7e4626d5
    015bade9957c587f7bb8ee5780130947ebe5e2763275c72e6da86c4cfb22f91a
    a729908c0174de108336948f5a09c5284cace300e37eb0a64ace0c5b35d7dc69). Do NOT edit their bodies.
  * StatisticsError is NOT vendored: it occurs only inside the
    empty-input raise statements -- no nonempty-input run evaluates the
    name (rsa_inverse rule). statistics.mean is NOT vendored at all
    (census reference only): it drags in _sum/_convert/Fraction --
    documented in docs/benchmark.md.
  * `sorted` is the builtin, resolved at call time; nothing else of
    statistics.py is referenced.

Authenticity (2026-07-29, Python 3.9.25): median([1,3,5]) = 3,
median([1,3,5,7]) = 4.0 (a float), median_low([1,3,5,7]) = 3,
median_high([1,3,5,7]) = 5 computed against this file AND against the
installed `statistics` module -- both agree.
"""

def median(data):
    """Return the median (middle value) of numeric data.

    When the number of data points is odd, return the middle data point.
    When the number of data points is even, the median is interpolated by
    taking the average of the two middle values:

    >>> median([1, 3, 5])
    3
    >>> median([1, 3, 5, 7])
    4.0

    """
    data = sorted(data)
    n = len(data)
    if n == 0:
        raise StatisticsError("no median for empty data")
    if n % 2 == 1:
        return data[n // 2]
    else:
        i = n // 2
        return (data[i - 1] + data[i]) / 2

def median_low(data):
    """Return the low median of numeric data.

    When the number of data points is odd, the middle value is returned.
    When it is even, the smaller of the two middle values is returned.

    >>> median_low([1, 3, 5])
    3
    >>> median_low([1, 3, 5, 7])
    3

    """
    data = sorted(data)
    n = len(data)
    if n == 0:
        raise StatisticsError("no median for empty data")
    if n % 2 == 1:
        return data[n // 2]
    else:
        return data[n // 2 - 1]

def median_high(data):
    """Return the high median of data.

    When the number of data points is odd, the middle value is returned.
    When it is even, the larger of the two middle values is returned.

    >>> median_high([1, 3, 5])
    3
    >>> median_high([1, 3, 5, 7])
    5

    """
    data = sorted(data)
    n = len(data)
    if n == 0:
        raise StatisticsError("no median for empty data")
    return data[n // 2]
