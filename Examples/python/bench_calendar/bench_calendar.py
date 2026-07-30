"""CPython calendar.isleap/leapdays, vendored verbatim for the Lean
verification benchmark (Band B, pure integer arithmetic -- in-tier today).

Provenance:
  package : CPython standard library, module `calendar`
  version : Python 3.9.25 (system interpreter of this repo's toolchain)
  file    : /usr/lib64/python3.9/calendar.py, sha256
            3ef1adcb836f240e3ae9d00de4466735e6e92ec74620737bb51605a123510ec8
  license : PSF License Agreement for Python 3.9.25 (PSF-2.0);
            Copyright (c) 2001-2026 Python Software Foundation.

Vendoring rules (python benchmark, Examples/python/bench_calendar):
  * isleap and leapdays are BYTE-VERBATIM copies of calendar.py 3.9.25
    lines 100-102 and 105-110 (sha256 of the two segments:
    fdb511accefe85bdddfe88197f58cc293725ad6ccd08c8e2e5f774603d3b12d6
    ddb3b4ed6e55b331968a7def7ccb90abf66e15e44e389f8acca71d22404e0f79). Do NOT edit their bodies.
  * Nothing else of calendar.py is vendored; neither function references
    any module-level name.

Authenticity (2026-07-29, Python 3.9.25): isleap(2024) = True,
isleap(1900) = False, isleap(2000) = True, leapdays(1900, 2000) = 24,
leapdays(2000, 2026) = 7 computed against this file AND against the
installed `calendar` module -- both agree.
"""

def isleap(year):
    """Return True for leap years, False for non-leap years."""
    return year % 4 == 0 and (year % 100 != 0 or year % 400 == 0)

def leapdays(y1, y2):
    """Return number of leap years in range [y1, y2).
       Assume y1 <= y2."""
    y1 -= 1
    y2 -= 1
    return (y2//4 - y1//4) - (y2//100 - y1//100) + (y2//400 - y1//400)
