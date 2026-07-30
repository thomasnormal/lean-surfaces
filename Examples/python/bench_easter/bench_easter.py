"""Gregorian/Julian Easter computus (python-dateutil easter.easter),
vendored verbatim for the Lean verification benchmark (Band B aspirational:
a pure-integer Gauss-style computus behind a thin datetime shell).

Provenance:
  package : python-dateutil, https://pypi.org/project/python-dateutil/
  version : 2.9.0.post0 (pip download --no-deps python-dateutil,
            2026-07-21; sdist python-dateutil-2.9.0.post0.tar.gz, sha256
            37dd54208da7e1cd875388217d5e00ebd4179249f90fb72437e91a35459a0ad3)
  file    : src/dateutil/easter.py, sha256
            772062fa52af8a61f5bbf93aa7b6742492bbd9086a56d541b2a072be910f2af7
  license : Apache-2.0 / BSD-3-Clause dual license; Copyright 2003-2011
            Gustavo Niemeyer, 2012-2014 Tomi Pievilainen, 2014-2016
            Yaron de Leeuw, 2015- Paul Ganssle and dateutil contributors.

Vendoring rules (python benchmark, Examples/python/bench_easter):
  * `import datetime` (line 7), the EASTER_JULIAN/EASTER_ORTHODOX/
    EASTER_WESTERN constants (lines 11-13) and the easter function
    (lines 16-89) are BYTE-VERBATIM copies of easter.py 2.9.0.post0
    (sha256 of the three segments:
    a47bc67d7a652367f6b2cfb2786dcd9067ea20f42e786a52f48bf676c0815782
    68317e7690f54385b983ae365ee82e884a9b99ba9ba2563ad3a407f03b1595ca
    769fd10661c24791d0788b6e72716093db34c3e1b236b1854f22f0ae40da802a). Do NOT edit their bodies.
  * `import datetime` and the constants are retained because both are
    needed at def/call time: the default `method=EASTER_WESTERN`
    evaluates the module constant at def time, and every call ends in
    `datetime.date(int(y), int(m), int(d))`.

Authenticity (2026-07-29, Python 3.9.25): easter(2026) =
datetime.date(2026, 4, 5), easter(2026, 2) = datetime.date(2026, 4, 12),
easter(2026, 1) = datetime.date(2026, 3, 30), easter(2000) =
datetime.date(2000, 4, 23) computed against this file AND against the
unpacked python-dateutil-2.9.0.post0 sdist module -- both agree.
"""

import datetime

EASTER_JULIAN = 1
EASTER_ORTHODOX = 2
EASTER_WESTERN = 3

def easter(year, method=EASTER_WESTERN):
    """
    This method was ported from the work done by GM Arts,
    on top of the algorithm by Claus Tondering, which was
    based in part on the algorithm of Ouding (1940), as
    quoted in "Explanatory Supplement to the Astronomical
    Almanac", P.  Kenneth Seidelmann, editor.

    This algorithm implements three different Easter
    calculation methods:

    1. Original calculation in Julian calendar, valid in
       dates after 326 AD
    2. Original method, with date converted to Gregorian
       calendar, valid in years 1583 to 4099
    3. Revised method, in Gregorian calendar, valid in
       years 1583 to 4099 as well

    These methods are represented by the constants:

    * ``EASTER_JULIAN   = 1``
    * ``EASTER_ORTHODOX = 2``
    * ``EASTER_WESTERN  = 3``

    The default method is method 3.

    More about the algorithm may be found at:

    `GM Arts: Easter Algorithms <http://www.gmarts.org/index.php?go=415>`_

    and

    `The Calendar FAQ: Easter <https://www.tondering.dk/claus/cal/easter.php>`_

    """

    if not (1 <= method <= 3):
        raise ValueError("invalid method")

    # g - Golden year - 1
    # c - Century
    # h - (23 - Epact) mod 30
    # i - Number of days from March 21 to Paschal Full Moon
    # j - Weekday for PFM (0=Sunday, etc)
    # p - Number of days from March 21 to Sunday on or before PFM
    #     (-6 to 28 methods 1 & 3, to 56 for method 2)
    # e - Extra days to add for method 2 (converting Julian
    #     date to Gregorian date)

    y = year
    g = y % 19
    e = 0
    if method < 3:
        # Old method
        i = (19*g + 15) % 30
        j = (y + y//4 + i) % 7
        if method == 2:
            # Extra dates to convert Julian to Gregorian date
            e = 10
            if y > 1600:
                e = e + y//100 - 16 - (y//100 - 16)//4
    else:
        # New method
        c = y//100
        h = (c - c//4 - (8*c + 13)//25 + 19*g + 15) % 30
        i = h - (h//28)*(1 - (h//28)*(29//(h + 1))*((21 - g)//11))
        j = (y + y//4 + i + 2 - c + c//4) % 7

    # p can be from -6 to 56 corresponding to dates 22 March to 23 May
    # (later dates apply to method 2, although 23 May never actually occurs)
    p = i - j + e
    d = 1 + (p + 27 + (p + 6)//40) % 31
    m = 3 + (p + 26)//30
    return datetime.date(int(y), int(m), int(d))
