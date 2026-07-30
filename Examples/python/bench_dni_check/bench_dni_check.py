"""Spanish DNI check letter (python-stdnum stdnum.es.dni.calc_check_digit),
vendored verbatim for the Lean verification benchmark (Band B: one builtin
`int` call away from the v0 tier).

Provenance:
  package : python-stdnum, https://pypi.org/project/python-stdnum/
  version : 2.2 (pip download --no-deps python-stdnum, 2026-07-21; sdist
            python_stdnum-2.2.tar.gz, sha256
            e95fcfa858a703d4a40130cb3eaac133c60d8808a7f3c98efeedac968c2479b9)
  file    : stdnum/es/dni.py, sha256
            d1fc9a757a5467dad759cacb4dfadb7a9ee4d36af24b005ecb0b40c3f0bf9d97
  license : LGPL-2.1-or-later. The functions below are Copyright (C)
            2010-2021 Arthur de Jong, licensed under the GNU Lesser
            General Public License version 2.1 or later.

Vendoring rules (python benchmark, Examples/python/bench_dni_check):
  * calc_check_digit is a BYTE-VERBATIM copy of stdnum/es/dni.py 2.2
    lines 53-56 (segment sha256:
    c61b9da75aa3c37c3bcbbf968eca1251c6ec2161fbfed28625aacba3a1b54d5b). Do NOT edit its body.
  * compact/validate/is_valid of dni.py are NOT vendored: they depend on
    stdnum.util.clean/isdigits (regex machinery) -- census entries only.
  * `from __future__ import annotations` IS retained from the original
    module (annotations stay lazy, as in the original); the stdnum
    imports are NOT needed by this function.

Authenticity (2026-07-29, Python 3.9.25): calc_check_digit('12345678')
= 'Z', calc_check_digit('0') = 'T' computed against this file AND
against the unpacked python_stdnum-2.2 sdist package -- both agree.
"""

from __future__ import annotations

def calc_check_digit(number: str) -> str:
    """Calculate the check digit. The number passed should not have the
    check digit included."""
    return 'TRWAGMYFPDXBNJZSQVHLCKE'[int(number) % 23]
