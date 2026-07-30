"""ISO 7064 Mod 11, 2 (python-stdnum; ISBN-10/ISNI check digits), vendored
verbatim for the Lean verification benchmark (Band B).

Provenance:
  package : python-stdnum, https://pypi.org/project/python-stdnum/
  version : 2.2 (pip download --no-deps python-stdnum, 2026-07-21; sdist
            python_stdnum-2.2.tar.gz, sha256
            e95fcfa858a703d4a40130cb3eaac133c60d8808a7f3c98efeedac968c2479b9)
  file    : stdnum/iso7064/mod_11_2.py, sha256
            e23a4687a2843d0b179d7b77cc793aef30c64e32e9a6a4e9b76af6f10d0111a6
  license : LGPL-2.1-or-later. The functions below are Copyright (C)
            2010-2021 Arthur de Jong, licensed under the GNU Lesser
            General Public License version 2.1 or later.

Vendoring rules (python benchmark, Examples/python/bench_iso7064_mod_11_2):
  * checksum, calc_check_digit, validate and is_valid are BYTE-VERBATIM
    copies of stdnum/iso7064/mod_11_2.py 2.2 lines 45-50, 53-57, 60-68
    and 71-76 (sha256 of the four segments:
    d843be0ca41e12587cc19a621bf29fb906c93f1a9012749458cb391a24ea1f21
    5961cbd8dafd79125b0c2084df632885991bf1f4862e70a93671e74faedfc9ac
    f4b7e23000224dd547f90c1b2ffc4f6e8152b61a43e9728b17a6bf8d89b21fb2
    caac6b41c319417341fa9e5a72b916fe145751ab42ec48800455c28712be8742). Do NOT edit their bodies.
  * The stdnum exception classes (InvalidFormat, InvalidChecksum,
    ValidationError; from `from stdnum.exceptions import *`) are NOT
    vendored: each occurs only inside a raise statement or an except
    clause, i.e. on invalid-input or error paths -- no valid-input run
    evaluates the names (same rule as Examples/python/rsa_inverse and its
    NotRelativePrimeError).
  * `from __future__ import annotations` IS retained from the original
    module (its own line-range segment below): it makes the `str`/`int`
    parameter annotations lazy at def time, exactly as in the original.

Authenticity (2026-07-29, Python 3.9.25): checksum('079X') = 1,
calc_check_digit('079') = 'X', calc_check_digit('0794') = '0',
validate('07940') = '07940' computed against this file AND against the
unpacked python_stdnum-2.2 sdist package -- both agree.
"""

from __future__ import annotations

def checksum(number: str) -> int:
    """Calculate the checksum. A valid number should have a checksum of 1."""
    check = 0
    for n in number:
        check = (2 * check + int(10 if n == 'X' else n)) % 11
    return check

def calc_check_digit(number: str) -> str:
    """Calculate the extra digit that should be appended to the number to
    make it a valid number."""
    c = (1 - 2 * checksum(number)) % 11
    return 'X' if c == 10 else str(c)

def validate(number: str) -> str:
    """Check whether the check digit is valid."""
    try:
        valid = checksum(number) == 1
    except Exception:  # noqa: B902
        raise InvalidFormat()
    if not valid:
        raise InvalidChecksum()
    return number

def is_valid(number: str) -> bool:
    """Check whether the check digit is valid."""
    try:
        return bool(validate(number))
    except ValidationError:
        return False
