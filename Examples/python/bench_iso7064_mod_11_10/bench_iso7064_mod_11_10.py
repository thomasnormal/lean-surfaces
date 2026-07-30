"""ISO 7064 Mod 11, 10 (python-stdnum), vendored verbatim for the Lean
verification benchmark (Band B: fold-mod checksum arithmetic).

Provenance:
  package : python-stdnum, https://pypi.org/project/python-stdnum/
  version : 2.2 (pip download --no-deps python-stdnum, 2026-07-21; sdist
            python_stdnum-2.2.tar.gz, sha256
            e95fcfa858a703d4a40130cb3eaac133c60d8808a7f3c98efeedac968c2479b9)
  file    : stdnum/iso7064/mod_11_10.py, sha256
            9b87a6c1b1a2606e74ea4aded7824f2306e645d267bc18a462737b531091bac7
  license : LGPL-2.1-or-later. The functions below are Copyright (C)
            2010-2021 Arthur de Jong, licensed under the GNU Lesser
            General Public License version 2.1 or later.

Vendoring rules (python benchmark, Examples/python/bench_iso7064_mod_11_10):
  * checksum, calc_check_digit, validate and is_valid are BYTE-VERBATIM
    copies of stdnum/iso7064/mod_11_10.py 2.2 lines 43-48, 51-54, 57-65
    and 68-73 (sha256 of the four segments:
    90eb9bfa088fa47432b734477ef6a4c72048cb2cde2faf70ce912de4264018f5
    41c1799de054685728fd94c5b65f3d881d552088d642e987d88841308e3395ba
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

Authenticity (2026-07-29, Python 3.9.25): checksum('794623') = 1,
calc_check_digit('79462') = '3', validate('794623') = '794623',
is_valid('794623') = True computed against this file AND against the
unpacked python_stdnum-2.2 sdist package -- both agree.
"""

from __future__ import annotations

def checksum(number: str) -> int:
    """Calculate the checksum. A valid number should have a checksum of 1."""
    check = 5
    for n in number:
        check = (((check or 10) * 2) % 11 + int(n)) % 10
    return check

def calc_check_digit(number: str) -> str:
    """Calculate the extra digit that should be appended to the number to
    make it a valid number."""
    return str((1 - ((checksum(number) or 10) * 2) % 11) % 10)

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
