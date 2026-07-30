"""ISO 7064 Mod 97, 10 (python-stdnum; the IBAN check-digit algorithm),
vendored verbatim for the Lean verification benchmark (Band B).

Provenance:
  package : python-stdnum, https://pypi.org/project/python-stdnum/
  version : 2.2 (pip download --no-deps python-stdnum, 2026-07-21; sdist
            python_stdnum-2.2.tar.gz, sha256
            e95fcfa858a703d4a40130cb3eaac133c60d8808a7f3c98efeedac968c2479b9)
  file    : stdnum/iso7064/mod_97_10.py, sha256
            ffd72642a9e1a80adfc0d13ba10a827152567be0f166b117cef7da286a58ed3c
  license : LGPL-2.1-or-later. The functions below are Copyright (C)
            2010-2021 Arthur de Jong, licensed under the GNU Lesser
            General Public License version 2.1 or later.

Vendoring rules (python benchmark, Examples/python/bench_iso7064_mod_97_10):
  * _to_base10, checksum, calc_check_digits, validate and is_valid are
    BYTE-VERBATIM copies of stdnum/iso7064/mod_97_10.py 2.2 lines 42-45,
    48-50, 53-56, 59-67 and 70-75 (sha256 of the five segments:
    6c392527be73b14509e8cdda33610d2531e563b41499d6581d27427f70d84ceb
    ea4ca99c54b435110c7d4ca0ee013d4e6447edcb425d5b081dd42eb01315f6fe
    be20b1bfdd1f489adf01cb9ef164b060b09135cb7857e20ca596f15beee045f1
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
  * Note for the census: _to_base10 calls int(x, 36) -- a TWO-argument
    int call (base-36 digit value) -- and calc_check_digits uses
    printf-style '%02d' % ... string formatting.

Authenticity (2026-07-29, Python 3.9.25):
checksum('9999123456789012141490') = 1,
calc_check_digits('99991234567890121414') = '90',
validate('08686001256515001121751') = '08686001256515001121751'
computed against this file AND against the unpacked python_stdnum-2.2
sdist package -- both agree.
"""

from __future__ import annotations

def _to_base10(number: str) -> str:
    """Prepare the number to its base10 representation."""
    return ''.join(
        str(int(x, 36)) for x in number)

def checksum(number: str) -> int:
    """Calculate the checksum. A valid number should have a checksum of 1."""
    return int(_to_base10(number)) % 97

def calc_check_digits(number: str) -> str:
    """Calculate the extra digits that should be appended to the number to
    make it a valid number."""
    return '%02d' % (98 - checksum(number + '00'))

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
