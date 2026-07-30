"""CPython string.capwords, vendored verbatim for the Lean verification
benchmark (Band C marker: string-method-heavy code).

Provenance:
  package : CPython standard library, module `string`
  version : Python 3.9.25 (system interpreter of this repo's toolchain)
  file    : /usr/lib64/python3.9/string.py, sha256
            bc57c407a8397ee2bea8683d0ce0a563a060c74c785ff36fc6555d66a9c7a566
  license : PSF License Agreement for Python 3.9.25 (PSF-2.0);
            Copyright (c) 2001-2026 Python Software Foundation.

Vendoring rules (python benchmark, Examples/python/bench_capwords):
  * capwords is a BYTE-VERBATIM copy of string.py 3.9.25 lines 37-48
    (segment sha256:
    252e953a3938ee925d42468c8c8a74b544474bd5267e3d18e1bc6273e1d01616). Do NOT edit its body.
  * Nothing else of string.py is vendored; capwords references only its
    parameters and the str methods join/split/capitalize.

Authenticity (2026-07-29, Python 3.9.25): capwords('  aBc  dEf ') =
'Abc Def', capwords('x-y z', '-') = 'X-Y z' computed against this file
AND against the installed `string` module -- both agree.
"""

def capwords(s, sep=None):
    """capwords(s [,sep]) -> string

    Split the argument into words using split, capitalize each
    word using capitalize, and join the capitalized words using
    join.  If the optional second argument sep is absent or None,
    runs of whitespace characters are replaced by a single space
    and leading and trailing whitespace are removed, otherwise
    sep is used to split and join the words.

    """
    return (sep or ' ').join(x.capitalize() for x in s.split(sep))
