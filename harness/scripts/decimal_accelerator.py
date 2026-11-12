"""The decimal module's public surface is supplied by the C accelerator.

CPython 3.9's ``decimal.py`` is only a guarded ``from _decimal import *``
wrapper.  The model therefore refuses the import rather than pretending that
the accelerator and a missing pure-Python implementation are equivalent.
This row prices that wall: there are no manifest functions defined by the
Python file to flip.
"""

from _decimal import *

print(Decimal(1))
