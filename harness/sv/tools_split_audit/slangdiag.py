#!/usr/bin/env python3.12
"""slangdiag.py [slang options] FILE.sv ... : run the REAL slang driver pipeline (parse, elaborate,
ANALYSIS) via pyslang.driver.Driver, the same as the `slang` CLI, with colours off.
Prints the diagnostics and a final line  `slang: ERRORS=<n>` / `slang: CLEAN` plus the warning count.
Pass `-Weverything` as an option to see optional warnings too."""
import sys, io, os
import pyslang
from pyslang.driver import Driver
d = Driver()
d.addStandardArgs()
d.setTerminalColorsEnabled(False)
args = "slang " + " ".join(sys.argv[1:])
ok = d.parseCommandLine(args)
if not ok:
    print("slang: BAD COMMAND LINE"); sys.exit(2)
if not d.processOptions():
    print("slang: PROCESSOPTIONS FAILED"); sys.exit(2)
if not d.parseAllSources():
    print('slang: PARSE FAILED'); sys.exit(2)
ok = d.runFullCompilation(quiet=False)
print("slang: " + ("CLEAN-OR-WARNINGS (no errors)" if ok else "ERRORS"))
sys.exit(0 if ok else 1)
