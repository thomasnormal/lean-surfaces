"""Pass 0 plain-import slice: an absent module raises before binding."""

print("before")
import zzz_no_such_module
print("unreached")
