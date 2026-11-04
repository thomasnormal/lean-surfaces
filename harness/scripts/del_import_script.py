# del of a benign-import name: CPython exits 0 silently, but the model
# binds `time` STATICALLY (never in the frame's locals), so the removal
# has nothing to act on -- refused LOUDLY.
import time
del time
print(0)
