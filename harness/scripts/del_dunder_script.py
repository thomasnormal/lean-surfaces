# del of a module dunder: CPython's removal UNCOVERS the builtins
# module's own __name__ (this prints 'builtins'!) -- the model resolves
# dunder reads statically, so it refuses LOUDLY rather than answer
# either way.
del __name__
print(__name__)
