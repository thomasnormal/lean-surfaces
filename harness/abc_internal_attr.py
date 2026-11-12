"""ABC-style internal attribute access stays outside the closed-function tier."""
def probe():
    return int._abc_invalidation_counter
