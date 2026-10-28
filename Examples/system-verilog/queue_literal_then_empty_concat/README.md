# Literal queue write followed by empty concatenation

This fixture covers a source-pure queue history in which a literal queue write
is immediately replaced by an empty queue concatenation. The earlier opaque
write has no observable effect, and the final `.size()` is exactly zero.
