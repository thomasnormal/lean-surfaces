# String null-character assignment

IEEE 1800-2023 §6.16 forbids the special character `\0` in a string. A
blocking assignment of the integral value zero to a selected string byte is
ignored. The legacy self-check envelope erases this exact no-op after checking
for a constant index and literal zero; dynamic, nonzero, timed, and
nonblocking writes remain loud.
