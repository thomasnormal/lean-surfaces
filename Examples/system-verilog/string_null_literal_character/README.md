# NUL string-literal character assignment

IEEE 1800-2023 §6.16 treats assigning the one-byte NUL string literal to a
string character like assigning integral zero: the write is ignored. The
legacy self-check extractor erases this blocking no-op while retaining dynamic,
nonzero, timed, and nonblocking string-byte writes as loud targets.
