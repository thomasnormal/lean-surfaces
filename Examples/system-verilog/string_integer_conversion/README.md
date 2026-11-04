# Literal string integer conversion

IEEE 1800-2023 §6.16.1 defines `itoa`, `bintoa`, `octtoa`, and `hextoa` as
source-pure replacements of a string with the unpadded ASCII rendering of a
literal integral argument. The self-check extractor replays those replacements
through opaque string history, preserving decimal, binary, octal, and
lower-case hexadecimal output. Dynamic arguments, control-dependent calls,
unknown values, aliases, and unsupported signatures remain loud.
