# Source-pure string case assignment

A blocking assignment from `string.toupper()` is admitted when the receiver's
history is a direct ASCII literal. The same source-history path also covers
`tolower()` and `substr()`; dynamic, timed, nonblocking, aliased, and non-ASCII
forms remain loud.
