# Literal format-string concatenation

The self-check tier accepts a `$display` format made from a concatenation of
string literals. The extractor folds only those source-pure pieces into the
existing `SysCall.format` field; a concatenation containing a string variable
remains loud.
