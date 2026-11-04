# Direct whole-net aliases

The legacy self-check tier admits a direct `alias left = right` declaration
when both references are module-scope integral nets with the same width and
four-state status. The two spellings use one flat storage cell, so a constant
driver through `left` is visible through `right`. Selected, concatenated,
non-net, and mismatched aliases remain loud.
