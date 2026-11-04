# Wrapped `$sformatf("%m")` string assignment

The legacy self-check extractor replays a blocking assignment from a literal
prefix and suffix around the metadata-only top-level `$sformatf("%m")` query.
Nested hierarchy, functions, generated scopes, and dynamic format forms remain
loud.
