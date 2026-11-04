# Source-pure string query initializers

A local string declaration can be initialized directly from a source-pure
ASCII query. This fixture checks case conversion, `substr`, and `$sformatf`
initializers through exact comparisons; dynamic string initializers remain loud.
