# Zero-size dynamic-array declarations

`dynamic_array_empty_decl.sv` checks the declaration-only boundary for
`new[0]` and empty assignment-pattern initializers.  Both forms create an
empty dynamic array, so the self-check envelope carries no declaration cells;
nonzero allocations remain represented by their flattened cells.
