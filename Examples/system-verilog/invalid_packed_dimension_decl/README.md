# Invalid packed-dimension declarations

The extractor lowers declaration-only integral variables whose packed dimension is rejected during elaboration (`bit [3:x]` and `bit [3]`) to `Empty`. The compiler rejects these declarations before simulation, so they do not create runtime state. Ordinary 2-state declarations and expressions involving an invalid declaration remain loud.
