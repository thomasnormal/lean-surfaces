# Implicit function return values

SystemVerilog permits an untyped function to use its implicit scalar return
variable, and an explicitly typed function may assign its implicit return
variable instead of using `return`. Pure literal bodies are lowered at the call
site; functions with reads, effects, or output formals remain loud.
