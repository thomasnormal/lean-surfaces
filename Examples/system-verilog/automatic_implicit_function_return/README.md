# Automatic implicit function return values

An automatic function may assign a pure literal to its implicit scalar return
variable. The narrow static lowering materializes that literal at value call
sites and erases discarded calls; functions with reads, effects, or output
formals remain loud.
