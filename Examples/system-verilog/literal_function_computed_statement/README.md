# Literal-return function with a pure computed argument

A discarded call to a source-declared literal-return function is admitted when
its input arguments are compile-time pure integral expressions. The function
body ignores the inputs and returns a literal, so the call has no represented
state or scheduler effect. Dynamic, effectful, named-state, copy-out, and
unsupported arguments remain loud.
