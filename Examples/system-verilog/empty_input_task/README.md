# Empty input-only task calls

An empty task with input-only formals has no body, scheduler, diagnostic, or
copy-out effect. The legacy self-check extractor evaluates each actual through
the pure expression boundary and erases the call. Effectful actuals and
output/inout/ref or defaulted formals remain loud.
