# Exact `int` constants at every parameter point

SystemVerilog `int` and `integer` constants are signed 32-bit values (§6.11,
§11.8.1). The semantic family `X.sem N` must therefore use the exact 32-bit
binding at every parameter point, not only at the envelope's default point.
`PDesign.int32Agrees` remains a diagnostic for the unbounded proof-facing
constant path; it cannot be the semantic guard because it is currently run
only while loading defaults.

The implementation will keep one source-shaped `PDesign` and one evaluator.
`instantiate2From` will expose the existing `IEnv.int32` choice through an
exact semantic entry point used by `instantiateGD2`/`sem`. The unbounded path
remains available for symbolic proofs and is accepted only when its result is
proved equal to the exact path at that point. A mismatch is a loud
`Unsupported` result at the point, with the existing `int32Agrees` comparison
used as the executable witness; no parameter-point is silently assigned the
unbounded branch.

The invariant is pointwise: for every argument list, every `int` parameter and
`int` localparam is represented in `nvals` with `(32, signed)`, every
constant-context operation wraps according to that type, and generate guards
read the same bindings and arithmetic. Typed non-`int` parameters continue to
use their declared width and signedness. No fuel or new AST constructor is
introduced.

The clean-room `add_int32` fixture is the regression witness. At `N = 5`,
`M = (N == 5) ? 1073741824 * 2 : 1` is `-2^31`, so the `else` generate arm is
the exact design. The unbounded path selects the other arm; the semantic family
must refuse the unbounded mismatch or evaluate the exact arm. The acceptance
checks cover the default `N = 16` and the non-default `N = 5` point.
