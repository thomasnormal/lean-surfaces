# fdivp loader walls

This clean-room packet records the three first walls measured on the
parametric floating-point-divider shape reported by the svGolf lead.  The
sources are intentionally small reproductions; the upstream design is not
rewritten here.

`fdivp_sized_localparam.sv` has a sized value localparam whose initializer is
an integer expression and whose width is symbolic.  The extractor retains the
envelope, but `load_design_sv2` refuses it with
`localparam 'KOV': unsupported node 'ConversionExpression:width' in a constant
context`.

`fdivp_generate_localdecl.sv` has a generate-local `localparam` and two local
variables in each generate scope.  Instantiation succeeds, while each
generated declaration and the assignments that target those undeclared local
names remain named `Process2.unsupported` nodes (`GenerateDecl:LocalParam`,
`GenerateDecl:Var`, and `Assign`).  The source rows still produce `00` and
`a5` for zero and pattern inputs.

`fdivp_large_pow.sv` has `2**W` in a constant context with `W=8193`.  The
current 32-bit constant evaluator instantiates it and produces a zero-valued
8-bit output; both simulators produce the same row.  This is recorded as the
current result, not as an unbounded-precision interpretation.  At `W=31`, the
planner's boundary still requires exact IEEE 32-bit `int` behavior; an
unbounded constant tier must refuse or model that boundary rather than claim
the two circuits are identical.

`check.py` regenerates all three envelopes byte-for-byte, checks the exact
sized-localparam loader refusal and generated-process nodes in Lean, and
compares source rows against Icarus Verilog 13.0 and readiness-gated Xcelium
24.03-s004.
