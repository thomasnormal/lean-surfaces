// An N-bit adder/subtractor with a zero flag as ONE always_comb: an if/else
// picks the operation and the flag reads the result back. The hand-built
// twin `LeanModels.Sv.Comb2ProcExample.asDesign N` is proved correct and
// terminating for EVERY N (`as_correct`, `as_terminates`).
module addsub_comb #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  input  logic         sub,
  output logic [N-1:0] y,
  output logic         z
);
  always_comb begin
    if (sub) y = a - b;
    else y = a + b;
    z = ~|y;
  end
endmodule
