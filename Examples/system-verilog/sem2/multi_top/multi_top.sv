// Two top-level modules in one source set (2026-10-28, round 3 CX repair;
// CX verifier repro). slang applies `paramOverrides` to EVERY top-level
// module, so a probe at N = 8 also elaborated the unrelated `side_mod` at
// N = 8, hit its `$error`, and refused the DUT, which is correct at N = 8
// under every tool (a testbench's `#(.N(8))` overrides `multi_top` alone).
// The probe compilation now elaborates the `--top` module alone.
module multi_top #(
  parameter int N = 4
) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  assign y = ~a;
endmodule

module side_mod #(
  parameter int N = 4
) (
  input  logic [3:0] b,
  output logic [3:0] z
);
  if (N > 6) begin : bad
    $error("side_mod: N too large");
  end
  assign z = b;
endmodule
