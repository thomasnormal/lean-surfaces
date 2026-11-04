// WP-G four-state contract: else-if chain (an x/z first condition falls to the second test), nested if/else, default then override (no latch), two targets under one if, and the value of the TAKEN arm only (x/z in the untaken arm never reaches the target; in the taken arm it does, z included). Pinned against Xcelium 24.03.
module wpg_if_chain (
  input  logic c1,
  input  logic c2,
  input  logic a,
  input  logic b,
  input  logic d,
  input  logic e,
  output logic y,
  output logic z,
  output logic w,
  output logic u,
  output logic v
);
  always_comb begin if (c1) y = a; else if (c2) y = b; else y = d; end
  always_comb begin if (c1) begin if (c2) z = a; else z = b; end else z = d; end
  always_comb begin w = 1'b0; if (c1) w = a; end
  always_comb begin if (c1) begin u = a; v = b; end else begin u = b; v = a; end end
endmodule
