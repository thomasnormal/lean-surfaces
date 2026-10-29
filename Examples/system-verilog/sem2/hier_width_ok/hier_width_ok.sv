// The part of `hier_width` that stays admitted (round 6, 2026-10-29): port-width
// coercion, a port connection is a continuous assignment, so a narrower source is
// zero-extended and a wider one truncated, in both directions. In `hier_width`
// instance u4 connects the BARE NET `s` (2 bits) to a NET formal of N + 2 bits; the
// tools split on that (IEEE 1800-2023 23.3.3 / 10.7 zero-extend, and so do Icarus
// 12.0, Verilator, Yosys and slang, but Xcelium 24.03-s004 binds the nets bit for
// bit and leaves the formal's high bits z, docs/sv-xcelium-audit.md H1), so
// `hier_width` is the loud-refusal row family `PortConn:net-width`. Here u4 is fed
// by a VARIABLE copy of `s`, which every tool, Xcelium included, zero-extends, and
// u1, u2, u3 and u5 are unchanged: rows `hier_width_ok*`.
module hw_pass #(parameter int W = 4) (
  input  logic [W-1:0] i,
  output logic [W-1:0] o
);
  assign o = ~i;
endmodule

module hier_width_ok #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [1:0]   s,
  output logic [N+1:0] out_wide,
  output logic [1:0]   out_narrow,
  output logic [N-1:0] in_wide,
  output logic [N+1:0] in_narrow,
  output logic [N-1:0] in_safe
);
  logic [1:0] sv;
  assign sv = s;
  hw_pass #(.W(N))     u1 (.i(a), .o(out_wide));
  hw_pass #(.W(N))     u2 (.i(a), .o(out_narrow));
  hw_pass #(.W(N - 1)) u3 (.i(a), .o(in_wide[N-2:0]));
  hw_pass #(.W(N + 2)) u4 (.i(sv), .o(in_narrow));
  hw_pass #(.W(N))     u5 (.i(s ^ 2'b10), .o(in_safe));
  assign in_wide[N-1] = 1'b0;
endmodule
