// Round 6 (H1 control, lane A, 2026-10-29): the narrower-actual shapes that
// every tool, Xcelium included, zero-extends, so `PortConn:net-width` must
// NOT fire: a VARIABLE actual (`sv`, assign-driven `logic`) and an
// expression ({s}, a concatenation) into a net formal. Compare net_width_min.
module nw_child (
  input  logic [5:0] i,
  output logic [5:0] p
);
  assign p = i;
endmodule

module net_width_ok (
  input  logic [1:0] s,
  output logic [5:0] pv,
  output logic [5:0] pe
);
  logic [1:0] sv;
  assign sv = s;
  nw_child uv (.i(sv), .p(pv));
  nw_child ue (.i({s}), .p(pe));
endmodule
