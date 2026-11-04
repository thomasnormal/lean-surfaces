// SPDX-License-Identifier: Apache-2.0
// WP-PROC N2: nets with exactly one continuous driver on every bit are variables: a declaration assignment (`wire t =
// e;` is `assign t = e;`), a whole-net assign, literal windows that tile an `output wire`, an implicit-type output, a
// scalar net, an implicit net, and a child output connected to a whole net. Verilog-2001 style (non-ANSI header).
module proc_net_child (i, o);
  input [3:0] i;
  output [3:0] o;
  assign o = ~i;
endmodule

module proc_net (a, b, s, y, z, w, q);
  input [7:0] a, b;
  input s;
  output [7:0] y;
  output wire [7:0] z;
  output w;
  output [3:0] q;
  wire [7:0] t = a ^ b;
  wire [7:0] u;
  wire [3:0] lo, hi;
  wire v;
  wire [3:0] c;
  assign u = t & a;
  assign lo = u[3:0] | b[3:0];
  assign hi = u[7:4];
  assign y = {hi ^ lo, lo};
  assign z[3:0] = t[3:0];
  assign z[7:4] = u[7:4] ^ hi;
  assign v = s & a[0];
  assign implicit_n = a[1];
  assign w = v ^ b[0] ^ implicit_n;
  proc_net_child ch (.i(a[3:0]), .o(c));
  assign q = c ^ lo;
endmodule
