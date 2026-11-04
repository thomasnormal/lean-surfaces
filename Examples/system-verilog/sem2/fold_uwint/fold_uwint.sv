// Round 6 folds: the INT-class twin of `fold_uwid`. `localparam B = N + 1`
// with an `int N` is a 32-bit `int` to slang, the LRM and the Yosys 0.53
// netlist and 33 bits wide in Icarus 12.0 (lossless untyped width), which
// shows as a concatenation part (`{a, B}`: 0x1e00000009 against 0xf00000009
// at a = 4'hF, N = 8) and as a negative value zero-extended into a wider
// unsigned context (`a + C` with C = N - 9 = -1: 0x200000002 against
// 0x100000002 at a = 3); `E = 2 ** N` is 42 bits in Icarus at N = 40, where
// the 32-bit `int` wraps to 0 in Yosys. Refused at every point:
// Constant:untyped-width.
module fold_uwint #(parameter int N = 8) (
  input  logic [3:0] a,
  output logic [63:0] o1, o2, o3);
  localparam B = N + 1;
  localparam C = N - 9;
  localparam E = 2 ** N;
  assign o1 = {a, B};
  assign o2 = a + C;
  assign o3 = {a, E};
endmodule
