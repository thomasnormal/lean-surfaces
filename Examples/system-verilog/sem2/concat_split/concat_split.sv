// Concatenated continuous-assignment targets mixing constant part-selects, a
// constant bit-select and whole signals: two windows of one signal in one
// target, a rotation, zero-extension of a narrower RHS, and truncation of a
// wider one. Each target's leaves receive the RHS (resized to the target's
// total width) MSB-first.
module concat_split (
  input  logic [4:0] x,
  input  logic [2:0] r,
  output logic [3:0] y,
  output logic       z,
  output logic [3:0] w,
  output logic [1:0] p, q,
  output logic       u,
  output logic [1:0] v
);
  assign {y[3:2], z, y[1:0]} = x;
  assign {w[0], w[3:1]} = x[3:0];
  assign {p, q} = r;
  assign {u, v} = x;
endmodule
