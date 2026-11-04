// Genvar-constant selects in self-determined positions: a bit select of a
// genvar is one bit (IEEE 1800-2023 11.5.1), so `{i[0]}` is a 1-bit concat
// and `{8{i[0]}}` an 8-bit replication - inside gates and next to
// packed-array row parts.
module gvcat #(parameter int N = 4) (
  input  logic [N-1:0]   a,
  input  logic [4*N-1:0] src,
  output logic [N-1:0]   y,
  output logic [N-1:0]   z,
  output logic [4*N-1:0] o_flat
);
  logic [N-1:0][3:0] m;
  logic [N-1:0][3:0] o;
  assign m = src;
  genvar i;
  for (i = 0; i < N; i++) begin : g
    assign y[i] = a[i] ^ {i[0]};
    assign z[i] = a[i] & ^{{2{i[0]}}, i[1]};
  end
  for (i = 0; i < N/2; i++) begin : h
    assign o[2*i +: 2] = m[2*i+1 -: 2] ^ {8{i[0]}};
  end
  assign o_flat = o;
endmodule
