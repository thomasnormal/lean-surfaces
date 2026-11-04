// A run-time index read from a finite unpacked input array.
module unpacked_dynamic_read (
  input logic [2:0] index,
  input logic [7:0] a [0:3],
  output logic [7:0] y
);
  always_comb y = a[index];
endmodule
