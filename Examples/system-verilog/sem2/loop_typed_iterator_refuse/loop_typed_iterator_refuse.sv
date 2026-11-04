// Narrow typed iterators wrap at their declared width and are not int loops.
module loop_typed_iterator_refuse #(
  parameter int N = 4
) (
  input  logic [7:0] d,
  output logic [7:0] q
);
  always_comb begin
    q = 8'h00;
    for (byte i = 100; i < N + 124; i += 30)
      q[0] = d[0];
  end
endmodule
