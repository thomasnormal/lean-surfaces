// A retained loop iterator must not capture a same-named module localparam in a function.
module loop_name_capture_refuse #(
  parameter int N = 4
) (
  input  logic [7:0] d,
  output logic [7:0] q
);
  localparam int K = 1;
  function automatic logic f(input logic x);
    f = (K == 1);
  endfunction
  always_comb begin
    q = 8'h00;
    for (int K = 0; K < N; K++)
      q[K] = f(1'b0);
  end
endmodule
