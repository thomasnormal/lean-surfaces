// Automatic block-local storage remains a retained loud boundary.
module proc_local_automatic (
  input logic clk,
  input logic [7:0] a,
  output logic [7:0] y
);
  always_ff @(posedge clk) begin
    automatic logic [7:0] t;
    t = a;
    y <= t;
  end
endmodule
