module toggle (input logic clk, rst, en, output logic q);
  always_ff @(posedge clk)
    if (rst) q <= 1'b0;
    else if (en) q <= ~q;
endmodule
