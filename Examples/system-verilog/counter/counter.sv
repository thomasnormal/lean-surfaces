module counter (input  logic clk, rst,
                output logic [7:0] count);
  always_ff @(posedge clk)
    if (rst) count <= '0;
    else     count <= count + 8'd1;
endmodule
