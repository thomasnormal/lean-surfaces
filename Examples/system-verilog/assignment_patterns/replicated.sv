module top;
  localparam int N = 4;
  logic [7:0] repeated = '{N{1'b1, 1'b0}};
  logic [7:0] unknowns = '{2{1'bx, 1'bz, 1'b0, 1'b1}};
  initial begin
    $display("repeated %b %b", repeated, unknowns);
    $finish;
  end
endmodule
