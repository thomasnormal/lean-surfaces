module fdivp_sized_localparam_tb;
  logic [7:0] a8;
  logic [3:0] y8;
  logic [9:0] a10;
  logic [3:0] y10;
  fdivp_sized_localparam #(.W(8), .OFF(0)) d8(.a(a8), .y(y8));
  fdivp_sized_localparam #(.W(10), .OFF(3)) d10(.a(a10), .y(y10));
  initial begin
    a8 = 0; a10 = 0;
    #1 $display("ROW default y=%h", y8);
    #1 $display("ROW override y=%h", y10);
    $finish;
  end
endmodule
