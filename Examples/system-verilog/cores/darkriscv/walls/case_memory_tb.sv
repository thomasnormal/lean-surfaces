`timescale 1ns/1ns
module case_memory_tb;
  logic clk;
  logic [1:0] sel;
  logic [7:0] d;
  logic [7:0] q;
  dark_case_memory dut(.clk(clk), .sel(sel), .d(d), .q(q));
  task automatic cycle(input logic [1:0] sv, input logic [7:0] dv);
    begin
      sel = sv; d = dv; #1; clk = 1; #1;
      $display("ROW sel=%0d q=%h mem=%h", sel, q, dut.mem[0]);
      clk = 0; #1;
    end
  endtask
  initial begin
    clk = 0; sel = 0; d = 0;
    #1;
    $display("ROW sel=%0d q=%h mem=%h", sel, q, dut.mem[0]);
    cycle(2'd0, 8'h3C);
    cycle(2'd1, 8'h00);
    cycle(2'd2, 8'h00);
    cycle(2'd3, 8'h00);
    $finish;
  end
endmodule
