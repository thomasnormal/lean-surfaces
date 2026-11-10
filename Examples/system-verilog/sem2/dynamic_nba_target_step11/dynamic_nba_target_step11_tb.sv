`timescale 1ns/1ps

module dynamic_nba_target_step11_tb;
    logic clk = 1'b0;
    logic [2:0] idx;
    logic d;
    logic en;
    logic [3:0] q;

    dynamic_nba_target_step11 dut (.*);

    always #5 clk = ~clk;

    task automatic row(input logic [8*24-1:0] name,
                       input logic [2:0] i,
                       input logic value,
                       input logic enable);
        begin
            @(negedge clk);
            idx = i;
            d = value;
            en = enable;
            @(posedge clk);
            #1 $display("ROW %0s q=%b", name, q);
        end
    endtask

    initial begin
        idx = 3'bxxx;
        d = 1'bx;
        en = 1'bx;
        #1 $display("ROW first q=%b", q);
        row("nba_idx_0_d1", 3'b000, 1'b1, 1'b1);
        row("nba_idx_3_d0", 3'b011, 1'b0, 1'b1);
        row("nba_idx_x_d1", 3'bx0x, 1'b1, 1'b1);
        row("nba_idx_z_d0", 3'bz01, 1'b0, 1'b1);
        row("nba_idx_4_d1", 3'b100, 1'b1, 1'b1);
        row("nba_idx_1_disabled", 3'b001, 1'b0, 1'b0);
        $finish;
    end
endmodule
