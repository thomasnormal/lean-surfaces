`timescale 1ns/1ps

module plain_always_posedge_step11_tb;
    logic clk = 1'b0;
    logic en;
    logic [3:0] d;
    logic [3:0] q;
    logic [3:0] q_copy;

    plain_always_posedge_step11 dut (.*);

    always #5 clk = ~clk;

    task automatic row(input logic [8*24-1:0] name,
                       input logic enable,
                       input logic [3:0] value);
        begin
            @(negedge clk);
            en = enable;
            d = value;
            @(posedge clk);
            #1 $display("ROW %0s q=%b q_copy=%b", name, q, q_copy);
        end
    endtask

    initial begin
        en = 1'bx;
        d = 4'bxxxx;
        #1 $display("ROW first q=%b q_copy=%b", q, q_copy);
        row("en0_d9", 1'b0, 4'b1001);
        row("en1_d6", 1'b1, 4'b0110);
        row("enx_d3", 1'bx, 4'b0011);
        row("enz_dz", 1'bz, 4'bzzzz);
        row("en1_dxz", 1'b1, 4'bxz01);
        $finish;
    end
endmodule
