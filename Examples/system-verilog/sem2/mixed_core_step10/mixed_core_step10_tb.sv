`timescale 1ns/1ps

module mixed_core_step10_tb;
    logic clk = 1'b0;
    logic en;
    logic [3:0] d;
    logic [3:0] q;
    logic [3:0] n;
    logic [3:0] post;

    mixed_core_step10 dut (.*);
    always #5 clk = ~clk;

    task automatic row(input logic [8*24-1:0] name,
                       input logic enable,
                       input logic [3:0] value);
        begin
            @(negedge clk);
            en = enable;
            d = value;
            #1 $display("ROW %0s comb q=%b n=%b post=%b", name, q, n, post);
            @(posedge clk);
            #1 $display("ROW %0s edge q=%b n=%b post=%b", name, q, n, post);
        end
    endtask

    initial begin
        en = 1'b0;
        d = 4'b0000;
        #1 $display("ROW startup q=%b n=%b post=%b", q, n, post);
        row("en1_d3", 1'b1, 4'b0011);
        row("en0_da", 1'b0, 4'b1010);
        row("en1_x5", 1'b1, 4'bx101);
        row("en0_z0", 1'b0, 4'bz000);
        $finish;
    end
endmodule
