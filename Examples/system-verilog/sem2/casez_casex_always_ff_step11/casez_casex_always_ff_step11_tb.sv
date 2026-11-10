`timescale 1ns/1ps

module casez_casex_always_ff_step11_tb;
    logic clk = 1'b0;
    logic [3:0] sel;
    logic [3:0] d;
    logic [3:0] qz;
    logic [3:0] qx;

    casez_casex_always_ff_step11 dut (.*);

    always #5 clk = ~clk;

    task automatic row(input logic [8*24-1:0] name,
                       input logic [3:0] s,
                       input logic [3:0] value);
        begin
            @(negedge clk);
            sel = s;
            d = value;
            @(posedge clk);
            #1 $display("ROW %0s qz=%b qx=%b", name, qz, qx);
        end
    endtask

    initial begin
        sel = 4'bxxxx;
        d = 4'bxxxx;
        #1 $display("ROW first qz=%b qx=%b", qz, qx);
        row("sel_0000_d9", 4'b0000, 4'b1001);
        row("sel_0001_d8", 4'b0001, 4'b1000);
        row("sel_00z1_d7", 4'b00z1, 4'b0111);
        row("sel_01xz_d6", 4'b01xz, 4'b0110);
        row("sel_1x00_d5", 4'b1x00, 4'b0101);
        row("sel_1z11_d4", 4'b1z11, 4'b0100);
        row("sel_zzzz_d3", 4'bzzzz, 4'b0011);
        row("sel_xxxx_d2", 4'bxxxx, 4'b0010);
        $finish;
    end
endmodule
