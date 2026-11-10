`timescale 1ns/1ps

module case_always_ff_step11_tb;
    logic clk = 1'b0;
    logic [1:0] sel;
    logic [3:0] d;
    logic [3:0] q;
    logic [3:0] q_default;

    case_always_ff_step11 dut (.*);

    always #5 clk = ~clk;

    task automatic row(input logic [8*24-1:0] name,
                       input logic [1:0] s,
                       input logic [3:0] v);
        begin
            @(negedge clk);
            sel = s;
            d = v;
            @(posedge clk);
            #1 $display("ROW %0s q=%b q_default=%b", name, q, q_default);
        end
    endtask

    initial begin
        sel = 2'bxx;
        d = 4'bxxxx;
        #1 $display("ROW first q=%b q_default=%b", q, q_default);
        row("case_00_d_xz01", 2'b00, 4'bxz01);
        row("case_01_d_zzzz", 2'b01, 4'bzzzz);
        row("case_1x_d_0000", 2'b1x, 4'b0000);
        row("case_1z_d_1111", 2'b1z, 4'b1111);
        row("case_z1_d_0001", 2'bz1, 4'b0001);
        row("case_x0_d_0000", 2'bx0, 4'b0000);
        row("case_zz_d_0000", 2'bzz, 4'b0000);
        $finish;
    end
endmodule
