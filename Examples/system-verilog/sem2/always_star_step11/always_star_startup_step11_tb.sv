`timescale 1ns/1ps
module always_star_startup_step11_tb;
    wire [3:0] y_star, y_comb, y_constant_star, y_constant_comb;
    always_star_startup_step11 dut (.*);
    task automatic show(input string label);
        $display("ROW %s %b %b %b %b", label, y_star, y_comb,
                 y_constant_star, y_constant_comb);
    endtask
    initial begin
        #1 show("first");
        dut.a = 4'b1010; #1 show("a_known");
        dut.b = 4'b1001; #1 show("b_known");
        dut.a = 4'bxz01; #1 show("a_xz");
        dut.b = 4'bzzzz; #1 show("b_z");
        $finish;
    end
endmodule
