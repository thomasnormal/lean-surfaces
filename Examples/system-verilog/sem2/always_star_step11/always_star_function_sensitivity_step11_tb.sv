`timescale 1ns/1ps
module always_star_function_sensitivity_step11_tb;
    logic [3:0] a = 4'b0011, hidden = 4'b0101;
    wire [3:0] y_star, y_comb;
    always_star_function_sensitivity_step11 dut (.*);
    task automatic show(input string label);
        $display("ROW %s %b %b", label, y_star, y_comb);
    endtask
    task automatic row(input string label, input logic [3:0] av, hv);
        a = av; hidden = hv;
        #1 show(label);
    endtask
    initial begin
        #1 show("first");
        row("hidden_only", 4'b0011, 4'b1001);
        row("argument", 4'b1010, 4'b1001);
        row("hidden_known", 4'b1010, 4'b0011);
        row("hidden_xz", 4'b1010, 4'bxz01);
        row("argument_after_xz", 4'b0011, 4'bxz01);
        row("hidden_z", 4'b0011, 4'bzzzz);
        row("argument_after_z", 4'b1111, 4'bzzzz);
        row("hidden_zero", 4'b1111, 4'b0000);
        row("argument_zero", 4'b0000, 4'b0000);
        row("argument_xz", 4'bxz01, 4'b0000);
        row("argument_z", 4'bzzzz, 4'b0000);
        $finish;
    end
endmodule
