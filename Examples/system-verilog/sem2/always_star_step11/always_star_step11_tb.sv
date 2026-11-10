`timescale 1ns/1ps
module always_star_step11_tb;
    // TB variable initialization precedes process startup (§6.8). Connected
    // input-port propagation still gives the recorded simulator startup split.
    logic [3:0] a = 4'b0011, b = 4'b0101;
    logic [1:0] sel = 2'b00;
    wire [3:0] y_star, y_comb;
    always_star_step11 dut (.*);
    task automatic show(input string label);
        $display("ROW %s %b %b", label, y_star, y_comb);
    endtask
    task automatic row(input string label, input logic [3:0] av, bv,
                       input logic [1:0] sv);
        a = av; b = bv; sel = sv;
        #1 show(label);
    endtask
    initial begin
        #1 show("first");
        // b is read by another branch, so its change also wakes @*.
        row("unselected_b", 4'b0011, 4'b1001, 2'b00);
        row("a_known", 4'b1010, 4'b1001, 2'b00);
        row("b_known", 4'b1010, 4'b0101, 2'b01);
        row("selector_x_label", 4'b1010, 4'b0101, 2'b1x);
        row("selector_z_label", 4'b1010, 4'b0101, 2'b1z);
        row("selector_x_default", 4'b1010, 4'b0101, 2'b0x);
        row("known_default", 4'b1010, 4'b0101, 2'b11);
        row("a_xz", 4'bxz01, 4'b0011, 2'b00);
        row("b_z", 4'b0011, 4'bzzzz, 2'b01);
        row("xor_xz", 4'bxz01, 4'b1010, 2'b1x);
        row("not_z", 4'bzzzz, 4'bxx00, 2'b1z);
        $finish;
    end
endmodule
