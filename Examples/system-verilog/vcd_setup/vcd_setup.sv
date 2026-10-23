/*
:name: vcd_setup
:description: IEEE 1800-2023 Sections 21.6-21.7 -- VCD setup does not alter
  the self-check observable output.
:tags: 21.6 21.7
:type: simulation
*/
module top;
  logic a;
  initial begin
    a = 1'b1;
    $dumpfile("vcd_setup.vcd");
    $dumpvars(0, top);
    $display("PASS");
    $finish;
  end
endmodule
