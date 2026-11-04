/* Clearing a virtual-interface handle has no represented self-check state. */
interface Bus;
  logic ready;
endinterface

module top;
  virtual Bus handle = null;
  initial begin
    handle = null;
    $display("PASS");
    $finish;
  end
endmodule
