/* A null virtual-interface declaration is inert on the time-zero self-check path. */
interface SBus;
  logic req;
endinterface
module top;
  virtual SBus via_null = null;
  initial begin
    $display("PASS");
    $finish;
  end
endmodule
