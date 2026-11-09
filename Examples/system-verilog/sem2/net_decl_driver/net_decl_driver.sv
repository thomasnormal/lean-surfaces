// Clean-room scheduler witness for IEEE 1800-2023 §10.3.1.
// A net declaration assignment is a continuous driver, not a time-zero
// storage initializer. Icarus 13.0 and Xcelium 24.03 print `P03 post=5`.
module net_decl_driver;
  reg [3:0] a = 4'd0;
  wire [3:0] c = a;
  initial begin
    #1 a = 4'd5;
    #1 $display("P03 post=%0d", c);
    $finish;
  end
endmodule
