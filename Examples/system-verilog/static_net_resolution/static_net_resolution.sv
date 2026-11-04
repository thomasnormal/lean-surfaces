/* Fixed literal wire drivers resolve at time zero under the IEEE table. */
module top;
  wire conflict, agree, z_only, unknown;
  assign conflict = 1'b0;
  assign conflict = 1'b1;
  assign agree = 1'b1;
  assign agree = 1'b1;
  assign z_only = 1'bz;
  assign z_only = 1'bz;
  assign unknown = 1'bx;
  assign unknown = 1'b0;
  initial begin
    if (conflict === 1'bx && agree === 1'b1 &&
        z_only === 1'bz && unknown === 1'bx)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
