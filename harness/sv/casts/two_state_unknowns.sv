module top;
  logic signed [3:0] signed_source;
  int x_result;
  int z_result;
  int known_sign_result;
  bit scalar_x;
  bit scalar_z;
  integer four_state_result;
  integer size_unknown_result;
  time unsigned_unknown_result;

  initial begin
    signed_source = 4'bx001;
    x_result = int'(signed_source);
    four_state_result = integer'(signed_source);
    size_unknown_result = 32'(signed_source);
    scalar_x = bit'(1'bx);
    scalar_z = bit'(1'bz);
    signed_source = 4'bz101;
    z_result = int'(signed_source);
    unsigned_unknown_result = time'(signed_source);
    signed_source = 4'b1xz1;
    known_sign_result = int'(signed_source);
    $display("two-state=[%h][%h][%h][%b][%b][%b][%b][%b]", x_result, z_result,
             known_sign_result, scalar_x, scalar_z, four_state_result,
             size_unknown_result, unsigned_unknown_result);
    if ((x_result === 32'h00000001) &&
        (z_result === 32'h00000005) &&
        (known_sign_result === 32'hfffffff9) &&
        (scalar_x === 1'b0) && (scalar_z === 1'b0) &&
        (four_state_result === 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxx001) &&
        (size_unknown_result === 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxx001) &&
        (unsigned_unknown_result === 64'bzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz101))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 9a1e73f5144c6c37f363feed TOOL:	xrun(64)	24.03-s004 2026-10-09T21:34:37Z
