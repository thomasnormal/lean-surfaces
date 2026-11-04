module top;
  logic signed [3:0] signed_source;
  logic signed [7:0] signed_dest;
  logic [7:0] unsigned_dest;
  bit signed [7:0] two_state_dest;
  bit signed [3:0] two_state_source;
  logic signed signed_scalar;
  logic unsigned unsigned_scalar;

  initial begin
    signed_source = 4'bx001;
    signed_dest = signed_source;
    unsigned_dest = signed_source;
    two_state_dest = signed_source;
    $display("x-sign=[%b][%b][%b]", signed_dest, unsigned_dest, two_state_dest);
    signed_source = 4'bz101;
    signed_dest = signed_source;
    unsigned_dest = signed_source;
    two_state_dest = signed_source;
    $display("z-sign=[%b][%b][%b]", signed_dest, unsigned_dest, two_state_dest);
    two_state_source = 4'bx101;
    signed_dest = two_state_source;
    $display("squash-before-sign=[%b][%b]", two_state_source, signed_dest);
    two_state_source = 4'b1xz1;
    signed_dest = two_state_source;
    $display("known-sign-squash=[%b][%b]", two_state_source, signed_dest);
    signed_scalar = 1'b1;
    unsigned_scalar = 1'b1;
    signed_dest = signed_scalar;
    unsigned_dest = unsigned_scalar;
    $display("scalar-one=[%b][%b]", signed_dest, unsigned_dest);
    signed_scalar = 1'bx;
    signed_dest = signed_scalar;
    $display("scalar-x=[%b]", signed_dest);
    signed_scalar = 1'bz;
    signed_dest = signed_scalar;
    $display("scalar-z=[%b]", signed_dest);
    $finish;
  end
endmodule
