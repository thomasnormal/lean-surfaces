module top;
  typedef logic signed [7:0] four_signed_byte_t;
  typedef logic [7:0] four_unsigned_byte_t;
  typedef bit signed [7:0] two_signed_byte_t;
  typedef bit two_scalar_t;
  typedef logic four_scalar_t;
  four_signed_byte_t source_value;
  four_unsigned_byte_t preserved_value;
  two_signed_byte_t squashed_value;
  four_unsigned_byte_t reinterpreted_value;
  two_scalar_t squashed_scalar;
  four_scalar_t preserved_scalar;

  initial begin
    source_value = 8'b1xz00101;
    preserved_value = four_unsigned_byte_t'(source_value);
    squashed_value = two_signed_byte_t'(source_value);
    squashed_scalar = two_scalar_t'(1'bz);
    preserved_scalar = 1'bx;
    source_value = 8'h85;
    reinterpreted_value = four_unsigned_byte_t'(source_value);
    $display("alias-state=[%b][%h][%h][%b][%b]", preserved_value,
             squashed_value, reinterpreted_value, squashed_scalar,
             preserved_scalar);
    if ((preserved_value === 8'b1xz00101) &&
        (squashed_value === 8'h85) && (squashed_value < 0) &&
        (reinterpreted_value === 8'h85) && !(reinterpreted_value < 0) &&
        (squashed_scalar === 1'b0) && (preserved_scalar === 1'bx))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
