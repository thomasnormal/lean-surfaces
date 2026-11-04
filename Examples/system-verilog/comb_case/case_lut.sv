// WP-G S3a: a 4-entry look-up table (constant items, constant values) and its `default`. y = 5 * x mod 16
// for x = 0..3 is NOT the table: the values are arbitrary, the point is the fold and its bridge to numbers.
module case_lut (input logic [1:0] x, output logic [3:0] y);
  always_comb begin
    case (x)
      2'd0: y = 4'd9;
      2'd1: y = 4'd4;
      2'd2: y = 4'd14;
      default: y = 4'd1;
    endcase
  end
endmodule
