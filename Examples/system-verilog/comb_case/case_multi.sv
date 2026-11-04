// WP-G S3a: an item with several patterns (a comma list), a repeated pattern (the first item wins, the
// second is never reached) and arms that are gate trees.
module case_multi (input logic [1:0] s, input logic [3:0] a, b, output logic [3:0] y);
  always_comb begin
    case (s)
      2'd0, 2'd3: y = a;
      2'd1: y = b;
      2'd1: y = ~a;
      default: y = a ^ b;
    endcase
  end
endmodule
