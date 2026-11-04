// WP-G S3b: a plain `case` whose arms are trees: an `if/else` in an arm, a `begin ... end` with a default
// and an override in an arm, and a plain assignment.
module case_tree (input logic [1:0] s, input logic e, input logic [3:0] a, b, c, d, output logic [3:0] y);
  always_comb begin
    case (s)
      2'd0: if (e) y = a; else y = b;
      2'd1: begin
        y = b;
        if (e) y = c;
      end
      2'd2: y = c;
      default: begin
        if (e) begin
          y = d;
        end else begin
          y = a;
        end
      end
    endcase
  end
endmodule
