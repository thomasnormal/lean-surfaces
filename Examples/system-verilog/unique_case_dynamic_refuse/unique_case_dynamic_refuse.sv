// Dynamic unique-case wildcard patterns stay loud in the legacy self-check tier.
module top;
  logic [4:0] a;
  logic [2:0] y;

  initial begin
    a = 5'b00010;
    unique case (a) inside
      5'b0001?: y = 3'd1;
      5'b001??: y = 3'd2;
      5'b1????: y = 3'd3;
      5'b00001: y = 3'd4;
      default:  y = 3'd0;
    endcase
  end
endmodule
