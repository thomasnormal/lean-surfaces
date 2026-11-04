module top;
  logic [1:0] subject;
  logic [3:0] result;
  initial begin
    subject = 2'd2;
    case (subject)
      default: result = 4'd9;
      2'd1: result = 4'd1;
      2'd2: result = 4'd2;
    endcase
    if (result == 4'd2) begin
      subject = 2'd3;
      case (subject)
        2'd0: result = 4'd0;
        default: result = 4'd6;
        2'd1: result = 4'd1;
      endcase
      case (subject)
        2'd0: result = 4'd0;
        2'd1: result = 4'd1;
      endcase
      if (result == 4'd6)
        $display("PASS");
      else
        $display("FAIL");
    end else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 6c2937aad4989dc0edc7012d xrun(64) 24.03-s004 2026-10-10T02:18:23Z; PASS.
