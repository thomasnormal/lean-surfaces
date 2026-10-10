module top;
  logic [1:0] subject;
  logic [2:0] result;
  initial begin
    subject = 2'bxz;
    case (subject)
      2'bxx: result = 3'd1;
      2'bzx: result = 3'd2;
      2'bxz: result = 3'd3;
      default: result = 3'd0;
    endcase
    if (result == 3'd3) begin
      subject = 2'bzx;
      case (subject)
        2'bxz: result = 3'd1;
        2'bzz: result = 3'd2;
        2'bzx: result = 3'd4;
        default: result = 3'd0;
      endcase
      if (result == 3'd4)
        $display("PASS");
      else
        $display("FAIL");
    end else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: fcecd03548cf3bb198b34a70 xrun(64) 24.03-s004 2026-10-10T02:18:26Z; PASS.
