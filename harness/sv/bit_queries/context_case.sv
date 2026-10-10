module top;
  initial begin
    logic [63:0] extended;
    extended = $bits(byte) + 64'd1;
    if (extended != 64'd9 || (($bits(bit) - 2) >= 0) ||
        $bits($bits(bit)) != 32) begin
      $display("FAIL: query sizing or signed integer result");
      $finish;
    end
    case ($bits(time))
      64'd64: $display("PASS");
      default: $display("FAIL: query case subject");
    endcase
    $finish;
  end
endmodule
// REFERENCE: 6d654e09e0df82cbe036af6f xrun(64) 24.03-s004 2026-10-10T03:16:17Z; PASS.
