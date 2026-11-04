// SPDX-License-Identifier: Apache-2.0
module top;
  int score = 0;
  logic [7:0] gate = 8'b1xxx_xxxx;
  initial begin
    labeled_check: assert (gate) begin
      score += 1;
      assume (0) score += 100; else score += 2;
      cover (1'bx) score += 200;
    end else score += 400;
    assert (1'bz) else begin end
    assume (0) else begin end
    cover (0);
    assert (0) score += 800; else begin
      score += 4;
      cover (1) score += 8;
    end
    $display("actions %0d",score);
    $finish;
  end
endmodule
