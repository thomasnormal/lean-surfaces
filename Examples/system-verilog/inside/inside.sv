// Pure integral membership, IEEE 1800-2023 §11.4.13.
module top;
  logic [3:0] u, x;
  logic signed [3:0] s;
  logic signed [3:0] choices [0:1];
  integer lo, hi;
  logic signed [7:0] subject;
  logic signed [3:0] signed_cells [0:1];
  logic [3:0] unsigned_cells [0:1];
  typedef enum logic signed [3:0] { A = 2, B = 6 } E;
  E e;
  logic [3:0] proof_left, proof_candidate, proof_mask;
  logic proof_result;
  initial begin
    u = 4'hf; s = -1; x = 4'bx001;
    choices = '{-1, 2};
    $display("signed %b %b %b", s inside {-1}, s inside {8'shff}, s inside {[8'shfe:8'sh00]});
    $display("mixed %b %b %b", s inside {8'hff}, s inside {-1, 8'h00}, u inside {-1});
    $display("context %b %b", u inside {4'hf, 16'h0000}, s inside {choices});
    $display("wild %b %b %b", x inside {4'bz001}, x inside {4'b0001}, x inside {4'b0001, 4'bx001});
    $display("unknown %b %b %b", x inside {[4'h0:4'hf]}, x inside {[4'hf:4'h0]}, x inside {[$:4'hf]});
    s = -8;
    $display("dollar %b %b %b", s inside {[$:-1]}, s inside {[0:$]}, u inside {[$:4'hf]});
    lo = 7; hi = 3;
    $display("reverse %b %b", s inside {[lo:hi]}, 32'bx inside {[lo:hi]});
    $display("bounds %b %b %b", u inside {[4'bxxxx:4'h0]}, u inside {[4'hf:4'bxxxx]}, 4'b0000 inside {[4'bxxxx:4'hf]});
    subject = -1;
    signed_cells = '{-1, 2}; unsigned_cells = '{15, 2};
    $display("cells %b %b %b", subject inside {signed_cells}, subject inside {unsigned_cells}, subject inside {signed_cells, 8'h00});
    e = E'(0);
    $display("enum %b %b", e inside {[$:4'sh7]}, e inside {[$:B]});
    proof_left = 4'bx001; proof_candidate = 4'b0001; proof_mask = 4'bz001;
    proof_result = proof_left inside {proof_candidate, proof_mask};
    $display("dominance %b", proof_result);
    $display("nested %b", (u inside {4'hf}) inside {1'b1});
    $finish;
  end
endmodule

// Independent observation: 2026-10-20, group integral-inside.
// Source SHA256 before this trailing observation block:
// 1cab467b201d87256d6768af538ae8c24f2eacec9e3bcfdbca6ba5223b98fdd8
// Mapping: each labeled display is compared verbatim, with no value or time projection.
