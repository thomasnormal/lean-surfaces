`timescale 1ns/1ps
module unsized_xz_conversion_canonical_e_tb;
  wire [39:0] qx40, qz40, qhx40, qhz40;
  wire [7:0] qx8, qz8, qhx8, qhz8;

  unsized_xz_conversion_canonical_e #(.N(40)) d40
    (.qx(qx40), .qz(qz40), .qhx(qhx40), .qhz(qhz40));
  unsized_xz_conversion_canonical_e #(.N(8)) d8
    (.qx(qx8), .qz(qz8), .qhx(qhx8), .qhz(qhz8));

  initial begin
    #1 $display("ROW values qx40=%b qz40=%b qhx40=%b qhz40=%b qx8=%b qz8=%b qhx8=%b qhz8=%b",
               qx40, qz40, qhx40, qhz40, qx8, qz8, qhx8, qhz8);
    $finish;
  end
endmodule
