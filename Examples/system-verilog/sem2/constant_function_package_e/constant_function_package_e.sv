package constant_function_package_e_pkg;
  function automatic integer vbits(input integer v);
    return (v > 1) ? $clog2(v) : 1;
  endfunction
endpackage
module constant_function_package_e #(parameter integer N = 8) (
    output logic [7:0] y);
  import constant_function_package_e_pkg::*;
  localparam integer W = vbits(N);
  logic [W-1:0] z;
  assign y = W;
  assign z = W;
endmodule
