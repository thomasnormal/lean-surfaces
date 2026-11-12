module initial_syscall_e(input logic x, output logic y);
  assign y = x;
  initial if (!x) $fatal(1, "bad");
endmodule
