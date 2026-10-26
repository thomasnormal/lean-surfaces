/* Destructive reinitialization of a finite scalar dynamic array. */
module top;
  int arr[];

  initial begin
    arr = new[5];
    arr[0] = 10;
    arr[4] = 50;

    // A new allocation without an initializer destroys the old values.
    arr = new[3];
    if (arr.size() === 3 && arr[0] === 0 && arr[1] === 0 && arr[2] === 0)
      $display("PASS");
    else
      $display("FAIL: size=%0d [0]=%0d", arr.size(), arr[0]);
    $finish;
  end
endmodule
