module _or_gate__bits33 (
    input  logic [32:0] a,
    input  logic [32:0] b,
    output logic [32:0] c
);

    // _or_gate module parameters:
    //  * bits = 33 (int) # None

    assign c = a | b;

endmodule  // _or_gate__bits33
