module _or_gate__bits16 (
    input  logic [15:0] a,
    input  logic [15:0] b,
    output logic [15:0] c
);

    // _or_gate module parameters:
    //  * bits = 16 (int) # None

    assign c = (a | b);

endmodule  // _or_gate__bits16
