module _or_gate__bits35 (
    input  logic [34:0] a,
    input  logic [34:0] b,
    output logic [34:0] c
);

    // _or_gate module parameters:
    //  * bits = 35 (int) # None

    assign c = (a | b);

endmodule  // _or_gate__bits35
