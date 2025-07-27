module _or_gate_list__num4_bits32 (
    input  logic [31:0] i__0,
    input  logic [31:0] i__1,
    input  logic [31:0] i__2,
    input  logic [31:0] i__3,
    output logic [31:0] c
);

    // _or_gate_list module parameters:
    //  * num = 4 (int) #  number of inputs
    //  * bits = 32 (int) #  data width

    assign c = i__0 | i__1 | i__2 | i__3;

endmodule  // _or_gate_list__num4_bits32
