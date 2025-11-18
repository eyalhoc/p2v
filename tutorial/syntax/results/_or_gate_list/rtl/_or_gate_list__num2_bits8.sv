module _or_gate_list__num2_bits8 (
    input  logic [7:0] i__0,
    input  logic [7:0] i__1,
    output logic [7:0] c
);

    // _or_gate_list module parameters:
    //  * num = 2 (int) #  number of inputs
    //  * bits = 8 (int) #  data width

    assign c = (i__0 | i__1);

endmodule  // _or_gate_list__num2_bits8
