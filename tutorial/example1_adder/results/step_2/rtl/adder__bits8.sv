module adder__bits8 (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] o
);

    // adder module parameters:
    //  * bits = 8 (int) #  set_param(var, type, constraints)

    assign o = a + b;

endmodule
