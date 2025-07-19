module instances__num4_bits32 (
    input  logic [31:0] a0,
    input  logic [31:0] b0,
    output logic [31:0] c0,
    input  logic [32:0] a1,
    input  logic [32:0] b1,
    output logic [32:0] c1,
    input  logic [33:0] a2,
    input  logic [33:0] b2,
    output logic [33:0] c2,
    input  logic [34:0] a3,
    input  logic [34:0] b3,
    output logic [34:0] c3,
    input  logic [15:0] a,
    input  logic [15:0] b,
    output logic [15:0] c,
    output logic [15:0] ca,
    input  logic [15:0] a_01,
    input  logic [15:0] b_01,
    output logic [15:0] c_01,
    input  logic [31:0] aa,
    input  logic [31:0] bb,
    output logic [31:0] cc
);

    // instances module parameters:
    //  * num = 4 (int) # None
    //  * bits = 32 (int) # None

    _or_gate__bits32 _or_gate0 (
        .a(a0),  // input
        .b(b0),  // input
        .c(c0)   // output
    );

    _or_gate__bits33 _or_gate1 (
        .a(a1),  // input
        .b(b1),  // input
        .c(c1)   // output
    );

    _or_gate__bits34 _or_gate2 (
        .a(a2),  // input
        .b(b2),  // input
        .c(c2)   // output
    );

    _or_gate__bits35 _or_gate3 (
        .a(a3),  // input
        .b(b3),  // input
        .c(c3)   // output
    );

    _or_gate__bits16 my_or_gate (
        .a(a),  // input
        .b(b),  // input
        .c(c)   // output
    );

    _or_gate__bits16 my_auto_connect_or (
        .c(ca),  // output
        .a(a),   // input
        .b(b)    // input
    );

    _or_gate__bits16 my_auto_connect_ports_or (
        .a(a_01),  // input
        .b(b_01),  // input
        .c(c_01)   // output
    );

    _and_gate #(
        .BITS(32)
    ) _and_gate (
        .a(aa),  // input
        .b(bb),  // input
        .c(cc)   // output
    );


endmodule  // instances__num4_bits32
