module instances__num4_bits32 (
    input  logic [31:0] a0__0,
    input  logic [31:0] b0__0,
    output logic [31:0] c0__0,
    input  logic [32:0] a0__1,
    input  logic [32:0] b0__1,
    output logic [32:0] c0__1,
    input  logic [33:0] a0__2,
    input  logic [33:0] b0__2,
    output logic [33:0] c0__2,
    input  logic [34:0] a0__3,
    input  logic [34:0] b0__3,
    output logic [34:0] c0__3,
    input  logic [31:0] al__0,
    input  logic [31:0] al__1,
    input  logic [31:0] al__2,
    input  logic [31:0] al__3,
    output logic [31:0] cl,
    input  logic [31:0] a2__0__w,
    input  logic [31:0] a2__0__r,
    output logic [31:0] c2__0,
    input  logic [31:0] a2__1__w,
    input  logic [31:0] a2__1__r,
    output logic [31:0] c2__1,
    input  logic [31:0] a2__2__w,
    input  logic [31:0] a2__2__r,
    output logic [31:0] c2__2,
    input  logic [31:0] a2__3__w,
    input  logic [31:0] a2__3__r,
    output logic [31:0] c2__3,
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
        .a(a0__0),  // input
        .b(b0__0),  // input
        .c(c0__0)   // output
    );

    _or_gate__bits33 _or_gate1 (
        .a(a0__1),  // input
        .b(b0__1),  // input
        .c(c0__1)   // output
    );

    _or_gate__bits34 _or_gate2 (
        .a(a0__2),  // input
        .b(b0__2),  // input
        .c(c0__2)   // output
    );

    _or_gate__bits35 _or_gate3 (
        .a(a0__3),  // input
        .b(b0__3),  // input
        .c(c0__3)   // output
    );

    _or_gate_list__num4_bits32 _or_gate_list (
        .i__0(al__0),  // input
        .i__1(al__1),  // input
        .i__2(al__2),  // input
        .i__3(al__3),  // input
        .c(cl)  // output
    );

    _or_gate_dict__num4_bits32 _or_gate_dict (
        .i__0__w(a2__0__w),  // input
        .i__0__r(a2__0__r),  // input
        .c__0(c2__0),  // output
        .i__1__w(a2__1__w),  // input
        .i__1__r(a2__1__r),  // input
        .c__1(c2__1),  // output
        .i__2__w(a2__2__w),  // input
        .i__2__r(a2__2__r),  // input
        .c__2(c2__2),  // output
        .i__3__w(a2__3__w),  // input
        .i__3__r(a2__3__r),  // input
        .c__3(c2__3)  // output
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
