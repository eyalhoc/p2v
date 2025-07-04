module adder__clk_bits16_num2_float16True (
    input logic clk,
    input logic resetn,
    input logic valid,
    input logic [15:0] i0,
    input logic [15:0] i1,
    output logic [15:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = "clock('clk', rst_n='resetn')" (p2v_clock)
    //  * bits = 16 (int) # data width
    //  * num = 2 (int) # number of inputs
    //  * float16 = True (bool) # use a float16 adder

    logic [15:0] o_pre;
    logic overflow;
    logic zero;
    logic NaN;
    logic precisionLost;
    float_adder float_adder (
        .num1(i0),  // input
        .num2(i1),  // input
        .result(o_pre),  // output
        .overflow(overflow),  // output
        .zero(zero),  // output
        .NaN(NaN),  // output
        .precisionLost(precisionLost)  // output
    );

    logic assert_never__received_unexpected_overflow;
    assign assert_never__received_unexpected_overflow = overflow;

    always @(posedge clk)
        if (resetn & assert_never__received_unexpected_overflow)
            $fatal(0, "received unexpected overflow");

    logic assert_never__received_unexpected_zero;
    assign assert_never__received_unexpected_zero = zero;

    always @(posedge clk)
        if (resetn & assert_never__received_unexpected_zero)
            $fatal(0, "received unexpected zero");

    logic assert_never__received_unexpected_NaN;
    assign assert_never__received_unexpected_NaN = NaN;

    always @(posedge clk)
        if (resetn & assert_never__received_unexpected_NaN)
            $fatal(0, "received unexpected NaN");

    always_ff @(posedge clk or negedge resetn)
        if (!resetn) o <= 16'd0;
        else if (valid) o <= o_pre;

    always_ff @(posedge clk or negedge resetn)
        if (!resetn) valid_out <= 1'd0;
        else valid_out <= valid;


endmodule
