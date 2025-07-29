module adder__clk_bits16_num2_float16True (
    input logic clk,
    input logic resetn,
    input logic valid,
    input logic [15:0] data_in__0,
    input logic [15:0] data_in__1,
    output logic [15:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = "clock('clk', rst_n='resetn')" (p2v_clock) # None
    //  * bits = 16 (int) #  data width
    //  * num = 2 (int) #  number of inputs
    //  * float16 = True (bool) #  use a float16 adder

    logic [15:0] o_pre;
    logic overflow;
    logic zero;
    logic NaN;
    float_adder float_adder (
        .num1(data_in__0),  // input
        .num2(data_in__1),  // input
        .result(o_pre),  // output
        .overflow(overflow),  // output
        .zero(zero),  // output
        .NaN(NaN),  // output
        .precisionLost()  // output
    );

    received_unexpected_overflow_assert :
    assert property (@(posedge clk) disable iff (!resetn) ~(overflow))
    else $fatal(1, "received unexpected overflow");

    received_unexpected_zero_assert :
    assert property (@(posedge clk) disable iff (!resetn) ~(zero))
    else $fatal(1, "received unexpected zero");

    received_unexpected_NaN_assert :
    assert property (@(posedge clk) disable iff (!resetn) ~(NaN))
    else $fatal(1, "received unexpected NaN");

    always_ff @(posedge clk or negedge resetn)
        if (!resetn) o <= 16'd0;
        else if (valid) o <= o_pre;

    always_ff @(posedge clk or negedge resetn)
        if (!resetn) valid_out <= 1'd0;
        else valid_out <= valid;


endmodule  // adder__clk_bits16_num2_float16True
