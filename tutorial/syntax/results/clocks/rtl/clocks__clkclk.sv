module clocks__clkclk (
    input logic clk,
    input logic rst_n,
    input logic [31:0] i0,
    output logic [31:0] o0,
    input logic clk0,
    input logic [31:0] i1,
    output logic [31:0] o1,
    input logic clk1,
    input logic clk1_rst_n,
    input logic [31:0] i2,
    output logic [31:0] o2,
    input logic clk2,
    input logic clk2_reset,
    input logic [31:0] i3,
    output logic [31:0] o3,
    input logic clk3,
    input logic clk3_rst_n,
    input logic clk3_reset,
    input logic [31:0] i4,
    output logic [31:0] o4,
    input logic clk4,
    input logic [31:0] i5,
    output logic [31:0] o5,
    input logic clk5,
    input logic clk5_rst_n,
    input logic [31:0] i6,
    output logic [31:0] o6,
    input logic clk6,
    input logic clk6_reset,
    input logic [31:0] i7,
    output logic [31:0] o7,
    input logic clk7,
    input logic clk7_rst_n,
    input logic clk7_reset,
    input logic [31:0] i8,
    output logic [31:0] o8,
    input logic clk8,
    input logic clk8_reset,
    input logic [31:0] i9,
    output logic [31:0] o9,
    input logic clk9,
    input logic clk9_rst_n,
    input logic [31:0] i10,
    output logic [31:0] o10
);

    // clocks module parameters:
    //  * clk = clk_arst() (p2v_clock) #  verifies that clk if a p2v clock

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) o0 <= 32'd0;
        else o0 <= i0;

    always_ff @(posedge clk0) o1 <= i1;

    always_ff @(posedge clk1 or negedge clk1_rst_n)
        if (!clk1_rst_n) o2 <= 32'd0;
        else o2 <= i2;

    always_ff @(posedge clk2)
        if (clk2_reset) o3 <= 32'd0;
        else o3 <= i3;

    always_ff @(posedge clk3 or negedge clk3_rst_n)
        if (!clk3_rst_n) o4 <= 32'd0;
        else if (clk3_reset) o4 <= 32'd0;
        else o4 <= i4;

    always_ff @(posedge clk4) o5 <= i5;

    always_ff @(posedge clk5 or negedge clk5_rst_n)
        if (!clk5_rst_n) o6 <= 32'd0;
        else o6 <= i6;

    always_ff @(posedge clk6)
        if (clk6_reset) o7 <= 32'd0;
        else o7 <= i7;

    always_ff @(posedge clk7 or negedge clk7_rst_n)
        if (!clk7_rst_n) o8 <= 32'd0;
        else if (clk7_reset) o8 <= 32'd0;
        else o8 <= i8;

    always_ff @(posedge clk8)
        if (clk8_reset) o9 <= 32'd0;
        else o9 <= i9;

    always_ff @(posedge clk9 or negedge clk9_rst_n)
        if (!clk9_rst_n) o10 <= 32'd0;
        else o10 <= i10;


endmodule  // clocks__clkclk
