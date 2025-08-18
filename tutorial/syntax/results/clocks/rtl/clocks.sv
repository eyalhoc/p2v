module clocks (
    input logic clk,
    input logic rst_n,
    input logic [31:0] i__0,
    output logic [31:0] o__0,
    input logic clk0,
    input logic [31:0] i__1,
    output logic [31:0] o__1,
    input logic clk1,
    input logic clk1_rst_n,
    input logic [31:0] i__2,
    output logic [31:0] o__2,
    input logic clk2,
    input logic clk2_reset,
    input logic [31:0] i__3,
    output logic [31:0] o__3,
    input logic clk3,
    input logic clk3_reset,
    input logic clk3_rst_n,
    input logic [31:0] i__4,
    output logic [31:0] o__4,
    input logic clk4,
    input logic [31:0] i__5,
    output logic [31:0] o__5,
    input logic clk5,
    input logic clk5_rst_n,
    input logic [31:0] i__6,
    output logic [31:0] o__6,
    input logic clk6,
    input logic clk6_reset,
    input logic [31:0] i__7,
    output logic [31:0] o__7,
    input logic clk7,
    input logic clk7_reset,
    input logic clk7_rst_n,
    input logic [31:0] i__8,
    output logic [31:0] o__8,
    input logic clk8,
    input logic clk8_reset,
    input logic [31:0] i__9,
    output logic [31:0] o__9,
    input logic clk9,
    input logic clk9_rst_n,
    input logic [31:0] i__10,
    output logic [31:0] o__10
);

    // clocks module parameters:
    //  * clk = clk_arst() (p2v_clock) #  verifies that clk if a p2v clock

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) o__0 <= 32'd0;
        else o__0 <= i__0;

    always_ff @(posedge clk0) o__1 <= i__1;

    always_ff @(posedge clk1 or negedge clk1_rst_n)
        if (!clk1_rst_n) o__2 <= 32'd0;
        else o__2 <= i__2;

    always_ff @(posedge clk2)
        if (clk2_reset) o__3 <= 32'd0;
        else o__3 <= i__3;

    always_ff @(posedge clk3 or negedge clk3_rst_n)
        if (!clk3_rst_n) o__4 <= 32'd0;
        else if (clk3_reset) o__4 <= 32'd0;
        else o__4 <= i__4;

    always_ff @(posedge clk4) o__5 <= i__5;

    always_ff @(posedge clk5 or negedge clk5_rst_n)
        if (!clk5_rst_n) o__6 <= 32'd0;
        else o__6 <= i__6;

    always_ff @(posedge clk6)
        if (clk6_reset) o__7 <= 32'd0;
        else o__7 <= i__7;

    always_ff @(posedge clk7 or negedge clk7_rst_n)
        if (!clk7_rst_n) o__8 <= 32'd0;
        else if (clk7_reset) o__8 <= 32'd0;
        else o__8 <= i__8;

    always_ff @(posedge clk8)
        if (clk8_reset) o__9 <= 32'd0;
        else o__9 <= i__9;

    always_ff @(posedge clk9 or negedge clk9_rst_n)
        if (!clk9_rst_n) o__10 <= 32'd0;
        else o__10 <= i__10;


endmodule  // clocks
