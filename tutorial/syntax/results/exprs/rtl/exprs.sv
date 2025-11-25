module exprs (
    input logic [7:0] a,
    input logic [7:0] b,
    output logic [7:0] bitwise,
    output logic boolean,
    output logic [10:0] lshift,
    output logic [7:0] rshift,
    output logic [7:0] o0,
    output logic [7:0] o1,
    output logic [7:0] o2,
    output logic [7:0] o3,
    output logic [7:0] o4,
    output logic [7:0] o5,
    output logic [7:0] o6,
    output logic [7:0] o7,
    input logic [2:0] o8_sel,
    output logic o8,
    output logic o8_neg,
    output logic o__0,
    output logic o__1,
    output logic o__2,
    output logic o__3,
    output logic o__4,
    output logic o__5,
    output logic o__6,
    output logic o__7,
    output logic o__8,
    output logic o__9,
    output logic o__10,
    output logic o__11
);


    assign bitwise = (((a + b) | (((a - b) & (a * b)) ^ (a - b))) | ~a);
    assign boolean = ((((((a == b) | (a != b)) | (a > b)) | (a >= b)) | (a < b)) | (a <= b));
    assign lshift = {a, 3'd0};
    assign rshift = {3'd0, b[7:3]};
    assign o0 = 8'd0;
    assign o1 = a;
    assign o2 = a;
    assign o3 = (8'd0 - a);
    assign o4 = bitwise[0] ? a : bitwise[1] ? b : bitwise[2] ? o1 : 8'd0;
    assign o5 = bitwise[0] ? a : bitwise[1] ? b : o1;
    assign {o6, o7} = bitwise[0] ? {a, b} : bitwise[1] ? {b, a} : bitwise[2] ? {2{o1}} : 16'd0;
    assign o8 = 
                ((o8_sel == 3'd0)) & o7[0] |
                ((o8_sel == 3'd1)) & o7[1] |
                ((o8_sel == 3'd2)) & o7[2] |
                ((o8_sel == 3'd3)) & o7[3] |
                ((o8_sel == 3'd4)) & o7[4] |
                ((o8_sel == 3'd5)) & o7[5] |
                ((o8_sel == 3'd6)) & o7[6] |
                ((o8_sel == 3'd7)) & o7[7];
    assign o8_neg = 
                ((o8_sel == 3'd0)) & ~o7[0] |
                ((o8_sel == 3'd1)) & ~o7[1] |
                ((o8_sel == 3'd2)) & ~o7[2] |
                ((o8_sel == 3'd3)) & ~o7[3] |
                ((o8_sel == 3'd4)) & ~o7[4] |
                ((o8_sel == 3'd5)) & ~o7[5] |
                ((o8_sel == 3'd6)) & ~o7[6] |
                ((o8_sel == 3'd7)) & ~o7[7];
    assign o__0 = ((a + 8'd2) == (a + 8'd2));
    assign o__1 = ((a * 8'd2) == (a * 8'd2));
    assign o__2 = ((a | 8'd2) == (a | 8'd2));
    assign o__3 = ((a & 8'd2) == (a & 8'd2));
    assign o__4 = ((a ^ 8'd2) == (a ^ 8'd2));
    assign o__5 = ((a == 8'd2) == (a == 8'd2));
    assign o__6 = ((a != 8'd2) == (a != 8'd2));
    assign o__7 = ((a > 8'd2) == (a > 8'd2));
    assign o__8 = ((a < 8'd2) == (a < 8'd2));
    assign o__9 = ((a >= 8'd2) == (a >= 8'd2));
    assign o__10 = ((a <= 8'd2) == (a <= 8'd2));
    assign o__11 = ((a - 8'd2) == (a - 8'd2));

endmodule  // exprs
