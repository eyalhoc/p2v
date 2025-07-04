module float_adder (num1, num2, result, overflow, zero, NaN, precisionLost);
input [15:0] num1, num2;
 output [15:0] result;
 output overflow;
 output zero;
 output NaN;
 output reg precisionLost;
 reg [15:0] bigNum, smallNum;
 reg [10:0] sign_small_float, shifted_small_float;
 reg [9:0] sum_shifted;
 reg [3:0] shift_am;
 reg [9:0] small_extension;
endmodule
