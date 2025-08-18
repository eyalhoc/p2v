module cocotb_iverilog_dump();
initial begin
    $dumpfile("sim_build/adder__clk_bits16_num4_float16True.fst");
    $dumpvars(0, adder__clk_bits16_num4_float16True);
end
endmodule
