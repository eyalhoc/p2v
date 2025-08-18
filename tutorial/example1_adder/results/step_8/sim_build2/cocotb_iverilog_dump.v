module cocotb_iverilog_dump();
initial begin
    $dumpfile("sim_build2/adder__bits16_num4_float16False.fst");
    $dumpvars(0, adder__bits16_num4_float16False);
end
endmodule
