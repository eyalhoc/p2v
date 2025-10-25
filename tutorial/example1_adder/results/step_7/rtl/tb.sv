module tb ();

    // tb_adder module parameters:
    //  * async_reset = True (bool) #  sync reset or async reset
    //  * size = 4 (int) #  number of inputs to test

    logic clk;
    logic resetn;

    initial
        forever begin
            clk = 0;
            #3;
            clk = 1;
            #3;
        end


    initial begin
        resetn = 1;
        repeat (0) @(negedge clk);  // async reset occurs not on posedge of clock
        resetn = 0;
        repeat (20) @(posedge clk);
        resetn = 1;
    end

    logic _clk_reset_released;
    initial _clk_reset_released = 1'd0;

    always @(posedge resetn) _clk_reset_released = $time > 0;
    logic valid;
    initial valid = 1'd0;

    logic [15:0] inputs__0;
    logic [15:0] inputs__1;
    logic [15:0] inputs__2;
    logic [15:0] inputs__3;
    logic [15:0] o;
    logic valid_out;
    adder__clk_bits16_num4_float16False adder (
        .clk(clk),  // input
        .resetn(resetn),  // input
        .valid(valid),  // input
        .data_in__0(inputs__0),  // input[15:0]
        .data_in__1(inputs__1),  // input[15:0]
        .data_in__2(inputs__2),  // input[15:0]
        .data_in__3(inputs__3),  // input[15:0]
        .o(o),  // output[15:0]
        .valid_out(valid_out)  // output
    );

    reg [63:0] data_in_q [$];
    reg [15:0] expected_q[$];
    initial begin
        data_in_q.push_back({16'h3c5f, 16'hfda9, 16'he623, 16'hf1ca});
        expected_q.push_back(16'h11f5);
        data_in_q.push_back({16'hc25c, 16'h6b7f, 16'h300e, 16'hf9c8});
        expected_q.push_back(16'h57b1);
        data_in_q.push_back({16'h0e83, 16'hc795, 16'hdd93, 16'h0114});
        expected_q.push_back(16'hb4bf);
        data_in_q.push_back({16'he409, 16'h885c, 16'h7520, 16'h3457});
        expected_q.push_back(16'h15dc);
    end
    logic [63:0] data_in;
    initial data_in = 64'd0;

    always @(negedge clk)
        if ((_clk_reset_released & ~((data_in_q.size() == 32'd0)))) begin
            data_in = data_in_q.pop_front();
            valid   = ~((data_in_q.size() == 32'd0));
        end
    assign {inputs__0, inputs__1, inputs__2, inputs__3} = data_in;
    logic [15:0] expected;
    initial expected = expected_q.pop_front();

    always @(posedge clk)
        if (valid_out) begin
            expected = expected_q.pop_front();
        end
    always @(posedge clk)
        if ((data_in_q.size() == 32'd0)) begin

            begin
                $display("test PASSED");
                #10;
                $finish;
            end

        end
    logic diff;
    assign diff = (valid_out & (o != expected));

    _mismatch_expected_0x_0h_actual_0x_0h_expected_o_assert :
    assert property (@(posedge clk) disable iff (!resetn) ~diff)
    else $fatal(1, "mismatch: expected=0x%0h, actual=0x%0h", expected, o);

    // CODE ADDED TO SUPPORT LEGACY SIMULATOR vvp THAT DOES NOT SUPPORT CONCURRENT ASSERTIONS
    logic assert_never__mismatch_expected_0x_0h_actual_0x_0h_expected_o;
    assign assert_never__mismatch_expected_0x_0h_actual_0x_0h_expected_o = ~(~diff);

    always @(posedge clk)
        if (resetn & assert_never__mismatch_expected_0x_0h_actual_0x_0h_expected_o)
            $fatal(1, "mismatch: expected=0x%0h, actual=0x%0h", expected, o);

    logic [31:0] _count_timeout__clk;
    initial _count_timeout__clk = 32'd0;


    always @(posedge clk) _count_timeout__clk <= (_count_timeout__clk + 32'd1);

    _reached_timeout_after_64_cycles_of_clk_assert :
    assert property (@(posedge clk) disable iff (!resetn) (_count_timeout__clk < 32'd64))
    else $fatal(1, "reached timeout after 64 cycles of clk");

    // CODE ADDED TO SUPPORT LEGACY SIMULATOR vvp THAT DOES NOT SUPPORT CONCURRENT ASSERTIONS
    logic assert_never__reached_timeout_after_64_cycles_of_clk;
    assign assert_never__reached_timeout_after_64_cycles_of_clk = ~((_count_timeout__clk < 32'd64));

    always @(posedge clk)
        if (resetn & assert_never__reached_timeout_after_64_cycles_of_clk)
            $fatal(1, "reached timeout after 64 cycles of clk");


    initial begin
        $dumpfile("dump.fst");
        $dumpvars;
        $dumpon;
    end


endmodule  // tb
