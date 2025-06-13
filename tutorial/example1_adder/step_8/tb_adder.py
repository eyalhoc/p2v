
# tb step 1: create a test bench that drives inputs and tests sum of adder
# tb step 2: support float16

import numpy as np

from p2v import p2v, misc, clock

import adder

class tb_adder(p2v):
    def module(self, async_reset=True, size=32):
        self.set_param(async_reset, bool, remark="sync reset or async reset")
        self.set_param(size, int, size > 0, remark="number of inputs to test")
        self.set_modname("tb") # explicitly set module name
        
        if async_reset:
            clk = clock("clk", rst_n="resetn")
        else:
            clk = clock("clk", reset="reset")
        
        self.logic(clk)
        self.tb.gen_clk(clk, cycle=self.tb.rand_int(1, 20))
        
        
        args = adder.adder(self).gen_rand_args()
        num = args["num"]
        bits = args["bits"]
        float16 = args["float16"]
        
        self.logic("valid", initial=0)
        inputs = []
        for n in range(num):
            inputs.append(f"i{n}")
        self.logic(inputs, bits, initial=0)
        self.logic("o", bits)
        self.logic("valid_out")
            
        son = adder.adder(self).module(clk, **args)
        son.connect_in(clk)
        son.connect_in("valid")
        for n in range(num):
            son.connect_in(f"i{n}")
        son.connect_out("o")
        son.connect_out("valid_out")
        son.inst()
        
        
        self.logic("en", initial=0)
        self.tb.fifo("data_in_q", bits*num)
        self.tb.fifo("expected_q", bits)
        
        self.line(f"""
                    initial
                        begin
                   """)
        for i in range(size):
            input_vec = []
            input_sum = misc.cond(float16, np.float16(0), 0)
            for j in range(num):
                if float16:
                    val = np.float16(np.random.rand())
                else:
                    val = self.tb.rand_int(1<<bits)
                input_sum += val
                if float16:
                    val = val.view(np.uint16)
                    
                input_vec.append(misc.hex(val, bits))
            if float16:
                input_sum = input_sum.view(np.uint16)
            self.line(f"data_in_q.push_back({misc.concat(input_vec)});")
            self.line(f"expected_q.push_back({misc.hex(input_sum, bits)});")
        self.line(f"""
                        end
                   """)
        
        
        self.logic("data_in", bits*num, initial=0)
        self.logic("expected", bits, initial=0)
        if float16:
            err_margin = 16
            fail_condition = f"o > expected ? (o - expected) > {err_margin} : (expected - o) > {err_margin}" # allow margin since rtl module is not bit exact to numpy float16
        else:
            fail_condition = "o !== expected"
        self.line(f"""
                    initial
                        begin
                            {misc.cond(async_reset, f"@(posedge {clk.rst_n});")}
                            repeat (10) @(posedge {clk});
                            en = 1;
                        end
                        
                        // drive inputs
                        always @(posedge {clk})
                            if (en && (data_in_q.size() > 0))
                                begin
                                    data_in = data_in_q.pop_front();
                                    {misc.concat(inputs)} <= data_in;
                                    valid <= 1;
                                end
                                
                        // check output
                        always @(posedge {clk})
                            if (valid_out)
                                begin
                                    expected = expected_q.pop_front();
                                    {self.tb.test_fail(condition=fail_condition, message="mismatch expected: 0x%0h, actual: 0x%0h", params=["expected", "o"])}
                                    if (expected_q.size() == 0)
                                        {self.tb.test_pass(message=f"successfully tested {size} additions")}
                                end
                   """)
        
        
        self.allow_unused(["valid_out", "o", "data_in", "expected", "en"])
        
        
        self.tb.set_timeout(clk, size * 100)
        self.tb.dump()

        return self.write()
