
# tb step 1: create a test bench that drives inputs and tests sum of adder

from p2v import p2v, misc, clock

import adder

class tb_adder(p2v):
    """ test bench for fixed point adder """
    def module(self, async_reset=True, size=32):
        self.set_param(async_reset, bool) # sync reset or async reset
        self.set_param(size, int, size > 0) # number of inputs to test
        self.set_modname("tb") # explicitly set module name

        if async_reset:
            clk = clock("clk", rst_n="resetn")
        else:
            clk = clock("clk", reset="reset")

        self.logic(clk)
        self.tb.gen_clk(clk, cycle=self.tb.rand_int(2, 20))
        reset_released = self.tb.reset_released(clk)


        args = adder.adder(self).gen_rand_args(override={"clk":clk, "float16":False})
        num = args.num
        bits = args.bits

        valid = self.logic(initial=0)
        inputs = {}
        for n in range(num):
            inputs[n] = self.logic(bits)
        o = self.logic(bits)
        valid_out = self.logic()

        son = adder.adder(self).module(**vars(args))
        son.connect_in(clk)
        son.connect_in(valid)
        for n in range(num):
            son.connect_in(son.data_in[n], inputs[n])
        son.connect_out(o)
        son.connect_out(valid_out)
        son.inst()


        data_in_q = self.tb.fifo(bits*num) # pylint: disable=unused-variable
        expected_q = self.tb.fifo(bits) # pylint: disable=unused-variable


        # INPUT AND OUTPUT DATA FIFOS
        self.tb.initial()
        for _ in range(size):
            input_vec = []
            input_sum = 0
            for _ in range(num):
                val = self.tb.rand_int(1<<bits)
                input_sum += val
                input_vec.append(misc.hex(int(val), bits))
            data_in_q.push(misc.concat(input_vec))
            expected_q.push(misc.hex(int(input_sum) & ((1 << bits) - 1), bits))
        self.tb.end()


        # PUSH INPUTS
        data_in = self.logic(bits*num, initial=0)
        self.tb.always(clk, cond=reset_released & ~data_in_q.empty(), posedge=False)
        self.assign(data_in, data_in_q.pop())
        self.assign(valid, ~data_in_q.empty())
        self.tb.end()
        self.assign(misc.concat(inputs), data_in)


        # POP EXPECTED
        expected = self.logic(bits, initial=expected_q.pop())
        self.tb.always(clk, cond=valid_out)
        self.assign(expected, expected_q.pop())
        self.tb.end()


        # END TEST
        self.tb.always(clk, cond=data_in_q.empty())
        self.tb.test_pass()
        self.tb.end()


        # COMPARE OUTPUT TO EXPECTED
        diff = self.logic(assign=valid_out & (o != expected))

        self.assert_property(clk, ~diff, misc.format_str("mismatch: expected=0x%0h, actual=0x%0h", params=[expected, o]))


        # TIMEOUT AND DUMP
        self.tb.set_timeout(clk, size * 16)
        self.tb.dump()

        return self.write()
