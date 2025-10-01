
# tb step 1: create a test bench that drives inputs and tests sum of adder

from p2v import p2v, misc

import adder
import test_din_dout

class tb_adder_elite(p2v):
    """ test bench for fixed point adder """
    def module(self, size=32):
        self.set_param(size, int, size > 0) # number of inputs to test
        self.set_modname("tb") # explicitly set module name


        # EXTRACT RTL PARAMETERS
        args = adder.adder(self).gen_rand_args(override={"float16":False})
        clk = args.clk
        num = args.num
        bits = args.bits


        # RANDOM TEST PARAMETERS
        cycle = self.tb.rand_int(2, 20)
        data = self.get_data(bits, num=num, size=size)
        bits_in = bits * num
        bits_out = bits


        # CLOCK AND RESET GENERATION
        self.logic(clk)
        self.tb.gen_clk(clk, cycle=cycle)


        # TEST
        data_in = self.logic(bits_in)
        valid = self.logic()
        data_out = self.logic(bits_out)
        valid_out = self.logic()
        son = test_din_dout.test_din_dout(self).module(clk, data=data, bits_in=bits_in, bits_out=bits_out, valid_busy=True, ready_busy=None)
        son.connect_in(clk)
        son.connect_in(son.en, 1)
        son.connect_out(son.data_in, data_in)
        son.connect_out(son.valid, valid)
        son.connect_in(son.data_out, data_out)
        son.connect_in(son.valid_out, valid_out)
        son.inst()


        # RTL
        son = adder.adder(self).module(**vars(args))
        son.connect_in(clk)
        son.connect_in(son.valid, valid)
        for n in range(num):
            son.connect_in(son.data_in[n], data_in[bits*n:bits*n+bits])
        son.connect_out(son.o, data_out)
        son.connect_out(son.valid_out, valid_out)
        son.inst()


        # TIMEOUT
        self.tb.set_timeout(clk, 10000)

        # DUMP
        self.tb.dump()


        return self.write()

    def get_data(self, bits, num=8, size=100):
        """ get test data as list of tuple (din, dout)"""

        data = []
        for _ in range(size):
            input_vec = []
            input_sum = 0
            for _ in range(num):
                val = self.tb.rand_int(1<<bits)
                input_sum += val
                input_vec.append(misc.hex(val, bits))
            din = misc.concat(input_vec)
            dout = misc.hex(input_sum % (1 << bits), bits)
            data.append((din, dout))
        return data
