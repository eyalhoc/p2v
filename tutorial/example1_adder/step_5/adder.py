
# step 1: create a module that receives two 8 bit inputs and outputs the sum
# step 2: make the number of bits parametric
# step 3: add a clock and sample the output
# step 4: build a binary adder tree
# step 5: generate random permutations to check robustness of code

from p2v import p2v, misc, clock, default_clk

class adder(p2v):
    """ fixed point adder """
    def module(self, clk=default_clk, bits=8, num=32):
        self.set_param(clk, clock)
        self.set_param(bits, int, bits > 0) # data width
        self.set_param(num, int, num > 0 and misc.is_pow2(num)) # number of inputs
        self.set_modname()

        self.input(clk)

        valid = self.input()
        data_in = {}
        for n in range(num):
            data_in[n] = self.input(bits)
        o = self.output(bits)
        valid_out = self.output()

        if num == 2:
            self.sample(clk, o, data_in[0] + data_in[1], valid=valid)
            self.sample(clk, valid_out, valid)


        else:
            son_num = num // 2
            datas = [None] * 2
            valids = [None] * 2
            for i in range(2):
                datas[i] = self.logic(bits)
                valids[i] = self.logic()
                son = adder(self).module(clk, bits=bits, num=son_num)
                son.connect_in(clk)
                son.connect_in(valid) # assumes port name equals wire name
                for n in range(son_num):
                    son.connect_in(son.data_in[n], data_in[son_num*i+n])
                son.connect_out(son.o, datas[i])
                son.connect_out(son.valid_out, valids[i])
                son.inst(suffix=i)


            # add the results
            son = adder(self).module(clk, bits=bits, num=2)
            son.connect_in(clk)
            son.connect_in(son.valid, valids[0] & valids[1])
            son.connect_in(son.data_in[0], datas[0])
            son.connect_in(son.data_in[1], datas[1])
            son.connect_out(o)
            son.connect_out(valid_out)
            son.inst(suffix="_out")


        return self.write()


    def gen(self):
        """ random module parameters """
        args = self.gen_args()
        args.bits = self.tb.rand_int(1, 128)
        args.num = 1 << self.tb.rand_int(1, 8)
        return args
