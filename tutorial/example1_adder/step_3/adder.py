
# step 1: create a module that receives two 8 bit inputs and outputs the sum
# step 2: make the number of bits parametric
# step 3: add a clock and sample the output

from p2v import p2v, clock, default_clk

class adder(p2v):
    """ fixed point adder """
    def module(self, clk=default_clk, bits=8):
        self.set_param(clk, clock)
        self.set_param(bits, int, bits > 0) # data width
        self.set_modname()

        self.input(clk) # default clock uses an async reset

        valid = self.input() # default width is 1 bit
        a = self.input(bits)
        b = self.input(bits)
        o = self.output(bits)
        valid_out = self.output()

        self.sample(clk, o, a + b, valid=valid)
        self.sample(clk, valid_out, valid)

        return self.write()
