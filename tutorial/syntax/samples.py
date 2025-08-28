
from p2v import p2v, misc, clock

bits = 8

strct_handshake = {}
strct_handshake["ctrl"] = 8
strct_handshake["data"] = 32
strct_handshake["valid"] = 1.0 # value reserved to mark qualifier
strct_handshake["ready"] = -1.0 # value reserved to mark back pressure


class samples(p2v):
    """ test samples """
    def module(self):
        self.set_modname()

        clk0 = clock("clk0", rst_n="clk0_rst_n") # clk with async reset
        clk1 = clock("clk1", reset="clk1_reset") # clk with sync reset
        self.input(clk0)
        self.input(clk1)

        ext_reset = self.input()

        valid = self.input()
        i0 = self.input(bits)
        x0 = self.output(bits)
        x1 = self.output(bits)
        x2 = self.output(bits)
        x3 = self.output(bits)
        x4 = self.output(bits)

        s = self.input(strct_handshake)
        t = self.output(strct_handshake)

        self.sample(clk0, x0, i0) # free running clock - async reset

        self.sample(clk1, x1, i0) # free running clock - sync reset

        self.sample(clk0, x2, i0, valid=valid) # sample with qualifier

        self.sample(clk0, x3, i0, valid=valid, reset_val=-1) # sample with non zero reset value

        self.sample(clk0, x4, i0, valid=valid, reset=ext_reset) # sample with additional sync reset

        self.sample(clk1, t.ctrl, s.ctrl | misc.hex(4, bits=8), valid=valid)
        self.sample(clk1, t, s) # sample structs


        return self.write()
