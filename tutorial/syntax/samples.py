
from p2v import p2v, misc, clock, default_clk

bits = 8

strct_handshake = {}
strct_handshake["ctrl"] = 8
strct_handshake["data"] = 32
strct_handshake["valid"] = 1.0 # value reserevd to mark qualifier
strct_handshake["ready"] = -1.0 # value reserevd to mark back pressure


class samples(p2v):
    def module(self):
        self.set_modname()
        
        clk0 = clock("clk0", rst_n="clk0_rst_n") # clk with async reset
        clk1 = clock("clk1", reset="clk1_reset") # clk with sync reset
        self.input(clk0)
        self.input(clk1)
        
        self.input("valid")
        self.input("i0", bits)
        self.output("x0", bits)
        self.output("x1", bits)
        self.output("x2", bits)
        self.output("x3", bits)
        
        s = self.input("s", strct_handshake)
        t = self.output("t", strct_handshake)
        
        self.sample(clk0, "x0", "i0") # free running clock - async reset
        
        self.sample(clk1, "x1", "i0") # free running clock - sync reset
        
        self.sample(clk0, "x2", "i0", valid="valid") # sample with qualifier
        
        self.sample(clk0, "x3", "i0", valid="valid", reset_val=-1) # sample with non zero reset value

        
        self.sample(clk1, t["ctrl"], f"{s['ctrl']} | 8'h4", valid="valid")
        self.sample(clk1, "t", "s") # sample structs
        
        
        return self.write()

