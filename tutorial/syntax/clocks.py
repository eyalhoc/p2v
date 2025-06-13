
from p2v import p2v, clock, default_clk

class clocks(p2v):
    def module(self, clk=default_clk):
        self.set_param(clk, clock) # verifies that clk if a p2v clock
        self.set_modname()
        
        clks = [clk]
        clks.append(clock("clk0")) # clock without reset
        clks.append(clock("clk1", rst_n="clk1_rst_n")) # clk with async reset
        clks.append(clock("clk2", reset="clk2_reset")) # clk with sync reset
        clks.append(clock("clk3", rst_n="clk3_rst_n", reset="clk3_reset")) # clk with both asycn and sync reset
        
        num = len(clks)
        for n in range(num):
            self.input(clks[n])
            self.input(f"i{n}", 32)
            self.output(f"o{n}", 32)
           
            self.sample(clks[n], f"o{n}", f"i{n}")
        
        return self.write()

