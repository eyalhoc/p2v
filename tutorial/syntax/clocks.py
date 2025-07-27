
from p2v import p2v, clock, default_clk, clk_0rst, clk_arst, clk_srst, clk_2rst

class clocks(p2v):
    def module(self, clk=default_clk):
        self.set_param(clk, clock) # verifies that clk if a p2v clock
        self.set_modname()
        
        clks = [clk] # default clk with async reset
        clks.append(clock("clk0")) # clock without reset
        clks.append(clock("clk1", rst_n="clk1_rst_n")) # clk with async reset
        clks.append(clock("clk2", reset="clk2_reset")) # clk with sync reset
        clks.append(clock("clk3", rst_n="clk3_rst_n", reset="clk3_reset")) # clk with both asycn and sync reset
        clks.append(clk_0rst("clk4")) # clk with no resets
        clks.append(clk_arst("clk5")) # clk with async reset
        clks.append(clk_srst("clk6")) # clk with sync reset
        clks.append(clk_2rst("clk7")) # clk with async and sync resets
        clks.append(self.tb.rand_clock(prefix="clk8")) # clk with random resets
        clks.append(self.tb.rand_clock(prefix="clk9", must_have_reset=True)) # clk with random resets
        
        i = {}
        o = {}
        num = len(clks)
        for n in range(num):
            self.input(clks[n])
            i[n] = self.input(32)
            o[n] = self.output(32)
           
            self.sample(clks[n], o[n], i[n])
        
        return self.write()

