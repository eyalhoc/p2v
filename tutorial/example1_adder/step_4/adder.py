
# step 1: create a module that receives two 8 bit inputs and outputs the sum
# step 2: make the number of bits parametric
# step 3: add a clock and sample the output
# step 4: build a binary adder tree

from p2v import p2v, misc, clock, default_clk # misc provides general purpose functions

class adder(p2v):
    def module(self, clk=default_clk, bits=8, num=8):
        self.set_param(clk, clock)
        self.set_param(bits, int, bits > 0, remark="data width")
        self.set_param(num, int, num > 0 and misc.is_pow2(num), remark="number of inputs")
        self.set_modname()
        
        self.input(clk)
        
        self.input("valid")
        for n in range(num):
            self.input(f"i{n}", bits)
        self.output("o", bits)
        self.output("valid_out")
        
        if num == 2:            
            self.sample(clk, "o", "i0 + i1", valid="valid")
            self.sample(clk, "valid_out", "valid")

        
        else:
            son_num = num // 2
            for i in range(2):
                self.logic(f"o{i}", bits)
                self.logic(f"valid_out{i}")
                
                son = adder(self).module(clk, bits=bits, num=son_num)
                son.connect_in(clk)
                son.connect_in("valid") # assumes port name equals wire name
                for n in range(son_num):
                    son.connect_in(f"i{n}", f"i{son_num*i+n}")
                son.connect_out("o", f"o{i}")
                son.connect_out("valid_out", f"valid_out{i}")
                son.inst(suffix=i)
        
        
            # add the results
            son = adder(self).module(clk, bits=bits, num=2)
            son.connect_in(clk)
            son.connect_in("valid", "valid_out0 & valid_out1")
            son.connect_in("i0", "o0")
            son.connect_in("i1", "o1")
            son.connect_out("o")
            son.connect_out("valid_out")
            son.inst(suffix="_out")
            
        
        return self.write()

