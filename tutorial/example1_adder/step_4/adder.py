
# step 1: create a module that receives two 8 bit inputs and outputs the sum
# step 2: make the number of bits parametric
# step 3: add a clock and sample the output
# step 4: build a binary adder tree

from p2v import p2v, misc, clock, default_clk # misc provides general purpose functions

class adder(p2v):
    def module(self, clk=default_clk, bits=8, num=8):
        self.set_param(clk, clock)
        self.set_param(bits, int, bits > 0) # data width
        self.set_param(num, int, num > 0 and misc.is_pow2(num)) # number of inputs
        self.set_modname()
        
        self.input(clk)
        
        valid = self.input()
        data_in = []
        for n in range(num):
            data_in.append(self.input(f"i{n}", bits))
        o = self.output(bits)
        valid_out = self.output()
        
        if num == 2:            
            self.sample(clk, o, data_in[0] + data_in[1], valid=valid)
            self.sample(clk, valid_out, valid)

        
        else:
            son_num = num // 2
            data_out = []
            valid_out = []
            for i in range(2):
                data_out.append(self.logic(f"o{i}", bits))
                valid_out.append(self.logic(f"valid_out{i}"))
                
                son = adder(self).module(clk, bits=bits, num=son_num)
                son.connect_in(clk)
                son.connect_in("valid") # assumes port name equals wire name
                for n in range(son_num):
                    son.connect_in(f"i{n}", data_in[son_num*i+n])
                son.connect_out("o", data_out[i])
                son.connect_out("valid_out", valid_out[i])
                son.inst(suffix=i)
        
        
            # add the results
            son = adder(self).module(clk, bits=bits, num=2)
            son.connect_in(clk)
            son.connect_in("valid", valid_out[0] & valid_out[1])
            son.connect_in("i0", data_out[0])
            son.connect_in("i1", data_out[1])
            son.connect_out("o")
            son.connect_out("valid_out")
            son.inst(suffix="_out")
            
        
        return self.write()

