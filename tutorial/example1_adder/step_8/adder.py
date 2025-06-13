
# step 1: create a module that receives two 8 bit inputs and outputs the sum
# step 2: make the number of bits parametric
# step 3: add a clock and sample the output
# step 4: build a binary adder tree
# step 5: generate random permutations to check robustness of code
# step 6: support float16 adder
# step 7: create a test bench that drives inputs and tests sum of adder
# step 8: support float16

from p2v import p2v, misc, clock, default_clk

class adder(p2v):
    def module(self, clk=default_clk, bits=8, num=32, float16=False):
        self.set_param(clk, clock)
        self.set_param(bits, int, bits > 0, remark="data width")
        self.set_param(num, int, num > 0 and misc.is_pow2(num), remark="number of inputs")
        self.set_param(float16, bool, remark="use a float16 adder")
        self.set_modname()
        
        if float16:
            self.assert_static(bits == 16, "float type only supports float16")
            
        
        self.input(clk)
        
        self.input("valid")
        for n in range(num):
            self.input(f"i{n}", bits)
        self.output("o", bits)
        self.output("valid_out")
        
        if num == 2:                
            self.logic("o_pre", bits)
            if float16:
                float16_stat = ["overflow", "zero", "NaN", "precisionLost"]
                self.logic(float16_stat)
                
                son = self.verilog_module("float_adder")
                son.connect_in("num1", "i0")
                son.connect_in("num2", "i1")
                son.connect_out("result", "o_pre")
                for stat in float16_stat:
                    son.connect_out(stat)
                son.inst()
                
                for stat in float16_stat:
                    if stat not in ["precisionLost"]:
                        self.assert_never(clk, stat, f"received unexpected {stat}")
                    else:
                        self.allow_unused(stat)
            else:
                self.assign("o_pre", "i0 + i1")
                
            self.sample(clk, "o", "o_pre", valid="valid")
            self.sample(clk, "valid_out", "valid")

        else:
            son_num = num // 2
            for i in range(2):
                self.logic(f"o{i}", bits)
                self.logic(f"valid_out{i}")
                
                son = adder(self).module(clk, bits=bits, num=son_num, float16=float16)
                son.connect_in(clk)
                son.connect_in("valid")
                for n in range(son_num):
                    son.connect_in(f"i{n}", f"i{son_num*i+n}")
                son.connect_out("o", f"o{i}")
                son.connect_out("valid_out", f"valid_out{i}")
                son.inst(suffix=i)
        
        
            # add the results
            son = adder(self).module(clk, bits=bits, num=2, float16=float16)
            son.connect_in(clk)
            son.connect_in("valid", "valid_out0 & valid_out1")
            son.connect_in("i0", "o0")
            son.connect_in("i1", "o1")
            son.connect_out("o")
            son.connect_out("valid_out")
            son.inst(suffix="_out")
            
        
        return self.write()


    def gen(self):
        args = {}
        args["float16"] = self.tb.rand_bool()
        if args["float16"]:
            args["bits"] = 16
        else:
            args["bits"] = self.tb.rand_int(1, 128)
        args["num"] = 1 << self.tb.rand_int(1, 8)
        return args
        