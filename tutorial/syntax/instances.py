
from p2v import p2v

import _or_gate
import _or_gate_list
import _or_gate_dict

class instances(p2v):
    """ test instances """
    def module(self, num=4, bits=32):
        self.set_param(num, int, 0 < num < 8)
        self.set_param(bits, int, bits > 0)
        self.set_modname()


        a0 = {}
        b0 = {}
        c0 = {}
        for n in range(num):
            a0[n] = self.input(bits+n)
            b0[n] = self.input(bits+n)
            c0[n] = self.output(bits+n)

            son = _or_gate._or_gate(self).module(bits=bits+n) # creates son module
            son.connect_in(son.a, a0[n])
            son.connect_in(son.b, b0[n])
            son.connect_out(son.c, c0[n])
            son.inst(suffix=n) # make instance name unique


        al = {}
        for n in range(num):
            al[n] = self.input(bits)
        cl = self.output(bits)
        son = _or_gate_list._or_gate_list(self).module(num=num, bits=bits)
        for n in range(num):
            son.connect_in(son.i[n], al[n])
        son.connect_out(son.c, cl)
        son.inst()

        a2 = {}
        c2 = {}
        for n in range(num):
            a2[n] = {}
            for x in ["w", "r"]:
                a2[n][x] = self.input(bits)
            c2[n] = self.output(bits)
        son = _or_gate_dict._or_gate_dict(self).module(num=num, bits=bits)
        for n in range(num):
            for x in ["w", "r"]:
                son.connect_in(son.i[n][x], a2[n][x])
            son.connect_out(son.c[n], c2[n])
        son.inst()

        a = self.input(16)
        b = self.input(16)
        c = self.output(16)
        son = _or_gate._or_gate(self).module(bits=16)
        son.connect_in(son.a, a) # assumes wire name equals port name
        son.connect_in(son.b, b) # assumes wire name equals port name
        son.connect_out(son.c, c) # assumes wire name equals port name
        son.inst("my_or_gate") # specific instance name


        ca = self.output(16)
        son = _or_gate._or_gate(self).module(bits=16)
        son.connect_out(son.c, ca)
        son.connect_auto() # trivially connects all missing ports (wire name equals port name)
        son.inst("my_auto_connect_or") # specific instance name


        son = _or_gate._or_gate(self).module(bits=16)
        son.connect_auto(ports=True, suffix="_01") #
        son.inst("my_auto_connect_ports_or") # specific instance name


        # Verilog instance
        aa = self.input(bits)
        bb = self.input(bits)
        cc = self.output(bits)
        son = self.verilog_module("_and_gate", params={"BITS":bits}) # setting instance Verilog parameter
        son.connect_in(son.a, aa) # connecting Verilog is same as connecting a p2v instance
        son.connect_in(son.b, bb) # connecting Verilog is same as connecting a p2v instance
        son.connect_out(son.c, cc) # connecting Verilog is same as connecting a p2v instance
        son.inst() # instance name equals module name

        return self.write()
