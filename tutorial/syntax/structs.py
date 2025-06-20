
from p2v import p2v, misc, clock, default_clk

import axi

from copy import deepcopy

# basic struct with 2 data fields
basic = {}
basic["a"] = 8
basic["b"] = 4

# inherit basic struct and add field
basic_with_c = deepcopy(basic)
basic_with_c["c"] = 2


class structs(p2v):
    def module(self, clk=default_clk, addr_bits=32, data_bits=512):
        self.set_param(clk, clock)
        self.set_param(addr_bits, int, addr_bits > 0)
        self.set_param(data_bits, int, data_bits > 0 and misc.is_pow2(data_bits))
        self.set_modname()
        
        axi_strct = axi.axi(addr_bits=addr_bits, data_bits=data_bits, cache_bits=0, lock_bits=0, prot_bits=0)
        self.input(clk)
        
        
        # async assignment - full axi struct
        mstr0 = self.input("master0", axi_strct) # axi input port
        slv0 = self.output("slave0", axi_strct) # axi output port
        
        self.assign("slave0", "master0") # assign axi structs with change of write address
        
        
        # async assignment - full axi struct with field change
        self.input("write_addr", addr_bits)
        mstr1 = self.input("master1", axi_strct) # axi input port
        slv1 = self.output("slave1", axi_strct) # axi output port
        
        self.assign(slv1["aw"]["addr"], "write_addr") # assign awaddr field
        self.assign("slave1", "master1") # assign axi structs with change of write address
        self.allow_unused(mstr1["aw"]["addr"]) # don't give lint error on unused master awaddr
        
        
        # async assignment - sub structs one by one
        for x in ["aw", "w", "b", "ar", "r"]:
            self.input(f"master2_{x}", axi_strct[x]) # partial axi input port
            self.output(f"slave2_{x}", axi_strct[x]) # partial axi output port
            
            self.assign(f"slave2_{x}", f"master2_{x}")
        
        
        # sync assignment - sub structs one by one
        for x in axi_strct: # same as ["aw", "w", "b", "ar", "r"]:
            self.input(f"master3_{x}", axi_strct[x]) # partial axi input port
            self.output(f"slave3_{x}", axi_strct[x]) # partial axi output port
            
            self.sample(clk, f"slave3_{x}", f"master3_{x}")
                

        # basic struct
        self.input("bi", basic)
        self.output("bo", basic)
        self.assign("bo", "bi")
       
       
        # basic struct with additonla field c
        self.input("bci", basic_with_c)
        self.output("bco", basic_with_c)
        self.assign("bco", "bci")
       
       
        # casting between basic and basic_with_c
        cast_o = self.output("cast_o", basic_with_c)
        self.assign("cast_o", "bi")
        self.assign(cast_o["c"], "2'd2")
       
        return self.write()

