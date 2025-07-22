
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
        mstr0 = self.input(axi_strct) # axi input port
        slv0 = self.output(axi_strct) # axi output port
        
        self.assign(slv0, mstr0) # assign axi structs with change of write address
        
        
        # async assignment - full axi struct with field change
        write_addr = self.input(addr_bits)
        mstr1 = self.input(axi_strct) # axi input port
        slv1 = self.output(axi_strct) # axi output port
        
        self.assign(slv1.aw.addr, write_addr) # assign awaddr field
        self.assign(slv1, mstr1) # assign axi structs with change of write address
        self.allow_unused(mstr1.aw.addr) # don't give lint error on unused master awaddr
        
        
        # async assignment - sub structs one by one
        master2 = {}
        slave2 = {}
        for x in ["aw", "w", "b", "ar", "r"]:
            master2[x] = self.input(f"master2_{x}", axi_strct[x]) # partial axi input port
            slave2[x] = self.output(f"slave2_{x}", axi_strct[x]) # partial axi output port
            
            self.assign(slave2[x], master2[x])
        
        
        # sync assignment - sub structs one by one
        master3 = {}
        slave3 = {}
        for x in axi_strct: # same as ["aw", "w", "b", "ar", "r"]:
            master3[x] = self.input(f"master3_{x}", axi_strct[x]) # partial axi input port
            slave3[x] = self.output(f"slave3_{x}", axi_strct[x]) # partial axi output port
            
            self.sample(clk, slave3[x], master3[x])
                

        # basic struct
        bi = self.input(basic)
        bo = self.output(basic)
        self.assign(bo, bi)
       
       
        # basic struct with additonla field c
        bci = self.input(basic_with_c)
        bco = self.output(basic_with_c)
        self.assign(bco, bci)
       
       
        # casting between basic and basic_with_c
        cast_o = self.output(basic_with_c)
        self.assign(cast_o, bi)
        self.assign(cast_o.c, 2)
       
        return self.write()

