
from p2v import p2v, misc, clock, default_clk

class fsms(p2v):
    def module(self, clk=default_clk):
        self.set_param(clk, clock)
        self.set_modname()

        my_fsm = self.enum(["START", "WAIT", "STOP"])

        self.input(clk)
        a = self.input()
        b = self.input()
        state = self.output(my_fsm)
        

        fsm = self.fsm(clk, my_fsm, reset_val=my_fsm.START)
        fsm.transition(my_fsm.START, misc.cond(a, my_fsm.WAIT, my_fsm.START))
        fsm.transition(my_fsm.WAIT, misc.cond(b, my_fsm.STOP, my_fsm.WAIT))
        fsm.transition(my_fsm.STOP, my_fsm.START)
        fsm.end()
        
        self.assign(state, fsm.state)
        
        return self.write()
