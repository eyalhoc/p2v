
from p2v import p2v, misc

class _or_gate_dict(p2v):
    """ logical or gate between multiple inputs (implemented as dict) """
    def module(self, num=2, bits=8):
        self.set_param(num, int, num > 0) # number of inputs
        self.set_param(bits, int, bits > 0) # data width
        self.set_modname()

        i = {}
        c = {}
        for n in range(num):
            i[n] = {}
            for x in ["w", "r"]:
                i[n][x] = self.input(bits)
            c[n] = self.output(bits)

        for n in range(num):
            self.assign(c[n], misc.concat(i[n], sep="|"))

        return self.write()
