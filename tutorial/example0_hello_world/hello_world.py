from p2v import p2v

class hello_world(p2v):
    def module(self):
        self.set_modname()

        a = self.input()
        b = self.input()
        o = self.output()

        self.assign(o, a | b)

        return self.write()

