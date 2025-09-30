# -----------------------------------------------------------------------------
#  Copyright (C) 2025 Eyal Hochberg (eyalhoc@gmail.com)
#
#  This file is part of an open-source Python-to-Verilog synthesizable converter.
#
#  Licensed under the GNU General Public License v3.0 or later (GPL-3.0-or-later).
#  You may use, modify, and distribute this software in accordance with the GPL-3.0 terms.
#
#  This software is distributed WITHOUT ANY WARRANTY; without even the implied
#  warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
#  GPL-3.0 license for full details: https://www.gnu.org/licenses/gpl-3.0.html
# -----------------------------------------------------------------------------

# pylint: disable=too-few-public-methods
class p2v_pipe:
    """
    This class is a p2v pipline.
    """

    def __init__(self, parent, clk, valid, ready=None, bypass=False):
        self.parent = parent
        self.clk = clk
        self.valid = valid
        self.ready = ready
        self.bypass = bypass

        self.stage_valid = valid
        if ready is not None:
            self.parent._set_used(ready)


    def advance(self, bypass=False):
        """ advance pipeline stage """
        if not bypass:
            self.stage_valid = self._sample(self.valid, stage=self.parent._pipe_stage)
            self.parent._pipe_stage += 1
        return self.stage_valid


    def _get_delay_name(self, name, stage):
        name = str(name)
        if stage == 0:
            return name

        if not name.startswith("_"):
            name = f"_{name}"
        return f"{name}_d{stage}"

    def _get_signal(self, name, stage=0):
        name_d = self._get_delay_name(name, stage=stage)
        return self.parent._signals[name_d]

    def _signal_exists(self, name, stage=0):
        name_d = self._get_delay_name(name, stage=stage)
        return name_d in self.parent._signals

    def _sample(self, name, bits=1, stage=0):
        src = self._get_signal(name, stage=stage)
        if self.bypass:
            return src

        tgt_name = self._get_delay_name(name, stage=stage+1)
        src_name = src._name
        tgt = self.parent.logic(tgt_name, bits=bits, _allow_str=True)
        tgt._strct = src._strct
        tgt._pipe_stage += 1
        self.parent._signals[tgt_name]._strct = tgt._strct
        
        # valid signal
        if name == str(self.valid):
            if self.ready is not None:
                valid = f"{self.ready} | ~{src_name}" # allow valid to go high when waiting on ready
            else:
                valid = None
        else:
            valid = self._get_delay_name(self.valid, stage=stage)
            if self.ready is not None:
                valid = f"{valid} & {self.ready}"

        self.parent.sample(self.clk, tgt_name, src_name, valid=valid, _allow_str=True)
        return tgt
