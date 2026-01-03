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

from p2v_signal import p2v_signal

# pylint: disable=too-few-public-methods
class p2v_pipe:
    """
    This class is a p2v pipline.
    """

    def __init__(self, parent, clk, valid, ready=None, bypass=False, debug=False):
        self._parent = parent
        self._clk = clk
        self._valid = valid
        self._ready = ready
        self._bypass = bypass
        self._debug = debug

        self._stage_valid = valid
        self._stage_valid._const = True
        if ready is not None:
            self._parent._set_used(ready)
            ready._const = True
        if debug:
            self._stage_cnt()


    def valid(self):
        """ get pipeline valid signal """
        return self._stage_valid

    def end(self):
        """ close pipeline """
        del self._parent._pipelines[self._valid]
        self._stage_valid._initial_pipe_stage = -1
        return self.valid()

    def advance(self, num=1, bypass=False):
        """ advance pipeline stage """
        if not self._bypass:
            if isinstance(num, p2v_signal):
                self._parent._set_used(num)
                num = num._pipe_stage
            self._parent._assert(self._valid in self._parent._pipelines, "trying to advance undeclared pipeline", fatal=True)
            self._parent._assert(self._parent._pipelines[self._valid] is not None, "trying to advance a closed pipeline", fatal=True)
            if not bypass:
                if self._parent._pipe_stage == 0:
                    delay_name = self._get_delay_name(self._valid, self._parent._pipe_stage)
                    signal = self._parent.logic(delay_name, assign=self._valid, _allow_str=True)
                    signal._const = True # don't expect .pipe()
                self._stage_valid = self._sample(self._valid, stage=self._parent._pipe_stage)
                self._stage_valid._const = True
                self._parent._pipe_stage += 1
                if self._debug:
                    self._stage_cnt()
                self._parent.line("")
                self._parent.remark("=" * 32)
                self._parent.remark(f" ==== PIPELINE STAGE {self._parent._pipe_stage}")
                self._parent.remark("=" * 32)
                self._parent.line("")
                if num > 1:
                    self.advance(num-1)
        return self._stage_valid

    def _stage_cnt(self):
        self._parent.tb.syn_off()
        cnt_name = self._get_delay_name("stage_cnt", self._parent._pipe_stage)
        signal = self._parent.logic(cnt_name, 8, initial=0, _allow_str=True)
        signal._const = True # don't expect .pipe()
        valid = self._stage_valid
        if self._ready is not None:
            valid = f"{valid} & {self._ready}"
        self._parent.line(f"""always @(posedge {self._clk})
                                 if ({valid})
                                     {cnt_name} = {cnt_name} + 1;
                          """)
        self._parent._set_used(cnt_name)
        self._parent.tb.syn_on()

    def _get_delay_name(self, name, stage):
        name = str(name)
        if not name.startswith("_"):
            name = f"_{name}"
        return f"{name}_d{stage}"

    def _get_orig_name(self, name):
        if name.startswith("_"):
            name = name.replace("_", "", 1)
        if "_d" in name:
            stage = name.split("_d")[-1]
            if stage.isdigit():
                name = name[:-len(f"_d{stage}")]
        return name

    def _get_signal(self, name, stage=0):
        if self._bypass:
            return self._parent._signals[str(name)]
        name_d = self._get_delay_name(name, stage=stage)
        return self._parent._signals[name_d]

    def _signal_exists(self, name, stage=0):
        name_d = self._get_delay_name(name, stage=stage)
        return name_d in self._parent._signals

    def _sample(self, name, bits=1, stage=0):
        src = self._get_signal(name, stage=stage)
        if self._bypass:
            return src

        tgt_name = self._get_delay_name(name, stage=stage+1)
        src_name = src._name
        tgt = self._parent.logic(tgt_name, bits=bits, _allow_str=True)
        tgt._strct = src._strct
        tgt._pipe_stage += 1
        self._parent._signals[tgt_name]._strct = tgt._strct

        # valid signal
        if name == str(self._valid):
            valid = self._ready
        else:
            valid = self._get_delay_name(self._valid, stage=stage)
            if self._ready is not None:
                valid = f"{valid} & {self._ready}"

        self._parent.sample(self._clk, tgt_name, src_name, valid=valid, _allow_str=True)
        return tgt
