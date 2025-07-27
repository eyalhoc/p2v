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

"""
p2v_clock module
"""

from p2v_signal import p2v_signal

class p2v_fsm:
    """
    This class is a p2v state machine.
    """

    def __init__(self, parent, clk, enum, reset_val=None):
        self._parent = parent
        self._clk = clk
        self._enum = enum
        self._reset_val = reset_val

        self._transitions = {}
        self.state = None
        self.next_state = None

    def transition(self, state, next_state):
        """
        Sets state machine transition.

        Args:
            state(p2v_signal): present state
            next_state(p2v_signal): next state

        Returns:
            None
        """
        self._parent._assert_type(state, p2v_signal)
        self._parent._assert_type(next_state, p2v_signal)
        state = str(state)
        self._parent._assert(state not in self._transitions, f"transition for state {state} was previously defined")
        self._transitions[state] = next_state
        self._parent._set_used(next_state)

    def end(self, suffix=""):
        """
        Ends state machine decleration and inserts lines to module.

        Args:
            suffix(str): state machine suffix to all used logic.

        Returns:
            None
        """
        self._parent._assert_type(suffix, str)

        fsm_name = f"fsm_{self._enum.NAME}{suffix}"
        self.state = self._parent.logic(f"{fsm_name}_ps", self._enum, _allow_str=True)
        self.next_state = self._parent.logic(f"{fsm_name}_ns", self._enum, _allow_str=True)

        self._parent._set_used(self.state)
        self._parent._set_driven(self.next_state)
        self._parent.line(f"""
                         always_comb
                             begin
                                 case({fsm_name}_ps)
                          """)

        for state, next_state in self._transitions.items():
            self._parent._set_used(state)
            self._parent.line(f"{state} : {fsm_name}_ns = {next_state};")


        self._parent.line(f"""
                                     default : {fsm_name}_ns = 'x;
                                 endcase
                             end // {fsm_name}
                         """)

        self._parent.sample(self._clk, self.state, self.next_state, reset_val=self._reset_val)
