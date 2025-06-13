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

from copy import deepcopy

FIELD_SEP = "__"

class p2v_struct():

    def __init__(self, parent, name, fields):
        self._parent = parent
        
        self.data_names = self.name_fields(name, fields, data_only=True)
        self.ctrl_names = self.name_fields(name, fields, ctrl_only=True)
        self.names = self.name_fields(name, fields)
        
        self._data_fields = self.prefix_fields(name, fields, data_only=True)
        self._ctrl_fields = self.prefix_fields(name, fields, ctrl_only=True)
        self.fields = self.prefix_fields(name, fields)
        
        self.valid = self.ready = None
        for name in self._ctrl_fields:
            if self._ctrl_fields[name] == 1.0:
                self.valid = name
            elif self._ctrl_fields[name] == -1.0:
                self.ready = name
            
    def _name_fields(self, name, fields, data_only=False, ctrl_only=False):
        remove = []
        for key, value in fields.items():
            field_name = self.get_field_name(name, key)
            if type(value) is dict:
                self._name_fields(field_name, value, data_only=data_only, ctrl_only=ctrl_only)
            elif type(value) is float and data_only:
                remove.append(key)
            elif type(value) is not float and ctrl_only:
                remove.append(key)
            else:
                fields[key] = field_name
        for key in remove:
            del fields[key]
        return fields


    def get_names(self, data=True, ctrl=True):
        if data and ctrl:
            return list(self.names.values())
        elif data:
            return list(self.data_names.values())
        elif ctrl:
            return list(self.ctrl_names.values())
        
    def get_field_name(self, name, field_name):
        if FIELD_SEP in name:
            sep = ""
        else:
            sep = FIELD_SEP
        return f"{name}{sep}{field_name}"

    def update_field_name(self, name, field_name):
        field_name = field_name.split(FIELD_SEP)[-1]
        return self.get_field_name(name, field_name)

    def prefix_fields(self, name, fields, data_only=False, ctrl_only=False):
        valid = ready = None
        new_fields = {}
        for field_name in fields:
            bits = fields[field_name]
            full_field_name = self.get_field_name(name, field_name)
            if type(bits) is dict:
                son_fields = self.prefix_fields(full_field_name, bits, data_only=data_only, ctrl_only=ctrl_only)
                for son_name in son_fields:
                    new_fields[son_name] = son_fields[son_name]
            else:
                if type(bits) is float:
                    if data_only:
                        continue
                    
                    if bits == 1.0:
                        assert valid is None, f"struct {name} has multiple valid signals (bits = 1.0)"
                        valid = full_field_name
                    elif bits == -1.0:
                        assert ready is None, f"struct {name} has multiple ready signals (bits = -1.0)"
                        ready = full_field_name
                elif bits != 0:
                    new_fields[full_field_name] = bits
        if not data_only:
            if valid is not None:
                new_fields[valid] = 1.0
            if ready is not None:
                new_fields[ready] = -1.0
        return new_fields
        
    def name_fields(self, name, fields, data_only=False, ctrl_only=False):
        return self._name_fields(name, deepcopy(fields), data_only=data_only, ctrl_only=ctrl_only)
        