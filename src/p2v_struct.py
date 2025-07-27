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
p2v_struct module. Responsible for creating p2v structs.
"""

from copy import deepcopy

FIELD_SEP = "__"

class p2v_struct():
    """
    This class is a p2v struct.
    """

    def __init__(self, parent, name, fields):
        self._parent = parent

        self.data_names = self.name_fields(name, fields, data_only=True)
        self.ctrl_names = self.name_fields(name, fields, ctrl_only=True)
        self.names = self.name_fields(name, fields)

        self._data_fields = self.prefix_fields(name, fields, data_only=True)
        self._ctrl_fields = self.prefix_fields(name, fields, ctrl_only=True)
        self.fields = self.prefix_fields(name, fields)

        self.valid = self.ready = None
        for field_name, val in self._ctrl_fields.items():
            if val == 1.0:
                self.valid = field_name
            elif val == -1.0:
                self.ready = field_name

    def _name_fields(self, name, fields, data_only=False, ctrl_only=False):
        remove = []
        for key, value in fields.items():
            field_name = self.get_field_name(name, key)
            if isinstance(value, dict):
                self._name_fields(field_name, value, data_only=data_only, ctrl_only=ctrl_only)
            elif isinstance(value, float) and data_only:
                remove.append(key)
            elif not isinstance(value, float) and ctrl_only:
                remove.append(key)
            else:
                fields[key] = field_name
        for key in remove:
            del fields[key]
        return fields


    def get_names(self, data=True, ctrl=True):
        """
        Returns a list of struct field names.

        Args:
            data(bool): return data fields
            ctrl(bool): return control fields

        Returns:
            list
        """
        if data and ctrl:
            return list(self.names.values())
        if data:
            return list(self.data_names.values())
        if ctrl:
            return list(self.ctrl_names.values())
        return []

    def get_field_name(self, name, field_name):
        """
        Build full struct field name for Verilog signal.

        Args:
            name(str): struct name
            field_name(str): field name

        Returns:
            str
        """
        name = str(name)
        if FIELD_SEP in name:
            sep = ""
        else:
            sep = FIELD_SEP
        return f"{name}{sep}{field_name}"

    def update_field_name(self, name, field_name):
        """
        Takes a full field name and replaces the struct name prefix.

        Args:
            name(str): struct name
            field_name(str): field name

        Returns:
            updated ffull struct field name (str)
        """
        field_name = str(field_name)
        name = str(name)
        if field_name.startswith(name):
            field_name = field_name.replace(name, "", 1)
        field_name = field_name.rsplit(FIELD_SEP, 1)[-1]
        return self.get_field_name(name, field_name)

    def prefix_fields(self, name, fields, data_only=False, ctrl_only=False):
        """
        Build a dictionary of field names to allow access to field names from hierarchical struct structure.

        Args:
            name(str): struct name
            fields(dict): struct dics as defines by user
            data_only(bool): only data field
            ctrl_only(bool): only control field

        Returns:
            dict
        """
        valid = ready = None
        new_fields = {}
        for field_name in fields:
            bits = fields[field_name]
            full_field_name = self.get_field_name(name, field_name)
            if isinstance(bits, dict):
                son_fields = self.prefix_fields(full_field_name, bits, data_only=data_only, ctrl_only=ctrl_only)
                for son_name, val in son_fields.items():
                    new_fields[son_name] = val
            else:
                if isinstance(bits, float):
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
        """
        Build a dictionary of fields to allow access to field data width from hierarchical struct structure.

        Args:
            name(str): struct name
            fields(dict): struct dics as defines by user
            data_only(bool): only data field
            ctrl_only(bool): only control field

        Returns:
            dict
        """
        return self._name_fields(name, deepcopy(fields), data_only=data_only, ctrl_only=ctrl_only)
