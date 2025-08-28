
def axi_a(id_bits=4, addr_bits=32, burst_bits=2, len_bits=8, size_bits=3, cache_bits=4, lock_bits=1, prot_bits=3):
    fields = {}
    fields["id"] = id_bits
    fields["addr"] = addr_bits
    fields["burst"] = burst_bits
    fields["len"] = len_bits
    fields["size"] = size_bits
    fields["cache"] = cache_bits
    fields["lock"] = lock_bits
    fields["prot"] = prot_bits
    fields["valid"] = 1.0
    fields["ready"] = -1.0
    return fields


def axi_w(data_bits=512):
    fields = {}
    fields["data"] = data_bits
    fields["strb"] = data_bits // 8
    fields["last"] = 1
    fields["valid"] = 1.0
    fields["ready"] = -1.0
    return fields

def axi_b(id_bits=4, resp_bits=2):
    fields = {}
    fields["id"] = -id_bits
    fields["resp"] = -resp_bits
    fields["valid"] = -1.0
    fields["ready"] = 1.0
    return fields

def axi_r(id_bits=4, resp_bits=2, data_bits=512):
    fields = {}
    fields["data"] = -data_bits
    fields["id"] = -id_bits
    fields["resp"] = -resp_bits
    fields["last"] = -1
    fields["valid"] = -1.0
    fields["ready"] = 1.0
    return fields


def axi(id_bits=4, addr_bits=32, data_bits=512, burst_bits=2, len_bits=8, size_bits=3, cache_bits=4, lock_bits=1, prot_bits=3, resp_bits=2):
    fields = {}
    for x in ["w", "r"]:
        fields[f"a{x}"] = axi_a(id_bits=id_bits, addr_bits=addr_bits, burst_bits=burst_bits, len_bits=len_bits, size_bits=size_bits, cache_bits=cache_bits, lock_bits=lock_bits, prot_bits=prot_bits)
    fields["w"] = axi_w(data_bits=data_bits)
    fields["b"] = axi_b(id_bits=id_bits, resp_bits=resp_bits)
    fields["r"] = axi_r(id_bits=id_bits, resp_bits=resp_bits, data_bits=data_bits)
    return fields
