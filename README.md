# 🚀 P2V – Designing Chips in Python  
**Python to Verilog Compiler**

---

## 📘 What Is P2V?
**P2V** is a Python library for generating synthesizable RTL. It lets chip designers express RTL modules in Python, then compiles them into Verilog.

---

## 👥 Who Is P2V For?
For hardware designers familiar with Verilog and Python who want higher-level abstraction and automation in RTL creation.

---

## 📦 Installation

Install P2V using pip:

```bash
pip install p2v-compiler
```

P2V is a native Python 3 library with no mandatory external dependencies. However, some advanced features rely on the following open-source tools:

| Tool      | Purpose                   | Link |
|-----------|---------------------------|------|
| Verible   | Verilog indentation        | [Verible GitHub](https://github.com/chipsalliance/verible) |
| Verilator | Verilog linting            | [Verilator Install Guide](https://verilator.org/guide/latest/install.html) |
| Icarus    | Verilog simulation         | [Icarus Install Guide](https://steveicarus.github.io/iverilog/usage/installation.html) |

---

## ⚙️ Using P2V with Partial Tooling

P2V can run without all dependencies. To gracefully skip missing tools, add:

```bash
-allow_missing_tools
```

This allows partial functionality (e.g. skipping indentation if Verible is not installed).

---

## 📚 Documentation

👉 [p2v_spec.pdf](https://github.com/eyalhoc/p2v/blob/main/doc/p2v_spec.pdf)

---

## 👋 Hello World Example

Run the tutorial:

```bash
python3 p2v/tutorial/example0_hello_world/hello_world.py
```

Sample output:
```
p2v-INFO: starting with seed 1
p2v-DEBUG: created: hello_world.sv
p2v-INFO: verilog generation completed successfully (1 sec)
p2v-INFO: verilog lint completed successfully
p2v-INFO: completed successfully
```
