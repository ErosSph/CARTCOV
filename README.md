# Table of contents
- [Project info](#project-info)
- [Quick start](#quick-start)
  - [Dependencies](#dependencies)
  - [Install](#install)
  - [Run](#run)
- [Usage](#usage)
- [Examples](#examples)
- [License](#license)

# Project info
CartCov is a platform that characterizes the relationship between assertions and code coverage by computing which RTL(.v/.sv) branches and statements are exercised by a given assertion. Starting from a design under verification (DUV), a set of assertions, and a bounded time horizon, CartCov encodes the assertion semantics together with branch/statement reachability conditions as a MaxSAT problem. By solving MaxSAT, the platform identifies a maximal set of coverage items (branches and statements) that can be simultaneously justified under the assertion constraints, and reports the corresponding covered locations and witnesses.

# Quick start
We recommend using Python 3.10 or later.
## Dependencies
- pyslang
- Z3
- yosys
- pyverilog
- networkx
## Install
```bash
pip install -r requirements-full.txt
```
## Run
```bash
python coverage_refine_maxsat.py \
    --top <top_module> \
    --assertion-file <assertions.txt> \
    <design.v>
```
# Usage
## Inputs
CartCov takes three types of inputs: design files, assertions, and analysis configuration (time bound, clock, optional assumptions).
### Design Under Verification (DUV)
**Formats**: Verilog/SystemVerilog (.v/.sv), single or multiple files, hierarchical designs supported.

**Usage**：
```bash
python coverage_refine_maxsat.py --top <top_module> file1.v file2.sv ...
```
**Include dirs**:
```bash
python coverage_refine_maxsat.py --top top -I ./include -I ./common design.sv
```
### Assertions
**File**: a text file specified by --assertion-file.

**One assertion per line**, either as a raw SVA expression or wrapped in assert property(...).

Examples:
```bash
req |-> ##1 ack
assert property ($rose(start) |-> ##[1:5] done);
```
**Supported SVA subset (high level)**:
| Category | Operators / Functions | Syntax Examples |
|---|---|---|
| Implication | `\|->`, `\|=>` | `req \|-> ack`, `req \|=> ack` |
| Delay | `##N`, `##[m:n]` | `##1`, `##[1:5]` |
| Repetition | `[*N]`, `[*m:n]` | `busy[*3]`, `busy[*1:5]` |
| Boolean / bitwise | `!`, `&&`, `\|\|`, `&`, `\|`, `^` | `!reset`, `a && b`, `a \|\| b`, `a & b`, `a \| b`, `a ^ b` |
| Comparisons (unsigned) | `==`, `!=`, `<`, `<=`, `>`, `>=` | `state == IDLE`, `cnt != 0`, `cnt < 10` |
| System functions | `$past`, `$stable`, `$rose`, `$fell`, `$onehot0` | `$past(sig, 1)`, `$stable(state)`, `$rose(req)`, `$fell(ack)`, `$onehot0(vec)` |
| Disable | `disable iff (cond)` | `disable iff (reset) req \|-> ack` |


