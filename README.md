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
### Assumptions (optional)
Use assumptions to constrain the environment (reduce false hits / improve precision).
```bash
python coverage_refine_maxsat.py \
  --top top \
  --assertion-file assertions.txt \
  --assume-file assumptions.txt \
  design.sv
```
### Time Bound
CartCov uses BMC to determine the correctness of assertions, therefore it is necessary to set the time boundary (default is small; larger values increase solving time).
```bash
python coverage_refine_maxsat.py --top top --assertion-file a.txt --sva-max-time 10 design.sv
```
### Clock (optional)
`-c` / `--clock` `<clk_name>:<period>` (default: `DEFAULT_CLOCK:1` Clock rising edge sampling).

Multi-clock support is limited; single-clock designs are recommended.
## What CartCov Computes
### Coverage Items
**Statement coverage (S)**: source lines that contain assignments exercised when the assertion holds, including:
- blocking / non-blocking assignments in procedural blocks
- assignment expressions in procedural statements
**Branch coverage (B)**: control-flow decision points taken when the assertion holds:
-`if/else`
-`case`
### Output Modes
**Core (RTL) mode**: prints covered statements/branches for each assertion:
```bash
Assertion <label> statements <k>
S <label> <file>:<line>
...
Assertion <label> branches <m>
B <label> <file>:<line>
...
```
**SMT2 mode**: prints the selected hit names from a user-provided hit list:
```bash
Minimized hits: <selected> / <total>
<hit_name_1>
<hit_name_2>
...
```
## Workflow
CartCov turns “assertion → covered branch/statement” into a MaxSAT optimization problem. It supports two workflows: **Core refinement mode** (end-to-end from RTL + SVA) and **SMT2 mode** (direct MaxSAT on user-defined hits).
### Core Refinement Mode (End-to-End)
1) **Parse assertions**
- Read `--assertion-file` and extract SVA expressions (supports `assert property(...)` wrapper).
- Optional labels are preserved; otherwise auto-label as `assertion_1`, `assertion_2`, ...
2) **RTL → SMT2**
- Use Yosys to elaborate the RTL and generate an SMT2 model of the design.
- Extract a signal map used by later translations.
3) **SVA → SMT2 constraints**
- Translate the supported SVA subset into SMT2 constraints over time steps `s0..sN` (bounded by `--sva-max-time`).
4) **CEGAR proof core**
- Run a CEGAR loop to prove the assertion and obtain a **minimal set of registers/signals** needed for the proof (`kept`).
- This reduces noise and focuses coverage mapping on the assertion’s effective cone.
5) **Coverage mapping (signals → source locations)**
- Parse RTL with pyslang and build a database:
  - `signal -> statement lines` (assignments)
  - `signal -> branch lines` (control statements guarding those assignments)
- Collect candidate statement/branch locations for signals in `kept`.
6) **MaxSAT set cover on source lines**
- Variables: one boolean per source location (line).
- Hard constraints: every kept signal must be covered by ≥1 selected location.
- Objective: minimize the number of selected locations.

**Output:** minimal statement list (`S ...`) and branch list (`B ...`) per assertion.
### MaxSAT Formulation (Core mode)
Let `Lines(sig)` be the set of source locations that assign `sig` (and branch locations guarding those assignments).

- **Hard:** for each `sig` in `kept`, select at least one location that covers it  
  `∀sig ∈ kept:  OR_{ℓ ∈ Lines(sig)} x_ℓ`
- **Minimize:** total number of selected locations  
  `minimize  Σ_{ℓ} I(x_ℓ)`

This is a set-cover style optimization over statement/branch locations.
### Workflow Diagram
```mermaid
flowchart TD
  A[Inputs<br/>RTL (.v/.sv)<br/>Assertions (SVA)<br/>Assumptions (optional)] --> B[RTL Elaboration / SMT2 Generation<br/>(Yosys)]
  A --> C[Assertion Parsing<br/>(labels, disable iff, ...)]

  C --> D[SVA -> SMT2 Constraints<br/>(bounded by --sva-max-time)]
  B --> E[Design SMT2 + Signal Map]

  D --> F[CEGAR Proof Core (optional)<br/>Output: kept regs/signals]
  E --> F

  F --> G[Coverage Extraction (pyslang)<br/>signal -> stmt lines<br/>signal -> branch lines]
  G --> H[Build candidates from kept]
  H --> I[MaxSAT Optimization<br/>Minimize selected locations<br/>s.t. each kept signal covered]

  I --> J[Outputs<br/>S <label> <file>:<line><br/>B <label> <file>:<line>]

  subgraph SMT2_Mode[SMT2 Mode]
    K[Base SMT2] --> L[Load hits (coverage points)]
    L --> M[MaxSAT: maximize satisfiable hits]
    M --> N[Output hit names]
  end
