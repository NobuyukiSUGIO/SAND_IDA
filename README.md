## ReadMe
### 1. Overview
This repository contains the code artifacts for “Impossible Differential Attacks on a Lightweight Block Cipher SAND” by Nobuyuki Sugio. 
It includes MiniZinc models and Python helpers for searching impossible differential distinguishers and constructing distinguishers for key-recovery experiments on SAND-64 and SAND-128.

### 2. Repository Structure
.  
├─ Phase1/ &emsp;                     # Search impossible differential distinguishers (coarse search)  
│  ├─ SAND_64_impossible_differentials.mzn  
│  └─ SAND_128_impossible_differentials.mzn  
│  
├─ Phase2/ &emsp;                     # Search with (i, j) constraints (refined search)  
│  ├─ SAND_64_subprocess_with_i_and_j.py  
│  ├─ SAND_64_with_i_and_j.mzn  
│  ├─ SAND_128_subprocess_with_i_and_j.py  
│  └─ SAND_128_with_i_and_j.mzn  
│  
└─ KeyRecovery/ &emsp;                # Distinguishers for key-recovery  
&emsp;├─ SAND_64_Key_Recovery.mzn  
&emsp;└─ SAND_128_Key_Recovery.mzn  

If you keep all files in a single folder, you can omit the directory names above. 
The grouping is only for readability.

### 3. Requirements
* MiniZinc (with a compatible constraint solver)
* Python 3.x
Ensure minizinc is on your PATH. The Python scripts call MiniZinc via subprocess.

### 4. How to Use
#### Phase 1 — Search for impossible differential distinguishers
Use these MiniZinc models to perform the initial search:  
* SAND_64_impossible_differentials.mzn
* SAND_128_impossible_differentials.mzn

Example (command line):  
bash  
minizinc SAND_64_impossible_differentials.mzn  
minizinc SAND_128_impossible_differentials.mzn  

#### Phase 2 — Refined search with (i, j) constraints
Use the Python helpers, which invoke the corresponding MiniZinc models:
* SAND_64_subprocess_with_i_and_j.py (uses SAND_64_with_i_and_j.mzn)
* SAND_128_subprocess_with_i_and_j.py (uses SAND_128_with_i_and_j.mzn)

Example (command line):  
bash  
python3 SAND_64_subprocess_with_i_and_j.py  
python3 SAND_128_subprocess_with_i_and_j.py  

Options: `--workers`, `--parallel`, `--solver`, `--minizinc`, `--time-limit` (seconds), `--outdir`.
Each (i, j) is recorded as SAT (impossible differential found), UNSAT, UNKNOWN or ERROR in `results_summary.csv`.

**Optional**: You may also run the MiniZinc models directly without the Python wrappers:
bash   
minizinc SAND_64_with_i_and_j.mzn  
minizinc SAND_128_with_i_and_j.mzn  

#### Key-Recovery — Build distinguishers for attacks
Use the following MiniZinc models to search distinguishers tailored for key-recovery:
* SAND_64_Key_Recovery.mzn
* SAND_128_Key_Recovery.mzn

Example (command line):  
bash  
minizinc SAND_64_Key_Recovery.mzn  
minizinc SAND_128_Key_Recovery.mzn  

Defaults: r_in = 3, r_out = 3 for SAND64 (17 rounds) and r_in = 4, r_out = 3 for SAND128 (21 rounds).
The output lists c_in, c_out, k_in, k_out, |Δin|, |Δout| and the data/time/memory estimate for N = N_min.
It also enumerates, for 2^D plaintexts (D = ⌈log2 C_N⌉ … 2n), the number of C_N sets S = ⌊2^D / C_N⌋ and the time complexity
T = 2^D + S·(N_min + 2^|k_in ∪ k_out|)·C_E' + 2^|K|·(1/2)^S; `-D data_log2=<D>` marks the available data (default 63 for SAND64, 125 for SAND128).
Options: `-D obj_mode=0` (minimize |k_in ∪ k_out|, default), `1` (then c_in + c_out, then maximize |Δin| + |Δout|), `2` (minimize c_in + c_out);
`-D unknown_bit_position_i=<i> -D unknown_bit_position_j=<j>` applies the Phase 2 unknown seeding to the distinguisher.

### 5. Notes
* Output formats and runtime depend on your solver and machine configuration.
* For reproducibility, consider recording MiniZinc version, solver backend, and command-line options.

### 6. Citation
If you use this code, please cite:  
Nobuyuki Sugio, “Impossible Differential Attacks on a Lightweight Block Cipher SAND,” (manuscript under review).
