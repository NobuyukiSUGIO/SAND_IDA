## ReadMe
### 1. Overview
This repository contains the code artifacts for “Impossible Differential Attacks on a Lightweight Block Cipher SAND” by Nobuyuki Sugio. 
It includes MiniZinc models and Python helpers for searching impossible differential distinguishers and constructing distinguishers for key-recovery experiments on SAND-64 and SAND-128.

### 2. Repository Structure
.  
├─ Phase1/                      # Search impossible differential distinguishers (coarse search)  
│  ├─ SAND_64_impossible_differentials.mzn  
│  └─ SAND_128_impossible_differentials.mzn  
│  
├─ Phase2/                      # Search with (i, j) constraints (refined search)  
│  ├─ SAND_64_subprocess_with_i_and_j.py  
│  ├─ SAND_64_with_i_and_j.mzn  
│  ├─ SAND_128_subprocess_with_i_and_j.py  
│  └─ SAND_128_with_i_and_j.mzn  
│  
└─ KeyRecovery/                 # Distinguishers for key-recovery  
   ├─ SAND_64_Key_Recovery.mzn  
   └─ SAND_128_Key_Recovery.mzn  

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

### 5. Notes
* Output formats and runtime depend on your solver and machine configuration.
* For reproducibility, consider recording MiniZinc version, solver backend, and command-line options.

### 6. Citation
If you use this code, please cite:  
Nobuyuki Sugio, “Impossible Differential Attacks on a Lightweight Block Cipher SAND,” (manuscript under review).
