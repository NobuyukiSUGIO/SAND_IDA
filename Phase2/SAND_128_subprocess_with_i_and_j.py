#!/usr/bin/env python3
"""
MiniZinc Bit Position Tester
Runs MiniZinc with unknown_bit_position_i and unknown_bit_position_j from 0 to 63 each
Total: 128 * 128 combinations
"""

import subprocess
import time
import concurrent.futures
import sys
import os

def run_minizinc(bit_position_i, bit_position_j):
    """Run MiniZinc with specific bit positions for i and j"""
    cmd = [
        "minizinc",
        "--solver", "cp-sat",
        "--parallel", "2",
        "-D", f"unknown_bit_position_i={bit_position_i}",
        "-D", f"unknown_bit_position_j={bit_position_j}",
        "SAND_128_with_i_and_j.mzn"
    ]
    
    print(f"Running bit_position_i={bit_position_i}, bit_position_j={bit_position_j}...")
    start_time = time.time()
    
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            check=True
        )
        
        elapsed_time = time.time() - start_time
        
        # Create result directory if it doesn't exist
        os.makedirs("result", exist_ok=True)
        
        # Save output to file
        with open(f"result/output_bit_i{bit_position_i}_j{bit_position_j}.txt", "w") as f:
            f.write(f"Bit position i: {bit_position_i}\n")
            f.write(f"Bit position j: {bit_position_j}\n")
            f.write(f"Elapsed time: {elapsed_time:.2f}s\n")
            f.write(f"Command: {' '.join(cmd)}\n")
            f.write("-" * 80 + "\n")
            f.write("STDOUT:\n")
            f.write(result.stdout)
            f.write("\nSTDERR:\n")
            f.write(result.stderr)
        
        # Also save successful solutions to a summary file
        if "----------" in result.stdout:  # MiniZinc solution separator
            with open("solutions_summary.txt", "a") as f:
                f.write(f"Bit position i={bit_position_i}, j={bit_position_j}: SOLUTION FOUND (time: {elapsed_time:.2f}s)\n")
                f.write(result.stdout)
                f.write("\n" + "="*80 + "\n\n")
        
        print(f"✓ Bit position i={bit_position_i}, j={bit_position_j} completed in {elapsed_time:.2f}s")
        return (bit_position_i, bit_position_j), True, elapsed_time
        
    except subprocess.CalledProcessError as e:
        elapsed_time = time.time() - start_time
        
        # Create result directory if it doesn't exist
        os.makedirs("result", exist_ok=True)
        
        # Save error output
        with open(f"result/output_bit_i{bit_position_i}_j{bit_position_j}.txt", "w") as f:
            f.write(f"Bit position i: {bit_position_i}\n")
            f.write(f"Bit position j: {bit_position_j}\n")
            f.write(f"Elapsed time: {elapsed_time:.2f}s\n")
            f.write(f"Command: {' '.join(cmd)}\n")
            f.write(f"Return code: {e.returncode}\n")
            f.write("-" * 80 + "\n")
            f.write("STDOUT:\n")
            f.write(e.stdout if e.stdout else "")
            f.write("\nSTDERR:\n")
            f.write(e.stderr if e.stderr else "")
        
        print(f"✗ Bit position i={bit_position_i}, j={bit_position_j} failed (time: {elapsed_time:.2f}s)")
        return (bit_position_i, bit_position_j), False, elapsed_time

def main():
    # Number of parallel jobs (adjust based on your system)
    max_workers = 16  # Adjust based on your system capacity
    
    print("MiniZinc Bit Position Tester (i,j version)")
    print(f"Testing bit positions i=0-127, j=0-127 with {max_workers} parallel workers")
    print("-" * 80)
    
    # Clear summary file
    with open("solutions_summary.txt", "w") as f:
        f.write("MiniZinc Solutions Summary\n")
        f.write("=" * 80 + "\n\n")
    
    start_time = time.time()
    results = []
    
    # Generate all combinations of (i, j)
    combinations = [(i, j) for i in range(128) for j in range(128)]
    total_combinations = len(combinations)
    
    print(f"Total combinations to test: {total_combinations}")
    
    # Run tests in parallel
    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {executor.submit(run_minizinc, i, j): (i, j) for i, j in combinations}
        
        completed = 0
        for future in concurrent.futures.as_completed(futures):
            (bit_i, bit_j), success, elapsed = future.result()
            results.append(((bit_i, bit_j), success, elapsed))
            completed += 1
            
            # Progress update every 100 completions
            if completed % 100 == 0:
                print(f"Progress: {completed}/{total_combinations} completed ({completed/total_combinations*100:.1f}%)")
    
    total_time = time.time() - start_time
    
    # Print summary
    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    
    successful = [((i, j), time) for (i, j), success, time in results if success]
    failed = [((i, j), time) for (i, j), success, time in results if not success]
    
    print(f"Total execution time: {total_time:.2f}s")
    print(f"Total combinations tested: {total_combinations}")
    print(f"Successful runs: {len(successful)}")
    print(f"Failed runs: {len(failed)}")
    
    if successful:
        print(f"\nSuccessful bit positions (showing first 20):")
        for (i, j), elapsed in sorted(successful)[:20]:
            print(f"  Bit i={i}, j={j}: {elapsed:.2f}s")
        if len(successful) > 20:
            print(f"  ... and {len(successful) - 20} more")
    
    if failed and len(failed) <= 20:
        print("\nFailed bit positions:")
        for (i, j), elapsed in sorted(failed):
            print(f"  Bit i={i}, j={j}: {elapsed:.2f}s")
    elif failed:
        print(f"\nFailed runs: {len(failed)} (too many to display)")
    
    print(f"\nResults saved to result/output_bit_i*_j*.txt files")
    print(f"Solutions summary saved to solutions_summary.txt")
    
    # Optional: Create a summary CSV for easier analysis
    print("\nCreating summary CSV...")
    with open("results_summary.csv", "w") as f:
        f.write("bit_i,bit_j,success,elapsed_time\n")
        for (i, j), success, elapsed in sorted(results):
            f.write(f"{i},{j},{1 if success else 0},{elapsed:.2f}\n")
    print("Summary CSV saved to results_summary.csv")

if __name__ == "__main__":
    main()