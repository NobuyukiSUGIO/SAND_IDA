#!/usr/bin/env python3
"""
MiniZinc Bit Position Tester (SAND-128, Phase 2)
Runs SAND_128_with_i_and_j.mzn with unknown_bit_position_i and
unknown_bit_position_j from 0 to 127 each.
Total: 128 * 128 = 16384 combinations

Each run is classified as
  SAT     : an impossible differential was found for (i, j)
  UNSAT   : no impossible differential exists for (i, j) in this model
  UNKNOWN : the solver stopped (time limit) without a conclusion
  ERROR   : MiniZinc failed
"""

import argparse
import concurrent.futures
import os
import subprocess
import time

BLOCK = 128
MODEL = f"SAND_{BLOCK}_with_i_and_j.mzn"
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


def classify(returncode, stdout):
    """Map a MiniZinc run to SAT / UNSAT / UNKNOWN / ERROR"""
    if returncode != 0:
        return "ERROR"
    if "=====UNSATISFIABLE=====" in stdout:
        return "UNSAT"
    if "----------" in stdout:  # MiniZinc solution separator
        return "SAT"
    return "UNKNOWN"


def run_minizinc(bit_position_i, bit_position_j, args):
    """Run MiniZinc with specific bit positions for i and j"""
    cmd = [
        args.minizinc,
        "--solver", args.solver,
        "--parallel", str(args.parallel),
        "-D", f"unknown_bit_position_i={bit_position_i}",
        "-D", f"unknown_bit_position_j={bit_position_j}",
    ]
    if args.time_limit:
        cmd += ["--time-limit", str(args.time_limit * 1000)]
    cmd.append(os.path.join(SCRIPT_DIR, MODEL))

    start_time = time.time()
    try:
        result = subprocess.run(cmd, capture_output=True, text=True)
        returncode, stdout, stderr = result.returncode, result.stdout, result.stderr
    except OSError as e:
        returncode, stdout, stderr = -1, "", str(e)
    elapsed_time = time.time() - start_time
    status = classify(returncode, stdout)

    # Save output to file
    with open(os.path.join(args.outdir, "result",
                           f"output_bit_i{bit_position_i}_j{bit_position_j}.txt"), "w") as f:
        f.write(f"Bit position i: {bit_position_i}\n")
        f.write(f"Bit position j: {bit_position_j}\n")
        f.write(f"Status: {status}\n")
        f.write(f"Elapsed time: {elapsed_time:.2f}s\n")
        f.write(f"Command: {' '.join(cmd)}\n")
        f.write(f"Return code: {returncode}\n")
        f.write("-" * 80 + "\n")
        f.write("STDOUT:\n")
        f.write(stdout)
        f.write("\nSTDERR:\n")
        f.write(stderr)

    return (bit_position_i, bit_position_j), status, elapsed_time, stdout


def main():
    parser = argparse.ArgumentParser(description=f"Phase 2 (i, j) search for SAND-{BLOCK}")
    parser.add_argument("--workers", type=int, default=16, help="number of MiniZinc runs in parallel")
    parser.add_argument("--parallel", type=int, default=2, help="threads per MiniZinc run")
    parser.add_argument("--solver", default="cp-sat")
    parser.add_argument("--minizinc", default="minizinc", help="path to the minizinc executable")
    parser.add_argument("--time-limit", type=int, default=0, help="per-run time limit in seconds (0: none)")
    parser.add_argument("--outdir", default=".", help="directory for result files")
    args = parser.parse_args()

    os.makedirs(os.path.join(args.outdir, "result"), exist_ok=True)
    summary_path = os.path.join(args.outdir, "solutions_summary.txt")
    csv_path = os.path.join(args.outdir, "results_summary.csv")

    # Generate all combinations of (i, j)
    combinations = [(i, j) for i in range(BLOCK) for j in range(BLOCK)]
    total_combinations = len(combinations)

    print(f"MiniZinc Bit Position Tester (SAND-{BLOCK}, i,j version)")
    print(f"Testing bit positions i=0-{BLOCK-1}, j=0-{BLOCK-1} ({total_combinations} combinations) "
          f"with {args.workers} parallel workers")
    print("-" * 80)

    # Clear summary file
    with open(summary_path, "w") as f:
        f.write("MiniZinc Solutions Summary\n")
        f.write("=" * 80 + "\n\n")

    start_time = time.time()
    results = []

    # Run tests in parallel
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as executor:
        futures = [executor.submit(run_minizinc, i, j, args) for i, j in combinations]

        for completed, future in enumerate(concurrent.futures.as_completed(futures), 1):
            (bit_i, bit_j), status, elapsed, stdout = future.result()
            results.append(((bit_i, bit_j), status, elapsed))

            if status == "SAT":
                print(f"✓ i={bit_i}, j={bit_j}: impossible differential found ({elapsed:.2f}s)")
                with open(summary_path, "a") as f:
                    f.write(f"Bit position i={bit_i}, j={bit_j}: SOLUTION FOUND (time: {elapsed:.2f}s)\n")
                    f.write(stdout)
                    f.write("\n" + "=" * 80 + "\n\n")
            elif status in ("ERROR", "UNKNOWN"):
                print(f"✗ i={bit_i}, j={bit_j}: {status} ({elapsed:.2f}s)")

            # Progress update every 100 completions
            if completed % 100 == 0:
                print(f"Progress: {completed}/{total_combinations} completed "
                      f"({completed/total_combinations*100:.1f}%)")

    total_time = time.time() - start_time
    results.sort()

    # Print summary
    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    by_status = {s: [r for r in results if r[1] == s] for s in ("SAT", "UNSAT", "UNKNOWN", "ERROR")}

    print(f"Total execution time: {total_time:.2f}s")
    print(f"Total combinations tested: {total_combinations}")
    for s, rs in by_status.items():
        print(f"{s:8s}: {len(rs)}")

    if by_status["SAT"]:
        print("\nImpossible differentials found (showing first 20):")
        for (i, j), _, elapsed in by_status["SAT"][:20]:
            print(f"  Bit i={i}, j={j}: {elapsed:.2f}s")
        if len(by_status["SAT"]) > 20:
            print(f"  ... and {len(by_status['SAT']) - 20} more")

    bad = by_status["UNKNOWN"] + by_status["ERROR"]
    if bad and len(bad) <= 20:
        print("\nUnfinished / failed runs:")
        for (i, j), status, elapsed in bad:
            print(f"  Bit i={i}, j={j}: {status} ({elapsed:.2f}s)")
    elif bad:
        print(f"\nUnfinished / failed runs: {len(bad)} (too many to display)")

    with open(csv_path, "w") as f:
        f.write("bit_i,bit_j,status,elapsed_time\n")
        for (i, j), status, elapsed in results:
            f.write(f"{i},{j},{status},{elapsed:.2f}\n")

    print(f"\nResults saved to {os.path.join(args.outdir, 'result')}/output_bit_i*_j*.txt")
    print(f"Solutions summary saved to {summary_path}")
    print(f"Summary CSV saved to {csv_path}")


if __name__ == "__main__":
    main()
