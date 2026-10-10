#!/usr/bin/env python3
"""
Generate the instances of Sect. 10.2 (Table 8): for every allocation of the
appended rounds, the key-recovery model is combined with the time-oriented
objective in SAND_time_objective.mzn.

  t<bs>_<r_in><r_out>.mzn : time-oriented objective; the data constraint
                            C_N < 2^n of the model is removed, and the data
                            is limited to 2^63 for SAND64.

Run each instance with, e.g.,
  minizinc --solver cp-sat --parallel 2 t128_43.mzn
"""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
SPLITS = {64: [(1, 5), (2, 4), (3, 3), (4, 2), (5, 1)],
          128: [(1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1)]}
DEFAULT = {64: (3, 3), 128: (4, 3)}


def main(outdir="."):
    tobj = open(os.path.join(HERE, "SAND_time_objective.mzn")).read()
    for bs in (64, 128):
        src = open(os.path.join(HERE, f"SAND_{bs}_Key_Recovery.mzn"), "rb").read().decode().replace("\r\n", "\n")
        a = src.index("% Data complexity C_N of Eq. (1)")
        b = src.index("< 4*n;", a) + len("< 4*n;")
        src = src[:a] + "% (data constraint removed; see SAND_time_objective.mzn)" + src[b:]
        src = src.replace("solve minimize objective;", "")
        for r_in, r_out in SPLITS[bs]:
            s = src.replace(f"int: r_in = {DEFAULT[bs][0]};", f"int: r_in = {r_in};", 1) \
                   .replace(f"int: r_out = {DEFAULT[bs][1]};", f"int: r_out = {r_out};", 1)
            s += "\n" + tobj
            if bs == 64:
                s += "\nconstraint DD <= 63;\n"
            with open(os.path.join(outdir, f"t{bs}_{r_in}{r_out}.mzn"), "w") as f:
                f.write(s)


if __name__ == "__main__":
    import sys
    main(sys.argv[1] if len(sys.argv) > 1 else ".")
