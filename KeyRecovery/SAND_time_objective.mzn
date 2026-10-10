%==============================================================================
% Time-oriented objective for SAND_{64,128}_Key_Recovery.mzn (Sect. 10.2)
%
% Usage: append this file to a key-recovery model after removing
%   - its "solve minimize objective;" item, and
%   - the data constraint (C_N < 2^n),
% e.g. with make_variants.py.  For SAND64 add "constraint DD <= 63;".
%
% Variables: the pattern of the model and the amount of data 2^DD.
%   CN2 = 2 * log2 C_N  (Eq. (1), integer)
%   S   = floor(2^DD / C_N) = floor(2^((2*DD - CN2)/2))      (number of sets)
%   T   = 2^DD + S*(N_min + 2^|k|)*C'_E + 2^|K|*(1/2)^S
% The solver minimizes the largest of the four terms of T on a log2 scale
% (x100).  T is at least its largest term and at most four times it; the
% minimum of the largest term does not guarantee that T itself is minimized.
% |k| is the number of guessed subkey bits K_IN + K_OUT, an upper bound on
% the number of linearly independent key bits under the key schedule.
%==============================================================================
var int: CN2 = max(min(C_IN + C_OUT + 2*n + 1 - D_IN, C_IN + C_OUT + 2*n + 1 - D_OUT),
                   2 * (C_IN + C_OUT + 2*n + 1 - D_IN - D_OUT));
var 1..2*n: DD;
constraint CN2 <= 2*DD;
var 0..4*n: E = 2*DD - CN2;          % S = floor(2^(E/2))
% S and round(100*log2 S) for E = 0..17 (S <= 362); for E >= 18, S >= 512
array[0..17] of int: S_TAB = array1d(0..17,
  [1, 1, 2, 2, 4, 5, 8, 11, 16, 22, 32, 45, 64, 90, 128, 181, 256, 362]);
array[0..17] of int: LS_TAB = array1d(0..17,
  [0, 0, 100, 100, 200, 232, 300, 346, 400, 446, 500, 549, 600, 649, 700, 750, 800, 850]);
var int: S_CAP = if E <= 17 then S_TAB[min(E, 17)] else 1000 endif;   % S (capped)
var int: LS100 = if E <= 17 then LS_TAB[min(E, 17)] else 50*E endif;  % 100*log2 S
% 100*log2 C'_E, rounded up
int: LCE = ceil(100.0 * log2(int2float(r_in + r_out) / int2float(r_in + rounds + r_out)));
var int: TT = max([100*DD, LS100 + 100*(C_IN + C_OUT) + LCE, LS100 + 100*(K_IN + K_OUT) + LCE,
                   100*(key_size - S_CAP)]);
solve minimize TT;
output ["\nTMIN: D = " ++ show(DD) ++ ", S = " ++ (if fix(E) <= 17 then show(S_TAB[fix(E)]) else "2^" ++ show(fix(E) div 2) ++ "+" endif) ++
        ", CN2 = " ++ show(CN2) ++ ", c = " ++ show(C_IN + C_OUT) ++ ", k = " ++ show(K_IN + K_OUT) ++
        ", TT/100 = " ++ show(TT) ++ "\n"];
