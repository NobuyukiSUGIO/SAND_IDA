% Fixes the 14-round impossible differential of Fig. 8 (Sect. 9.2) in
% SAND_128_Key_Recovery.mzn.  Usage:
%   minizinc --solver cp-sat SAND_128_Key_Recovery.mzn SAND_128_fix_Fig8.mzn
% Columns are indexed as in the model (w = 0 is the leftmost column).
%   Delta x_4 = 0,  Delta y_4 column 9 = (?, ?, 1, ?)
%   Delta x_18 column 7 = (?, ?, 0, ?),  Delta y_18 = 0
function int: fig8_dy4(int: i, int: w)  = if w = 9 then (if i = 2 then 1 else -1 endif) else 0 endif;
function int: fig8_dx18(int: i, int: w) = if w = 7 then (if i = 2 then 0 else -1 endif) else 0 endif;
constraint forall(i in 0..3, w in 0..15)(
  XU[0, i, w] = 0 /\ YU[0, i, w] = fig8_dy4(i, w) /\
  XL[rounds, i, w] = fig8_dx18(i, w) /\ YL[rounds, i, w] = 0);
