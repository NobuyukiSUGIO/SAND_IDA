% Fixes the 11-round impossible differential of Fig. 7 (Sect. 9.1) in
% SAND_64_Key_Recovery.mzn.  Usage:
%   minizinc --solver cp-sat SAND_64_Key_Recovery.mzn SAND_64_fix_Fig7.mzn
% Columns are indexed as in the model (w = 0 is the leftmost column).
%   Delta x_3 = 0,  Delta y_3 column 5 = (?, ?, 1, ?)
%   Delta x_14 column 5 = (?, ?, 0, ?),  Delta y_14 = 0
array[0..3, 0..7] of int: FIG7_DY3  = array2d(0..3, 0..7,
  [0,0,0,0,0,-1,0,0, 0,0,0,0,0,-1,0,0, 0,0,0,0,0,1,0,0, 0,0,0,0,0,-1,0,0]);
array[0..3, 0..7] of int: FIG7_DX14 = array2d(0..3, 0..7,
  [0,0,0,0,0,-1,0,0, 0,0,0,0,0,-1,0,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,-1,0,0]);
constraint forall(i in 0..3, w in 0..7)(
  XU[0, i, w] = 0 /\ YU[0, i, w] = FIG7_DY3[i, w] /\
  XL[rounds, i, w] = FIG7_DX14[i, w] /\ YL[rounds, i, w] = 0);
