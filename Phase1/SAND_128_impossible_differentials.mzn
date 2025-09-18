include "globals.mzn";

int: rounds = 14;    % Number of rounds (adjust as needed)
int: word = 16;      % 8 for SAND-64, 16 for SAND-128
int: n=64;           % 32 for SAND-64, 64 for SAND-128

set of int: D = -1..1; % -1: Unknown, 0: No diff, 1: Diff of 1
array[0..n-1] of var D: PL; % State variables for Plaintext-Left 
array[0..n-1] of var D: PR; % State variables for Plaintext-Right 
array[0..n-1] of var D: CL; % State variables for Ciphertext-Left 
array[0..n-1] of var D: CR; % State variables for Ciphertext-Right 
array[0..rounds, 0..3, 0..word-1] of var D: XU; % State variables for Left 
array[0..rounds, 0..3, 0..word-1] of var D: YU; % State variables for Right
array[0..rounds-1, 0..3, 0..word-1] of var D: G0_U; % State variables for G0-box
array[0..rounds-1, 0..3, 0..word-1] of var D: G1_U; % State variables for G1-box
array[0..rounds, 0..3, 0..word-1] of var D: XL; % Backward difference variables
array[0..rounds, 0..3, 0..word-1] of var D: YL; % Backward difference variables for S-box
array[0..rounds-1, 0..3, 0..word-1] of var D: G0_L; % State variables for G0-box
array[0..rounds-1, 0..3, 0..word-1] of var D: G1_L; % State variables for G1-box

% Forward:Round function constraints ========================================
% State loading
constraint forall(w in 0..word-1, i in 0..3)(
  PL[i+4*w] = XU[0, i, w] /\
  PR[i+4*w] = YU[0, i, w]
);

% Input constraints
constraint sum(i in 0..3, w in 0..word-1) (XU[0, i, w] + YU[0, i, w]) != 0;

% G-box layer (Bit-wise Deterministic Differential Transitions)
constraint forall(r in 0..rounds-1, w in 0..word-1) (
  g0_box(XU[r,0,w],XU[r,1,w],XU[r,2,w],XU[r,3,w],G0_U[r,0,w],G0_U[r,1,w],G0_U[r,2,w],G0_U[r,3,w]) /\
  g1_box(XU[r,0,(w+1)mod 16],XU[r,1,(w+1)mod 16],XU[r,2,(w+1)mod 16],XU[r,3,(w+1)mod 16],G1_U[r,0,w],G1_U[r,1,w],G1_U[r,2,w],G1_U[r,3,w])
);

% Linear layer Note that MSB=0, LSB=15
array[0..word-1] of int: P = array1d(0..word-1, [14,15,8,9,2,3,12,13,6,7,0,1,10,11,4,5]);
constraint forall(r in 0..rounds-1, j in 0..3, w in 0..word-1) (
  YU[r+1, j, w] = XU[r, j, w] /\
  XU[r+1, j, w] = XOR(G0_U[r, j, P[w]], G1_U[r, j, P[w]], YU[r, j, w])
);
%=============================================================================

% Backward:Round function constraints ========================================
% State loading
constraint forall(w in 0..word-1, i in 0..3)(
  CL[i+4*w] = XL[rounds, i, w] /\
  CR[i+4*w] = YL[rounds, i, w]
);
% Outputs constraints
constraint sum(i in 0..3, w in 0..word-1) (XL[rounds, i, w] + YL[rounds, i, w]) != 0;

% G-box layer (Bit-wise Deterministic Differential Transitions)
constraint forall(r in 0..rounds-1, w in 0..word-1) (
  g0_box(XL[r,0,w],XL[r,1,w],XL[r,2,w],XL[r,3,w],G0_L[r,0,w],G0_L[r,1,w],G0_L[r,2,w],G0_L[r,3,w]) /\
  g1_box(XL[r,0,(w+1)mod 16],XL[r,1,(w+1)mod 16],XL[r,2,(w+1)mod 16],XL[r,3,(w+1)mod 16],G1_L[r,0,w],G1_L[r,1,w],G1_L[r,2,w],G1_L[r,3,w])
);

% Linear layer
constraint forall(r in 0..rounds-1, j in 0..3, w in 0..word-1) (
  XL[r, j, w] = YL[r+1, j, w] /\
  YL[r, j, w] = XOR(G0_L[r, j, P[w]], G1_L[r, j, P[w]], XL[r+1, j, w])
);
%=============================================================================

% constraints for the meeting point
array[0..rounds-1, 0..3, 0..word-1] of var 0..1: contradict_x;
array[0..rounds-1, 0..3, 0..word-1] of var 0..1: contradict_y;
array[0..rounds-1, 0..3, 0..word-1] of var 0..1: contradict_g0;
array[0..rounds-1, 0..3, 0..word-1] of var 0..1: contradict_g1;
constraint forall(r in 0..rounds-1, i in 0..3, w in 0..word-1)(contradict_x[r, i, w] = bool2int(XU[r, i, w] + XL[r, i, w] == 1));
constraint forall(r in 0..rounds-1, i in 0..3, w in 0..word-1)(contradict_y[r, i, w] = bool2int(YU[r, i, w] + YL[r, i, w] == 1));
constraint forall(r in 0..rounds-1, i in 0..3, w in 0..word-1)(contradict_g0[r, i, w] = bool2int(G0_U[r, i, w] + G0_L[r, i, w] == 1));
constraint forall(r in 0..rounds-1, i in 0..3, w in 0..word-1)(contradict_g1[r, i, w] = bool2int(G1_U[r, i, w] + G1_L[r, i, w] == 1));
constraint sum(r in 0..rounds-1, i in 0..3, w in 0..word-1)(
  contradict_x[r, i, w] + contradict_y[r, i, w] + contradict_g0[r, i, w] + contradict_g1[r, i, w]
  ) > 0;

% Search strategy
ann: search_ann;
search_ann = seq_search([
    int_search([G0_L[rounds-1, 0, w] | w in 0..word-1], indomain_median, complete),
    int_search([G0_L[rounds-1, 1, w] | w in 0..word-1], indomain_median, complete),
    int_search([G0_L[rounds-1, 2, w] | w in 0..word-1], indomain_median, complete),
    int_search([G0_L[rounds-1, 3, w] | w in 0..word-1], indomain_median, complete),
    int_search([G1_L[rounds-1, 0, w] | w in 0..word-1], indomain_median, complete),
    int_search([G1_L[rounds-1, 1, w] | w in 0..word-1], indomain_median, complete),
    int_search([G1_L[rounds-1, 2, w] | w in 0..word-1], indomain_median, complete),
    int_search([G1_L[rounds-1, 3, w] | w in 0..word-1], indomain_median, complete)]); 
            
%solve maximize unknown_bits;
solve minimize sum(i in 0..3, w in 0..word-1)(XU[0, i, w] + YU[0, i, w] + XL[rounds, i, w] + YL[rounds, i, w]);

% Output (adjusted for better readability)
output [
    "PL" ++ ": \"" ++
    join("", [if fix(PL[i+4*w]) = -1 then "?" else show(fix(PL[i+4*w])) endif | w in 0..word-1, i in 0..3])];
output ["\n"];
        
output [
    "XU_" ++ show(r) ++ ": \"" ++
    join("", [if fix(XU[r, i, w]) = -1 then "?" else show(fix(XU[r, i, w])) endif | i in 0..3, w in 0..word-1]) ++ "\"\n"
    | r in 0..rounds];

output [
    "PR" ++ ": \"" ++
    join("", [if fix(PR[i+4*w]) = -1 then "?" else show(fix(PR[i+4*w])) endif | w in 0..word-1, i in 0..3])];
output ["\n"];

output [
    "YU_" ++ show(r) ++ ": \"" ++
    join("", [if fix(YU[r, i, w]) = -1 then "?" else show(fix(YU[r, i, w])) endif | i in 0..3, w in 0..word-1]) ++ "\"\n"
    | r in 0..rounds];
    
output ["\n"];

output [
    "CL" ++ ": \"" ++
    join("", [if fix(CL[i+4*w]) = -1 then "?" else show(fix(CL[i+4*w])) endif | w in 0..word-1, i in 0..3])];
output ["\n"];
  
output [
    "XL_" ++ show(r) ++ ": \"" ++
    join("", [if fix(XL[r, i, w]) = -1 then "?" else show(fix(XL[r, i, w])) endif | i in 0..3, w in 0..word-1]) ++ "\"\n"
    | r in 0..rounds];

output [
    "CR" ++ ": \"" ++
    join("", [if fix(CR[i+4*w]) = -1 then "?" else show(fix(CR[i+4*w])) endif | w in 0..word-1, i in 0..3])];
output ["\n"];

output [
    "YL_" ++ show(r) ++ ": \"" ++
    join("", [if fix(YL[r, i, w]) = -1 then "?" else show(fix(YL[r, i, w])) endif | i in 0..3, w in 0..word-1]) ++ "\"\n"
    | r in 0..rounds];
    
output ["\n\nNo non-fixed input bits: " ++ show(sum(i in 0..3, w in 0..word-1)(bool2int(XU[0, i, w] == -1)+bool2int(YU[0, i, w] == -1)+bool2int(XL[rounds, i, w] == -1)+bool2int(YL[rounds, i, w] == -1)))];

% S-box (Bit-wise Deterministic Differential Transitions, a0 and b0 are MSBs.)
predicate g0_box(var D: a0,var D: a1, var D: a2, var D: a3, var D: b0,var D: b1, var D: b2, var D: b3,) = 
    if (a0 == 0 /\ a1 == 0 /\ a2 == 0 /\ a3 == 0) then (b0 = 0 /\ b1 = 0 /\ b2 = 0 /\ b3 = 0)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == 0 /\ a3 == 1) then (b0 = -1 /\ b1 = 0 /\ b2 = 0 /\ b3 = 1)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == 0 /\ a3 == -1) then (b0 = -1 /\ b1 = 0 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == 1 /\ a3 == 0) then (b0 = -1 /\ b1 = 0 /\ b2 = 1 /\ b3 = 0)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == 1 /\ a3 == 1) then (b0 = -1 /\ b1 = 0 /\ b2 = 1 /\ b3 = 1)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == 1 /\ a3 == -1) then (b0 = -1 /\ b1 = 0 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == -1 /\ a3 == 0) then (b0 = -1 /\ b1 = 0 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == -1 /\ a3 == 1) then (b0 = -1 /\ b1 = 0 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == -1 /\ a3 == -1) then (b0 = -1 /\ b1 = 0 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == 0 /\ a3 == 0) then (b0 = -1 /\ b1 = 1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == 0 /\ a3 == 1) then (b0 = -1 /\ b1 = 1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == 0 /\ a3 == -1) then (b0 = -1 /\ b1 = 1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == 1 /\ a3 == 0) then (b0 = -1 /\ b1 = 1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == 1 /\ a3 == 1) then (b0 = -1 /\ b1 = 1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == 1 /\ a3 == -1) then (b0 = -1 /\ b1 = 1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == -1 /\ a3 == 0) then (b0 = -1 /\ b1 = 1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == -1 /\ a3 == 1) then (b0 = -1 /\ b1 = 1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == -1 /\ a3 == -1) then (b0 = -1 /\ b1 = 1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == -1 /\ a2 == 0 /\ a3 == 0) then (b0 = -1 /\ b1 = -1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == -1 /\ a2 == 0 /\ a3 == 1) then (b0 = -1 /\ b1 = -1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == -1 /\ a2 == 0 /\ a3 == -1) then (b0 = -1 /\ b1 = -1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == -1 /\ a2 == 1 /\ a3 == 0) then (b0 = -1 /\ b1 = -1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == -1 /\ a2 == 1 /\ a3 == 1) then (b0 = -1 /\ b1 = -1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == -1 /\ a2 == 1 /\ a3 == -1) then (b0 = -1 /\ b1 = -1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == 0 /\ a3 == 0) then (b0 = -1 /\ b1 = 0 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == 0 /\ a3 == 1) then (b0 = -1 /\ b1 = 0 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == 0 /\ a3 == -1) then (b0 = -1 /\ b1 = 0 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == 1 /\ a3 == 0) then (b0 = -1 /\ b1 = 0 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == 1 /\ a3 == 1) then (b0 = -1 /\ b1 = 0 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == 1 /\ a3 == -1) then (b0 = -1 /\ b1 = 0 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == -1 /\ a3 == 0) then (b0 = -1 /\ b1 = 0 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == -1 /\ a3 == 1) then (b0 = -1 /\ b1 = 0 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == -1 /\ a3 == -1) then (b0 = -1 /\ b1 = 0 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == 0 /\ a3 == 0) then (b0 = -1 /\ b1 = 1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == 0 /\ a3 == 1) then (b0 = -1 /\ b1 = 1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == 0 /\ a3 == -1) then (b0 = -1 /\ b1 = 1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == 1 /\ a3 == 0) then (b0 = -1 /\ b1 = 1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == 1 /\ a3 == 1) then (b0 = -1 /\ b1 = 1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == 1 /\ a3 == -1) then (b0 = -1 /\ b1 = 1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == -1 /\ a3 == 0) then (b0 = -1 /\ b1 = 1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == -1 /\ a3 == 1) then (b0 = -1 /\ b1 = 1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == -1 /\ a3 == -1) then (b0 = -1 /\ b1 = 1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == -1 /\ a2 == 0 /\ a3 == 0) then (b0 = -1 /\ b1 = -1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == -1 /\ a2 == 0 /\ a3 == 1) then (b0 = -1 /\ b1 = -1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == -1 /\ a2 == 0 /\ a3 == -1) then (b0 = -1 /\ b1 = -1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == -1 /\ a2 == 1 /\ a3 == 0) then (b0 = -1 /\ b1 = -1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == -1 /\ a2 == 1 /\ a3 == 1) then (b0 = -1 /\ b1 = -1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == -1 /\ a2 == 1 /\ a3 == -1) then (b0 = -1 /\ b1 = -1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 0 /\ a2 == 0 /\ a3 == 0) then (b0 = -1 /\ b1 = 0 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 0 /\ a2 == 0 /\ a3 == 1) then (b0 = -1 /\ b1 = 0 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 0 /\ a2 == 0 /\ a3 == -1) then (b0 = -1 /\ b1 = 0 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 0 /\ a2 == 1 /\ a3 == 0) then (b0 = -1 /\ b1 = 0 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 0 /\ a2 == 1 /\ a3 == 1) then (b0 = -1 /\ b1 = 0 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 0 /\ a2 == 1 /\ a3 == -1) then (b0 = -1 /\ b1 = 0 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 0 /\ a2 == -1 /\ a3 == 0) then (b0 = -1 /\ b1 = 0 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 0 /\ a2 == -1 /\ a3 == 1) then (b0 = -1 /\ b1 = 0 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 0 /\ a2 == -1 /\ a3 == -1) then (b0 = -1 /\ b1 = 0 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 1 /\ a2 == 0 /\ a3 == 0) then (b0 = -1 /\ b1 = 1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 1 /\ a2 == 0 /\ a3 == 1) then (b0 = -1 /\ b1 = 1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 1 /\ a2 == 0 /\ a3 == -1) then (b0 = -1 /\ b1 = 1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 1 /\ a2 == 1 /\ a3 == 0) then (b0 = -1 /\ b1 = 1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 1 /\ a2 == 1 /\ a3 == 1) then (b0 = -1 /\ b1 = 1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 1 /\ a2 == 1 /\ a3 == -1) then (b0 = -1 /\ b1 = 1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 1 /\ a2 == -1 /\ a3 == 0) then (b0 = -1 /\ b1 = 1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 1 /\ a2 == -1 /\ a3 == 1) then (b0 = -1 /\ b1 = 1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 1 /\ a2 == -1 /\ a3 == -1) then (b0 = -1 /\ b1 = 1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == -1 /\ a2 == 0 /\ a3 == 0) then (b0 = -1 /\ b1 = -1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == -1 /\ a2 == 0 /\ a3 == 1) then (b0 = -1 /\ b1 = -1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == -1 /\ a2 == 0 /\ a3 == -1) then (b0 = -1 /\ b1 = -1 /\ b2 = 0 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == -1 /\ a2 == 1 /\ a3 == 0) then (b0 = -1 /\ b1 = -1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == -1 /\ a2 == 1 /\ a3 == 1) then (b0 = -1 /\ b1 = -1 /\ b2 = 1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == -1 /\ a2 == 1 /\ a3 == -1) then (b0 = -1 /\ b1 = -1 /\ b2 = 1 /\ b3 = -1)
    else (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    endif;

predicate g1_box(var D: a0,var D: a1, var D: a2, var D: a3, var D: b0,var D: b1, var D: b2, var D: b3,) = 
    if (a0 == 0 /\ a1 == 0 /\ a2 == 0 /\ a3 == 0) then (b0 = 0 /\ b1 = 0 /\ b2 = 0 /\ b3 = 0)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == 0 /\ a3 == 1) then (b0 = 0 /\ b1 = 0 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == 0 /\ a3 == -1) then (b0 = 0 /\ b1 = 0 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == 1 /\ a3 == 0) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == 1 /\ a3 == 1) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == 1 /\ a3 == -1) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == -1 /\ a3 == 0) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == -1 /\ a3 == 1) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 0 /\ a1 == 0 /\ a2 == -1 /\ a3 == -1) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == 0 /\ a3 == 0) then (b0 = 0 /\ b1 = 1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == 0 /\ a3 == 1) then (b0 = 0 /\ b1 = 1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == 0 /\ a3 == -1) then (b0 = 0 /\ b1 = 1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == 1 /\ a3 == 0) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == 1 /\ a3 == 1) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == 1 /\ a3 == -1) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == -1 /\ a3 == 0) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == -1 /\ a3 == 1) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 0 /\ a1 == 1 /\ a2 == -1 /\ a3 == -1) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == -1 /\ a2 == 0 /\ a3 == 0) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 0 /\ a1 == -1 /\ a2 == 0 /\ a3 == 1) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 0 /\ a1 == -1 /\ a2 == 0 /\ a3 == -1) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == -1 /\ a2 == 1 /\ a3 == 0) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 0 /\ a1 == -1 /\ a2 == 1 /\ a3 == 1) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 0 /\ a1 == -1 /\ a2 == 1 /\ a3 == -1) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 0 /\ a1 == -1 /\ a2 == -1 /\ a3 == 0) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 0 /\ a1 == -1 /\ a2 == -1 /\ a3 == 1) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 0 /\ a1 == -1 /\ a2 == -1 /\ a3 == -1) then (b0 = 0 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == 0 /\ a3 == 0) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == 0 /\ a3 == 1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == 0 /\ a3 == -1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == 1 /\ a3 == 0) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == 1 /\ a3 == 1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == 1 /\ a3 == -1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == -1 /\ a3 == 0) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == -1 /\ a3 == 1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 1 /\ a1 == 0 /\ a2 == -1 /\ a3 == -1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == 0 /\ a3 == 0) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == 0 /\ a3 == 1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == 0 /\ a3 == -1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == 1 /\ a3 == 0) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == 1 /\ a3 == 1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == 1 /\ a3 == -1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == -1 /\ a3 == 0) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == -1 /\ a3 == 1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 1 /\ a1 == 1 /\ a2 == -1 /\ a3 == -1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == -1 /\ a2 == 0 /\ a3 == 0) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 1 /\ a1 == -1 /\ a2 == 0 /\ a3 == 1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 1 /\ a1 == -1 /\ a2 == 0 /\ a3 == -1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == -1 /\ a2 == 1 /\ a3 == 0) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 1 /\ a1 == -1 /\ a2 == 1 /\ a3 == 1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 1 /\ a1 == -1 /\ a2 == 1 /\ a3 == -1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == 1 /\ a1 == -1 /\ a2 == -1 /\ a3 == 0) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == 1 /\ a1 == -1 /\ a2 == -1 /\ a3 == 1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == 1 /\ a1 == -1 /\ a2 == -1 /\ a3 == -1) then (b0 = 1 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    elseif (a0 == -1 /\ a1 == 0 /\ a2 == 0 /\ a3 == 0) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == -1 /\ a1 == 0 /\ a2 == 0 /\ a3 == 1) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == -1 /\ a1 == 0 /\ a2 == 1 /\ a3 == 0) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == -1 /\ a1 == 0 /\ a2 == 1 /\ a3 == 1) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == -1 /\ a1 == 0 /\ a2 == -1 /\ a3 == 0) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == -1 /\ a1 == 0 /\ a2 == -1 /\ a3 == 1) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == -1 /\ a1 == 1 /\ a2 == 0 /\ a3 == 0) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == -1 /\ a1 == 1 /\ a2 == 0 /\ a3 == 1) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == -1 /\ a1 == 1 /\ a2 == 1 /\ a3 == 0) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == -1 /\ a1 == 1 /\ a2 == 1 /\ a3 == 1) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == -1 /\ a1 == 1 /\ a2 == -1 /\ a3 == 0) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == -1 /\ a1 == 1 /\ a2 == -1 /\ a3 == 1) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == -1 /\ a1 == -1 /\ a2 == 0 /\ a3 == 0) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == -1 /\ a1 == -1 /\ a2 == 0 /\ a3 == 1) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == -1 /\ a1 == -1 /\ a2 == 1 /\ a3 == 0) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == -1 /\ a1 == -1 /\ a2 == 1 /\ a3 == 1) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    elseif (a0 == -1 /\ a1 == -1 /\ a2 == -1 /\ a3 == 0) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 0)
    elseif (a0 == -1 /\ a1 == -1 /\ a2 == -1 /\ a3 == 1) then (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = 1)
    else (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    endif;
    
% XOR-Bitwise function
function var D: XOR(var D: a, var D: b, var D: c) =
  if a == -1 \/ b == -1 \/ c == -1 then
    -1  % If any input is unknown, the output is unknown
  else 
    (a + b + c) mod 2  % Bitwise XOR
  endif;