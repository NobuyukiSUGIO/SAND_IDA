include "globals.mzn";

int: rounds = 11;    % Number of rounds (adjust as needed)
int: word = 8;      % 8 or 16
int: n = 32;

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
constraint forall(r in 0..rounds-1, w in 0..7) (
  g0_box(XU[r,0,w],XU[r,1,w],XU[r,2,w],XU[r,3,w],G0_U[r,0,w],G0_U[r,1,w],G0_U[r,2,w],G0_U[r,3,w]) /\
  g1_box(XU[r,0,(w+1)mod 8],XU[r,1,(w+1)mod 8],XU[r,2,(w+1)mod 8],XU[r,3,(w+1)mod 8],G1_U[r,0,w],G1_U[r,1,w],G1_U[r,2,w],G1_U[r,3,w])
);

% Linear layer Note that MSB=0, LSB=7
array[0..7] of int: P = array1d(0..7, [7,4,1,6,3,0,5,2]);
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
constraint forall(r in 0..rounds-1, w in 0..7) (
  g0_box(XL[r,0,w],XL[r,1,w],XL[r,2,w],XL[r,3,w],G0_L[r,0,w],G0_L[r,1,w],G0_L[r,2,w],G0_L[r,3,w]) /\
  g1_box(XL[r,0,(w+1)mod 8],XL[r,1,(w+1)mod 8],XL[r,2,(w+1)mod 8],XL[r,3,(w+1)mod 8],G1_L[r,0,w],G1_L[r,1,w],G1_L[r,2,w],G1_L[r,3,w])
);

% Linear layer
constraint forall(r in 0..rounds-1, j in 0..3, w in 0..word-1) (
  XL[r, j, w] = YL[r+1, j, w] /\
  YL[r, j, w] = XOR(G0_L[r, j, P[w]], G1_L[r, j, P[w]], XL[r+1, j, w])
);
%=============================================================================

% Key Recovery ===============================================================
int: r_in = 3;
int: r_out = 2;
% State variables ------------------------------------------------------------
array[0..r_in-1, 0..3, 0..word-1] of var D : k_in; % k_in
array[0..r_in-1, 0..3, 0..word-1] of var 0..1 : c_in; % c_in
array[0..r_out-1, 0..3, 0..word-1] of var D : k_out; % k_out
array[0..r_out-1, 0..3, 0..word-1] of var 0..1 : c_out; % c_out
array[0..r_in, 0..3, 0..word-1] of var D: XL_KR; % Backward difference variables
array[0..r_in, 0..3, 0..word-1] of var D: YL_KR; % Backward difference variables for S-box
array[0..r_in-1, 0..3, 0..word-1] of var D: G0_L_KR; % State variables for G0-box
array[0..r_in-1, 0..3, 0..word-1] of var D: G1_L_KR; % State variables for G1-box
array[0..r_out, 0..3, 0..word-1] of var D: XU_KR; % State variables for Left 
array[0..r_out, 0..3, 0..word-1] of var D: YU_KR; % State variables for Right
array[0..r_out-1, 0..3, 0..word-1] of var D: G0_U_KR; % State variables for G0-box
array[0..r_out-1, 0..3, 0..word-1] of var D: G1_U_KR; % State variables for G1-box

% Backward:Round function constraints ---------------------------------------------------
constraint forall(i in 0..3, w in 0..word-1)(
    XL_KR[r_in, i, w] = XU[0, i, w] /\ 
    YL_KR[r_in, i, w] = YU[0, i, w] 
);

% G-box layer (Bit-wise Deterministic Differential Transitions)
constraint forall(r in 0..r_in-1, w in 0..word-1) (
  gt_box(XL_KR[r,0,w],XL_KR[r,1,w],XL_KR[r,2,w],XL_KR[r,3,w],G0_L_KR[r,0,w],G0_L_KR[r,1,w],G0_L_KR[r,2,w],G0_L_KR[r,3,w]) /\
  gt_box(XL_KR[r,0,(w+1)mod 8],XL_KR[r,1,(w+1)mod 8],XL_KR[r,2,(w+1)mod 8],XL_KR[r,3,(w+1)mod 8],G1_L_KR[r,0,w],G1_L_KR[r,1,w],G1_L_KR[r,2,w],G1_L_KR[r,3,w])
);

% Linear layer
constraint forall(r in 0..r_in-1, j in 0..3, w in 0..word-1) (
  XL_KR[r, j, w] = YL_KR[r+1, j, w] /\
  YL_KR[r, j, w] = XOR(G0_L_KR[r, j, P[w]], G1_L_KR[r, j, P[w]], XL_KR[r+1, j, w])
);

% C_in
constraint forall(r in 0..r_in-1, i in 0..3, w in 0..word-1)(c_in[r, i, w] = bool2int((YL_KR[r, i, w] + XL_KR[r+1, i, w] == 1) \/ (YL_KR[r, i, w] + XL_KR[r+1, i, w] == -1)));

% K_in
constraint forall(r in 0..r_in-1, w in 0..word-1) (
  gt_box(XL_KR[r+1,0,w],XL_KR[r+1,1,w],XL_KR[r+1,2,w],XL_KR[r+1,3,w],k_in[r,0,w],k_in[r,1,w],k_in[r,2,w],k_in[r,3,w])
);
%------------------------------------------------------------------------------------------

% Forward:Round function constraints ------------------------------------------------------
% Input States
constraint forall(i in 0..3, w in 0..word-1)(
    XU_KR[0, i, w] = XL[rounds, i, w] /\ 
    YU_KR[0, i, w] = YL[rounds, i, w]
);

% G-box layer (Bit-wise Deterministic Differential Transitions)
constraint forall(r in 0..r_out-1, w in 0..word-1) (
  gt_box(XU_KR[r,0,w],XU_KR[r,1,w],XU_KR[r,2,w],XU_KR[r,3,w],G0_U_KR[r,0,w],G0_U_KR[r,1,w],G0_U_KR[r,2,w],G0_U_KR[r,3,w]) /\
  gt_box(XU_KR[r,0,(w+1)mod 8],XU_KR[r,1,(w+1)mod 8],XU_KR[r,2,(w+1)mod 8],XU_KR[r,3,(w+1)mod 8],G1_U_KR[r,0,w],G1_U_KR[r,1,w],G1_U_KR[r,2,w],G1_U_KR[r,3,w])
);

% Linear layer Note that MSB=0, LSB=7
constraint forall(r in 0..r_out-1, j in 0..3, w in 0..word-1) (
  YU_KR[r+1, j, w] = XU_KR[r, j, w] /\
  XU_KR[r+1, j, w] = XOR(G0_U_KR[r, j, P[w]], G1_U_KR[r, j, P[w]], YU_KR[r, j, w])
);

% C_out
constraint forall(r in 0..r_out-1, i in 0..3, w in 0..word-1)(c_out[r, i, w] = bool2int((YU_KR[r, i, w] + XU_KR[r+1, i, w] == 1) \/ (YU_KR[r, i, w] + XU_KR[r+1, i, w] == -1)));

% K_out
constraint forall(r in 0..r_out-1, w in 0..word-1) (
  gt_box(YU_KR[r,0,w],YU_KR[r,1,w],YU_KR[r,2,w],YU_KR[r,3,w],k_out[r,0,w],k_out[r,1,w],k_out[r,2,w],k_out[r,3,w])
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
%solve minimize sum(i in 0..3, w in 0..word-1)(XL_KR[0, i, w] + YL_KR[0, i, w] + XU_KR[r_out, i, w] + YU_KR[r_out, i, w]);
%solve minimize sum(r in 0..r_in-1, i in 0..3, w in 0..word-1)(c_in[r, i, w]) + sum(r in 0..r_out-1, i in 0..3, w in 0..word-1)(c_out[r, i, w]);

% Output (adjusted for better readability)
output [
    "XU_" ++ show(r) ++ ": \"" ++
    join("", [if fix(XU[r, i, w]) = -1 then "?" else show(fix(XU[r, i, w])) endif | i in 0..3, w in 0..word-1]) ++ "\"\n"
    | r in 0..rounds];

output [
    "YU_" ++ show(r) ++ ": \"" ++
    join("", [if fix(YU[r, i, w]) = -1 then "?" else show(fix(YU[r, i, w])) endif | i in 0..3, w in 0..word-1]) ++ "\"\n"
    | r in 0..rounds];
    
output ["\n"];

output [
    "XL_" ++ show(r) ++ ": \"" ++
    join("", [if fix(XL[r, i, w]) = -1 then "?" else show(fix(XL[r, i, w])) endif | i in 0..3, w in 0..word-1]) ++ "\"\n"
    | r in 0..rounds];

output [
    "YL_" ++ show(r) ++ ": \"" ++
    join("", [if fix(YL[r, i, w]) = -1 then "?" else show(fix(YL[r, i, w])) endif | i in 0..3, w in 0..word-1]) ++ "\"\n"
    | r in 0..rounds];

output [
    "PL: " ++
    join("", [if fix(PL[i]) = -1 then "?" else show(fix(PL[i])) endif | i in 0..31]) ++ "\"\n"];

output [
    "PR: " ++
    join("", [if fix(PR[i]) = -1 then "?" else show(fix(PR[i])) endif | i in 0..31]) ++ "\"\n"];

output [
    "CL: " ++
    join("", [if fix(CL[i]) = -1 then "?" else show(fix(CL[i])) endif | i in 0..31]) ++ "\"\n"];

output [
    "CR: " ++
    join("", [if fix(CR[i]) = -1 then "?" else show(fix(CR[i])) endif | i in 0..31]) ++ "\"\n"];

output [
    "c_in_" ++ show(r) ++ ": \"" ++
    join("", [show(fix(c_in[r, i, w])) | i in 0..3, w in 0..word-1]) ++ "\"\n"
    | r in 0..r_in-1];

output [
    "c_out_" ++ show(r) ++ ": \"" ++
    join("", [show(fix(c_out[r, i, w])) | i in 0..3, w in 0..word-1]) ++ "\"\n"
    | r in 0..r_out-1];

output [
    "XL_KR_" ++ show(r) ++ ": \"" ++
    join("", [if fix(XL_KR[r, i, w]) = -1 then "?" else show(fix(XL_KR[r, i, w])) endif | i in 0..3, w in 0..word-1]) ++ "\"\n"
    | r in 0..r_in];

output [
    "YL_KR_" ++ show(r) ++ ": \"" ++
    join("", [if fix(YL_KR[r, i, w]) = -1 then "?" else show(fix(YL_KR[r, i, w])) endif | i in 0..3, w in 0..word-1]) ++ "\"\n"
    | r in 0..r_in];
    
output [
    "XU_KR_" ++ show(r) ++ ": \"" ++
    join("", [if fix(XU_KR[r, i, w]) = -1 then "?" else show(fix(XU_KR[r, i, w])) endif | i in 0..3, w in 0..word-1]) ++ "\"\n"
    | r in 0..r_out];

output [
    "YU_KR_" ++ show(r) ++ ": \"" ++
    join("", [if fix(YU_KR[r, i, w]) = -1 then "?" else show(fix(YU_KR[r, i, w])) endif | i in 0..3, w in 0..word-1]) ++ "\"\n"
    | r in 0..r_out];
    
output ["C_in bits: " ++ show(sum(r in 0..r_in-1, i in 0..3, w in 0..word-1)(bool2int(c_in[r, i, w] == 1)))];

output ["\nC_out bits: " ++ show(sum(r in 0..r_out-1, i in 0..3, w in 0..word-1)(bool2int(c_out[r, i, w] == 1)))];

output ["\nk_in bits: " ++ show(sum(r in 0..r_in-1, i in 0..3, w in 0..word-1)(bool2int(k_in[r, i, w] == -1)))];

output ["\nk_out bits: " ++ show(sum(r in 0..r_out-1, i in 0..3, w in 0..word-1)(bool2int(k_out[r, i, w] == -1)))];

output ["\nXL_KR, YL_KR bits: " ++ show(sum(i in 0..3, w in 0..word-1)(bool2int(XL_KR[0, i, w] == -1) + bool2int(YL_KR[0, i, w] == -1)))];

output ["\nXU_KR, YU_KR bits: " ++ show(sum(i in 0..3, w in 0..word-1)(bool2int(XU_KR[r_out, i, w] == -1) + bool2int(YU_KR[r_out, i, w] == -1)))];
                                                                                                                                        
output ["\nNo non-fixed input bits: " ++ show(sum(i in 0..3, w in 0..word-1)(bool2int(XU[0, i, w] == -1) + bool2int(YU[0, i, w] == -1) + bool2int(XL[rounds, i, w] == -1) + bool2int(YL[rounds, i, w] == -1)))];

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
    
% S-box truncated differentials (a0 and b0 are MSBs.)
predicate gt_box(var D: a0,var D: a1, var D: a2, var D: a3, var D: b0,var D: b1, var D: b2, var D: b3,) = 
    if (a0 == 0 /\ a1 == 0 /\ a2 == 0 /\ a3 == 0) then (b0 = 0 /\ b1 = 0 /\ b2 = 0 /\ b3 = 0)
    else (b0 = -1 /\ b1 = -1 /\ b2 = -1 /\ b3 = -1)
    endif;
            
% XOR-Bitwise function
function var D: XOR(var D: a, var D: b, var D: c) =
  if a == -1 \/ b == -1 \/ c == -1 then
    -1  % If any input is unknown, the output is unknown
  else 
    (a + b + c) mod 2  % Bitwise XOR
  endif;