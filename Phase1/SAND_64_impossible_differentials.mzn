include "globals.mzn";

%==============================================================================
% SAND-64 impossible-differential search (miss-in-the-middle)
%
% Joint-DDT (synthetic S-box SSb) version.
%
% In one round, input nibble j of Delta X feeds *two* G-boxes:
%     * G0's box  j        -> G0 output nibble j
%     * G1's box (j-1)     -> G1 output nibble (j-1) mod word
%   (G1's input is the state rotated left by one nibble).
% Both therefore consume the SAME 4-bit input value, so their output
% differences are not independent.  This model treats the pair as a single
% 4-bit -> 8-bit synthetic S-box
%     SSb(x) = G0(x) || G1(x)
% and uses its JOINT DDT instead of the product of the two marginal DDTs.
% The joint DDT has 97 realizable (din, dG0, dG1) triples, whereas the product
% of the marginals would admit 157 (e.g. din = 0x6 with (dG0, dG1) = (0x6, 0x2)
% is a spurious combination).
%
% Two places use it:
%   (1) SSB_DET  - deterministic bit-wise propagation, posted as one table
%                  constraint per shared input nibble instead of two separate
%                  g0_box / g1_box predicates.  Same 0/1/? results as before
%                  (a bit-wise abstraction cannot see the correlation) but it
%                  is a single relation, so the solver propagates it in both
%                  directions at once.
%   (2) SSB_SUP  - the 97 joint triples themselves, available for a meeting
%                  point test that asks whether ANY jointly realizable triple
%                  is compatible with both the forward and the backward
%                  pattern.  Disabled by default: see the note at the test,
%                  it provably never fires under this bit-wise abstraction.
%
% Bottom line: replacing the two marginal G-box tables by the joint SSb table
% does NOT change the set of solutions of this model (verified: the joint
% deterministic table reproduces the old g0_box / g1_box entries exactly).
% It makes the shared-input structure explicit and turns two reified
% if-then-else chains into one table constraint over the 12 involved variables.
%
% Bit order: index 0 is the MSB of a nibble, index 3 the LSB.
%==============================================================================

int: rounds = 11;    % Number of rounds (adjust as needed)
int: word = 8;      % 8 or 16
int: n=32;

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

% G1's box that consumes input nibble j produces output nibble (j-1) mod word
function int: g1out(int: j) = (j + word - 1) mod word;

% Forward:Round function constraints ========================================
% State loading
constraint forall(w in 0..word-1, i in 0..3)(
    PL[i+4*w] = XU[0, i, w] /\
    PR[i+4*w] = YU[0, i, w]
);

% Input constraints
constraint sum(i in 0..3, w in 0..word-1) (XU[0, i, w] + YU[0, i, w]) != 0;

% SSb layer: one joint constraint per shared input nibble
constraint forall(r in 0..rounds-1, j in 0..word-1) (
  ssb_box([XU[r,i,j] | i in 0..3],
          [G0_U[r,i,j] | i in 0..3],
          [G1_U[r,i,g1out(j)] | i in 0..3])
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

% SSb layer: one joint constraint per shared input nibble
constraint forall(r in 0..rounds-1, j in 0..word-1) (
  ssb_box([XL[r,i,j] | i in 0..3],
          [G0_L[r,i,j] | i in 0..3],
          [G1_L[r,i,g1out(j)] | i in 0..3])
);

% Linear layer
constraint forall(r in 0..rounds-1, j in 0..3, w in 0..word-1) (
  XL[r, j, w] = YL[r+1, j, w] /\
  YL[r, j, w] = XOR(G0_L[r, j, P[w]], G1_L[r, j, P[w]], XL[r+1, j, w])
);
%=============================================================================

% constraints for the meeting point ==========================================
% (a) bit-wise clashes (0 in one direction, 1 in the other)
array[0..rounds-1, 0..3, 0..word-1] of var 0..1: contradict_x;
array[0..rounds-1, 0..3, 0..word-1] of var 0..1: contradict_y;
array[0..rounds-1, 0..3, 0..word-1] of var 0..1: contradict_g0;
array[0..rounds-1, 0..3, 0..word-1] of var 0..1: contradict_g1;
constraint forall(r in 0..rounds-1, i in 0..3, w in 0..word-1)(contradict_x[r, i, w] = bool2int(XU[r, i, w] + XL[r, i, w] == 1));
constraint forall(r in 0..rounds-1, i in 0..3, w in 0..word-1)(contradict_y[r, i, w] = bool2int(YU[r, i, w] + YL[r, i, w] == 1));
constraint forall(r in 0..rounds-1, i in 0..3, w in 0..word-1)(contradict_g0[r, i, w] = bool2int(G0_U[r, i, w] + G0_L[r, i, w] == 1));
constraint forall(r in 0..rounds-1, i in 0..3, w in 0..word-1)(contradict_g1[r, i, w] = bool2int(G1_U[r, i, w] + G1_L[r, i, w] == 1));

% (b) SSb-level clashes detected by the joint DDT.
% For round r and shared input nibble j collect the 12 bits
%   0..3  : Delta X   nibble j          (SSb input difference)
%   4..7  : G0 output nibble j
%   8..11 : G1 output nibble (j-1) mod word
% from the forward and from the backward propagation.  The real trail has one
% concrete triple that both patterns must cover and that must be jointly
% realizable; if no such triple exists the differential is impossible.
% For v in D the test "v may equal bit b" is exactly "v != 1-b".
array[0..rounds-1, 0..word-1, 0..11] of var D: SSB_FW =
  array3d(0..rounds-1, 0..word-1, 0..11,
    [ if   k <= 3 then XU[r, k, j]
      elseif k <= 7 then G0_U[r, k-4, j]
      else               G1_U[r, k-8, g1out(j)] endif
    | r in 0..rounds-1, j in 0..word-1, k in 0..11 ]);
array[0..rounds-1, 0..word-1, 0..11] of var D: SSB_BW =
  array3d(0..rounds-1, 0..word-1, 0..11,
    [ if   k <= 3 then XL[r, k, j]
      elseif k <= 7 then G0_L[r, k-4, j]
      else               G1_L[r, k-8, g1out(j)] endif
    | r in 0..rounds-1, j in 0..word-1, k in 0..11 ]);

% NOTE (measured, not guessed): with the purely deterministic 0/1/? abstraction
% used here this test never fires.  SSB_FW and SSB_BW are always one of the 81
% rows of SSB_DET, and for all 81 x 81 = 6561 reachable pattern pairs every
% jointly-impossible combination already shows a bit-wise 0-vs-1 clash
% (4160 bit-wise clashes, 0 joint-only).  The correlation between dG0 and dG1
% is destroyed the moment each output nibble is reduced to its bit-wise hull,
% so the joint DDT can only bite in an exact-difference model (as in the SAT
% differential search).  The check is therefore off by default; set
% joint_meet_check = true to re-enable it (it roughly triples flattening time).
bool: joint_meet_check = false;

array[0..rounds-1, 0..word-1] of var 0..1: contradict_ssb;
constraint if joint_meet_check then
  forall(r in 0..rounds-1, j in 0..word-1)(
    contradict_ssb[r, j] = 1 - bool2int(
      exists(s in 1..SSB_SUP_N)(
        forall(k in 0..11)(
          SSB_FW[r, j, k] != 1 - SSB_SUP[s, k+1] /\
          SSB_BW[r, j, k] != 1 - SSB_SUP[s, k+1]
        )
      )
    )
  )
else
  forall(r in 0..rounds-1, j in 0..word-1)(contradict_ssb[r, j] = 0)
endif;

constraint sum(r in 0..rounds-1, i in 0..3, w in 0..word-1)(
  contradict_x[r, i, w] + contradict_y[r, i, w] + contradict_g0[r, i, w] + contradict_g1[r, i, w]
  ) + sum(r in 0..rounds-1, j in 0..word-1)(contradict_ssb[r, j]) > 0;
%=============================================================================

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

output ["\nContradiction sources: bitwise = " ++
        show(sum(r in 0..rounds-1, i in 0..3, w in 0..word-1)(
          fix(contradict_x[r,i,w]) + fix(contradict_y[r,i,w])
          + fix(contradict_g0[r,i,w]) + fix(contradict_g1[r,i,w]))) ++
        ", joint-SSb = " ++
        show(sum(r in 0..rounds-1, j in 0..word-1)(fix(contradict_ssb[r,j])))];

output ["\n\nNo non-fixed input bits: " ++ show(sum(i in 0..3, w in 0..word-1)(bool2int(XU[0, i, w] == -1)+bool2int(YU[0, i, w] == -1)+bool2int(XL[rounds, i, w] == -1)+bool2int(YL[rounds, i, w] == -1)))];

%==============================================================================
% Synthetic S-box SSb = (G0, G1), shared 4-bit input nibble
%
%   G0:  y2 = x2                  G1:  y3 = x3
%        y1 = x1                       y2 = (x3 & x1) xor x2
%        y0 = (x3 & x2) xor x0         y1 = (y2 & x0) xor x1
%        y3 = (y0 & x1) xor x3         y0 = x0
%   (x3 = MSB; a0/b0/c0 below are the MSBs)
%==============================================================================

% Deterministic bit-wise differential transition of the whole SSb.
% Columns 0..3 : input difference pattern (81 patterns over {0,1,?})
%         4..7 : G0 output difference pattern
%         8..11: G1 output difference pattern
% Posted as a table, i.e. as ONE relation over the 12 variables.
predicate ssb_box(array[int] of var D: a, array[int] of var D: b, array[int] of var D: c) =
  table(a ++ b ++ c, SSB_DET);

int: SSB_DET_N = 81;
array[1..SSB_DET_N, 1..12] of int: SSB_DET = array2d(1..SSB_DET_N, 1..12, [
   0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
   0,  0,  0,  1, -1,  0,  0,  1,  0,  0, -1,  1,
   0,  0,  0, -1, -1,  0,  0, -1,  0,  0, -1, -1,
   0,  0,  1,  0, -1,  0,  1,  0,  0, -1, -1,  0,
   0,  0,  1,  1, -1,  0,  1,  1,  0, -1, -1,  1,
   0,  0,  1, -1, -1,  0,  1, -1,  0, -1, -1, -1,
   0,  0, -1,  0, -1,  0, -1,  0,  0, -1, -1,  0,
   0,  0, -1,  1, -1,  0, -1,  1,  0, -1, -1,  1,
   0,  0, -1, -1, -1,  0, -1, -1,  0, -1, -1, -1,
   0,  1,  0,  0, -1,  1,  0, -1,  0,  1, -1,  0,
   0,  1,  0,  1, -1,  1,  0, -1,  0,  1, -1,  1,
   0,  1,  0, -1, -1,  1,  0, -1,  0,  1, -1, -1,
   0,  1,  1,  0, -1,  1,  1, -1,  0, -1, -1,  0,
   0,  1,  1,  1, -1,  1,  1, -1,  0, -1, -1,  1,
   0,  1,  1, -1, -1,  1,  1, -1,  0, -1, -1, -1,
   0,  1, -1,  0, -1,  1, -1, -1,  0, -1, -1,  0,
   0,  1, -1,  1, -1,  1, -1, -1,  0, -1, -1,  1,
   0,  1, -1, -1, -1,  1, -1, -1,  0, -1, -1, -1,
   0, -1,  0,  0, -1, -1,  0, -1,  0, -1, -1,  0,
   0, -1,  0,  1, -1, -1,  0, -1,  0, -1, -1,  1,
   0, -1,  0, -1, -1, -1,  0, -1,  0, -1, -1, -1,
   0, -1,  1,  0, -1, -1,  1, -1,  0, -1, -1,  0,
   0, -1,  1,  1, -1, -1,  1, -1,  0, -1, -1,  1,
   0, -1,  1, -1, -1, -1,  1, -1,  0, -1, -1, -1,
   0, -1, -1,  0, -1, -1, -1, -1,  0, -1, -1,  0,
   0, -1, -1,  1, -1, -1, -1, -1,  0, -1, -1,  1,
   0, -1, -1, -1, -1, -1, -1, -1,  0, -1, -1, -1,
   1,  0,  0,  0, -1,  0,  0, -1,  1, -1, -1,  0,
   1,  0,  0,  1, -1,  0,  0, -1,  1, -1, -1,  1,
   1,  0,  0, -1, -1,  0,  0, -1,  1, -1, -1, -1,
   1,  0,  1,  0, -1,  0,  1, -1,  1, -1, -1,  0,
   1,  0,  1,  1, -1,  0,  1, -1,  1, -1, -1,  1,
   1,  0,  1, -1, -1,  0,  1, -1,  1, -1, -1, -1,
   1,  0, -1,  0, -1,  0, -1, -1,  1, -1, -1,  0,
   1,  0, -1,  1, -1,  0, -1, -1,  1, -1, -1,  1,
   1,  0, -1, -1, -1,  0, -1, -1,  1, -1, -1, -1,
   1,  1,  0,  0, -1,  1,  0, -1,  1, -1, -1,  0,
   1,  1,  0,  1, -1,  1,  0, -1,  1, -1, -1,  1,
   1,  1,  0, -1, -1,  1,  0, -1,  1, -1, -1, -1,
   1,  1,  1,  0, -1,  1,  1, -1,  1, -1, -1,  0,
   1,  1,  1,  1, -1,  1,  1, -1,  1, -1, -1,  1,
   1,  1,  1, -1, -1,  1,  1, -1,  1, -1, -1, -1,
   1,  1, -1,  0, -1,  1, -1, -1,  1, -1, -1,  0,
   1,  1, -1,  1, -1,  1, -1, -1,  1, -1, -1,  1,
   1,  1, -1, -1, -1,  1, -1, -1,  1, -1, -1, -1,
   1, -1,  0,  0, -1, -1,  0, -1,  1, -1, -1,  0,
   1, -1,  0,  1, -1, -1,  0, -1,  1, -1, -1,  1,
   1, -1,  0, -1, -1, -1,  0, -1,  1, -1, -1, -1,
   1, -1,  1,  0, -1, -1,  1, -1,  1, -1, -1,  0,
   1, -1,  1,  1, -1, -1,  1, -1,  1, -1, -1,  1,
   1, -1,  1, -1, -1, -1,  1, -1,  1, -1, -1, -1,
   1, -1, -1,  0, -1, -1, -1, -1,  1, -1, -1,  0,
   1, -1, -1,  1, -1, -1, -1, -1,  1, -1, -1,  1,
   1, -1, -1, -1, -1, -1, -1, -1,  1, -1, -1, -1,
  -1,  0,  0,  0, -1,  0,  0, -1, -1, -1, -1,  0,
  -1,  0,  0,  1, -1,  0,  0, -1, -1, -1, -1,  1,
  -1,  0,  0, -1, -1,  0,  0, -1, -1, -1, -1, -1,
  -1,  0,  1,  0, -1,  0,  1, -1, -1, -1, -1,  0,
  -1,  0,  1,  1, -1,  0,  1, -1, -1, -1, -1,  1,
  -1,  0,  1, -1, -1,  0,  1, -1, -1, -1, -1, -1,
  -1,  0, -1,  0, -1,  0, -1, -1, -1, -1, -1,  0,
  -1,  0, -1,  1, -1,  0, -1, -1, -1, -1, -1,  1,
  -1,  0, -1, -1, -1,  0, -1, -1, -1, -1, -1, -1,
  -1,  1,  0,  0, -1,  1,  0, -1, -1, -1, -1,  0,
  -1,  1,  0,  1, -1,  1,  0, -1, -1, -1, -1,  1,
  -1,  1,  0, -1, -1,  1,  0, -1, -1, -1, -1, -1,
  -1,  1,  1,  0, -1,  1,  1, -1, -1, -1, -1,  0,
  -1,  1,  1,  1, -1,  1,  1, -1, -1, -1, -1,  1,
  -1,  1,  1, -1, -1,  1,  1, -1, -1, -1, -1, -1,
  -1,  1, -1,  0, -1,  1, -1, -1, -1, -1, -1,  0,
  -1,  1, -1,  1, -1,  1, -1, -1, -1, -1, -1,  1,
  -1,  1, -1, -1, -1,  1, -1, -1, -1, -1, -1, -1,
  -1, -1,  0,  0, -1, -1,  0, -1, -1, -1, -1,  0,
  -1, -1,  0,  1, -1, -1,  0, -1, -1, -1, -1,  1,
  -1, -1,  0, -1, -1, -1,  0, -1, -1, -1, -1, -1,
  -1, -1,  1,  0, -1, -1,  1, -1, -1, -1, -1,  0,
  -1, -1,  1,  1, -1, -1,  1, -1, -1, -1, -1,  1,
  -1, -1,  1, -1, -1, -1,  1, -1, -1, -1, -1, -1,
  -1, -1, -1,  0, -1, -1, -1, -1, -1, -1, -1,  0,
  -1, -1, -1,  1, -1, -1, -1, -1, -1, -1, -1,  1,
  -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
]);

% Joint DDT support: the 97 triples (din, dG0, dG1) that are simultaneously
% realizable by a single input value x.  The product of the two marginal DDTs
% would contain 157 triples; the extra 60 are the ones this table removes.
int: SSB_SUP_N = 97;
array[1..SSB_SUP_N, 1..12] of int: SSB_SUP = array2d(1..SSB_SUP_N, 1..12, [
   0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
   0,  0,  0,  1,  0,  0,  0,  1,  0,  0,  0,  1,
   0,  0,  0,  1,  0,  0,  0,  1,  0,  0,  1,  1,
   0,  0,  0,  1,  1,  0,  0,  1,  0,  0,  0,  1,
   0,  0,  0,  1,  1,  0,  0,  1,  0,  0,  1,  1,
   0,  0,  1,  0,  0,  0,  1,  0,  0,  0,  1,  0,
   0,  0,  1,  0,  0,  0,  1,  0,  0,  1,  0,  0,
   0,  0,  1,  0,  0,  0,  1,  0,  0,  1,  1,  0,
   0,  0,  1,  0,  1,  0,  1,  0,  0,  0,  1,  0,
   0,  0,  1,  0,  1,  0,  1,  0,  0,  1,  0,  0,
   0,  0,  1,  0,  1,  0,  1,  0,  0,  1,  1,  0,
   0,  0,  1,  1,  0,  0,  1,  1,  0,  0,  0,  1,
   0,  0,  1,  1,  0,  0,  1,  1,  0,  0,  1,  1,
   0,  0,  1,  1,  0,  0,  1,  1,  0,  1,  1,  1,
   0,  0,  1,  1,  1,  0,  1,  1,  0,  0,  0,  1,
   0,  0,  1,  1,  1,  0,  1,  1,  0,  0,  1,  1,
   0,  0,  1,  1,  1,  0,  1,  1,  0,  1,  0,  1,
   0,  1,  0,  0,  0,  1,  0,  0,  0,  1,  0,  0,
   0,  1,  0,  0,  0,  1,  0,  0,  0,  1,  1,  0,
   0,  1,  0,  0,  0,  1,  0,  1,  0,  1,  0,  0,
   0,  1,  0,  0,  0,  1,  0,  1,  0,  1,  1,  0,
   0,  1,  0,  0,  1,  1,  0,  1,  0,  1,  0,  0,
   0,  1,  0,  0,  1,  1,  0,  1,  0,  1,  1,  0,
   0,  1,  0,  1,  0,  1,  0,  0,  0,  1,  0,  1,
   0,  1,  0,  1,  0,  1,  0,  0,  0,  1,  1,  1,
   0,  1,  0,  1,  0,  1,  0,  1,  0,  1,  0,  1,
   0,  1,  0,  1,  0,  1,  0,  1,  0,  1,  1,  1,
   0,  1,  0,  1,  1,  1,  0,  1,  0,  1,  0,  1,
   0,  1,  0,  1,  1,  1,  0,  1,  0,  1,  1,  1,
   0,  1,  1,  0,  0,  1,  1,  0,  0,  1,  1,  0,
   0,  1,  1,  0,  0,  1,  1,  1,  0,  0,  1,  0,
   0,  1,  1,  0,  1,  1,  1,  0,  0,  1,  0,  0,
   0,  1,  1,  0,  1,  1,  1,  1,  0,  0,  1,  0,
   0,  1,  1,  1,  0,  1,  1,  0,  0,  0,  0,  1,
   0,  1,  1,  1,  0,  1,  1,  0,  0,  0,  1,  1,
   0,  1,  1,  1,  0,  1,  1,  1,  0,  1,  0,  1,
   0,  1,  1,  1,  0,  1,  1,  1,  0,  1,  1,  1,
   0,  1,  1,  1,  1,  1,  1,  0,  0,  0,  0,  1,
   0,  1,  1,  1,  1,  1,  1,  0,  0,  0,  1,  1,
   0,  1,  1,  1,  1,  1,  1,  1,  0,  1,  0,  1,
   0,  1,  1,  1,  1,  1,  1,  1,  0,  1,  1,  1,
   1,  0,  0,  0,  0,  0,  0,  1,  1,  1,  0,  0,
   1,  0,  0,  0,  0,  0,  0,  1,  1,  1,  1,  0,
   1,  0,  0,  0,  1,  0,  0,  0,  1,  0,  0,  0,
   1,  0,  0,  0,  1,  0,  0,  0,  1,  1,  0,  0,
   1,  0,  0,  0,  1,  0,  0,  0,  1,  1,  1,  0,
   1,  0,  0,  0,  1,  0,  0,  1,  1,  0,  0,  0,
   1,  0,  0,  1,  0,  0,  0,  1,  1,  1,  0,  1,
   1,  0,  0,  1,  0,  0,  0,  1,  1,  1,  1,  1,
   1,  0,  0,  1,  1,  0,  0,  0,  1,  0,  1,  1,
   1,  0,  0,  1,  1,  0,  0,  0,  1,  1,  0,  1,
   1,  0,  0,  1,  1,  0,  0,  0,  1,  1,  1,  1,
   1,  0,  0,  1,  1,  0,  0,  1,  1,  0,  0,  1,
   1,  0,  1,  0,  0,  0,  1,  0,  1,  0,  1,  0,
   1,  0,  1,  0,  0,  0,  1,  0,  1,  1,  0,  0,
   1,  0,  1,  0,  0,  0,  1,  1,  1,  0,  1,  0,
   1,  0,  1,  0,  0,  0,  1,  1,  1,  1,  1,  0,
   1,  0,  1,  0,  1,  0,  1,  0,  1,  0,  1,  0,
   1,  0,  1,  0,  1,  0,  1,  0,  1,  1,  1,  0,
   1,  0,  1,  0,  1,  0,  1,  1,  1,  0,  1,  0,
   1,  0,  1,  0,  1,  0,  1,  1,  1,  1,  0,  0,
   1,  0,  1,  1,  0,  0,  1,  0,  1,  0,  0,  1,
   1,  0,  1,  1,  0,  0,  1,  0,  1,  1,  0,  1,
   1,  0,  1,  1,  0,  0,  1,  1,  1,  0,  1,  1,
   1,  0,  1,  1,  0,  0,  1,  1,  1,  1,  0,  1,
   1,  0,  1,  1,  1,  0,  1,  0,  1,  0,  0,  1,
   1,  0,  1,  1,  1,  0,  1,  0,  1,  1,  1,  1,
   1,  0,  1,  1,  1,  0,  1,  1,  1,  0,  1,  1,
   1,  0,  1,  1,  1,  0,  1,  1,  1,  1,  1,  1,
   1,  1,  0,  0,  0,  1,  0,  1,  1,  0,  0,  0,
   1,  1,  0,  0,  1,  1,  0,  0,  1,  0,  0,  0,
   1,  1,  0,  0,  1,  1,  0,  0,  1,  1,  0,  0,
   1,  1,  0,  0,  1,  1,  0,  0,  1,  1,  1,  0,
   1,  1,  0,  0,  1,  1,  0,  1,  1,  1,  0,  0,
   1,  1,  0,  0,  1,  1,  0,  1,  1,  1,  1,  0,
   1,  1,  0,  1,  0,  1,  0,  1,  1,  0,  1,  1,
   1,  1,  0,  1,  1,  1,  0,  0,  1,  0,  0,  1,
   1,  1,  0,  1,  1,  1,  0,  0,  1,  1,  0,  1,
   1,  1,  0,  1,  1,  1,  0,  0,  1,  1,  1,  1,
   1,  1,  0,  1,  1,  1,  0,  1,  1,  1,  0,  1,
   1,  1,  0,  1,  1,  1,  0,  1,  1,  1,  1,  1,
   1,  1,  1,  0,  0,  1,  1,  0,  1,  0,  1,  0,
   1,  1,  1,  0,  0,  1,  1,  0,  1,  1,  0,  0,
   1,  1,  1,  0,  0,  1,  1,  1,  1,  0,  1,  0,
   1,  1,  1,  0,  0,  1,  1,  1,  1,  1,  0,  0,
   1,  1,  1,  0,  1,  1,  1,  0,  1,  0,  1,  0,
   1,  1,  1,  0,  1,  1,  1,  0,  1,  1,  1,  0,
   1,  1,  1,  0,  1,  1,  1,  1,  1,  0,  1,  0,
   1,  1,  1,  0,  1,  1,  1,  1,  1,  1,  1,  0,
   1,  1,  1,  1,  0,  1,  1,  0,  1,  0,  1,  1,
   1,  1,  1,  1,  0,  1,  1,  0,  1,  1,  1,  1,
   1,  1,  1,  1,  0,  1,  1,  1,  1,  0,  0,  1,
   1,  1,  1,  1,  0,  1,  1,  1,  1,  1,  0,  1,
   1,  1,  1,  1,  1,  1,  1,  0,  1,  0,  1,  1,
   1,  1,  1,  1,  1,  1,  1,  0,  1,  1,  0,  1,
   1,  1,  1,  1,  1,  1,  1,  1,  1,  0,  0,  1,
   1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1
]);

% XOR-Bitwise function
function var D: XOR(var D: a, var D: b, var D: c) =
  if a == -1 \/ b == -1 \/ c == -1 then
    -1  % If any input is unknown, the output is unknown
  else
    (a + b + c) mod 2  % Bitwise XOR
  endif;
