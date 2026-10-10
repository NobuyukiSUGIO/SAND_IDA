include "globals.mzn";

%==============================================================================
% SAND-128 key-recovery-oriented impossible-differential search (Sect. 7.3)
%
% An r_delta-round impossible differential (miss-in-the-middle, same model as
% Phase1/SAND_128_impossible_differentials.mzn: joint SSb table per shared
% input nibble) is searched together with
%   * r_in  rounds appended BEFORE the distinguisher (plaintext side) and
%   * r_out rounds appended AFTER  the distinguisher (ciphertext side),
% so that R_atk = r_in + r_delta + r_out.  Default: Sect. 9.2 / Fig. 8: 4 + 14 + 3 = 21 rounds.
%
% In the appended rounds differences are propagated in the truncated
% (nibble-wise) sense: an active G-box input nibble gives an unknown output
% nibble.  The model counts, as in Eq. (1), (2) of the paper,
%   c_in, c_out  : bit conditions of the transitions Delta_in -> Delta_X and
%                  Delta_out -> Delta_Y,
%   k_in, k_out  : subkey bits that must be guessed for partial
%                  encryption / decryption,
%   |Delta_in|, |Delta_out| : unknown (active) bits of the plaintext and
%                  ciphertext difference sets,
% and prints the resulting data / time / memory estimate for N = N_min.
%
% Round function: x_{r+1} = P_n(G0(x_r) xor G1(x_r <<< 1)) xor y_r xor sk_r,
%                 y_{r+1} = x_r.
%
% Bit-condition rule (one condition per bit):
%   round r, bit b : the propagated part P_n(dG) is unknown but the target
%                    difference bit is FIXED (0 or 1).
% Subkey rule (one nibble = 4 bits of sk_r):
%   A subkey nibble is guessed iff the VALUE of the state nibble it is xored
%   into must be computed.  The value of x_r[w] is needed
%     - if nibble w of Delta x_r is active in an appended round (its G-box
%       output difference must be computed), or
%     - recursively, if it feeds a needed nibble: output column c of P_n
%       receives G0 column P[c] (input column P[c]) and G1 column P[c]
%       (input column P[c]+1 mod word), so x_{r+1}[c] needs x_r[P[c]],
%       x_r[P[c]+1] and y_r[c] = x_{r-1}[c], and sk_r[c].
%   input side  : x_0, y_0 are known (plaintext); x_r[c] for r >= 1 needs
%                 sk_{r-1}[c].  sk_{r_in-1} is never needed.
%   output side : x_{R-1} = y_R is known (ciphertext); for t <= R-2,
%                 x_t = y_{t+1} = P_n(G(x_{t+1})) xor x_{t+2} xor sk_{t+1}
%                 needs sk_{t+1}[c], x_{t+1}[P[c]], x_{t+1}[P[c]+1] and
%                 x_{t+2}[c].  sk_{r_in+r_delta} is never needed.
% (Columns are indexed as in the model: w = 0 is the leftmost (MSB) column.)
%
% Objective (-D obj_mode=<0|1|2>, default 0):
%   0 : minimise |k_in u k_out|                       (paper, Sect. 7.3)
%   1 : minimise |k_in u k_out|, then c_in + c_out, then maximise
%       |Delta_in| + |Delta_out| (lexicographic; smaller data complexity)
%   2 : minimise c_in + c_out
% The objective is only a surrogate; candidates must be evaluated with the
% complete formulas (printed at the end of the output).
%
% Optional unknown seeding (Phase 2, Sect. 5.3): set
%   -D unknown_bit_position_i=<0..2n-1> / -D unknown_bit_position_j=<0..2n-1>
%   to force that bit of the distinguisher input / output to '?' (bit
%   numbering as in Phase2/SAND_128_with_i_and_j.mzn; default: disabled).
%
% Bit order: index 0 is the MSB of a nibble, index 3 the LSB.
%==============================================================================

int: rounds = 14;    % r_delta: rounds of the impossible differential
int: word = 16;      % 8 for SAND-64, 16 for SAND-128
int: n = 64;          % 32 for SAND-64, 64 for SAND-128 (= 4*word, half block)
int: r_in = 4;      % rounds appended before the distinguisher
int: r_out = 3;     % rounds appended after the distinguisher
int: key_size = 128;  % |K|

% Optional parameters, settable with -D (e.g. -D obj_mode=1)
opt int: obj_mode;                % default 0, see header
opt int: unknown_bit_position_i;  % default: no seeding, else 0 .. 2n-1
opt int: unknown_bit_position_j;  % default: no seeding, else 0 .. 2n-1
opt int: data_log2;               % available plaintexts 2^data_log2 (default 125, paper)
int: OBJ_MODE = if occurs(obj_mode) then deopt(obj_mode) else 0 endif;
int: SEED_I = if occurs(unknown_bit_position_i) then deopt(unknown_bit_position_i) else -1 endif;
int: SEED_J = if occurs(unknown_bit_position_j) then deopt(unknown_bit_position_j) else -1 endif;
int: DATA = if occurs(data_log2) then deopt(data_log2) else 125 endif;
constraint assert(r_in >= 1 /\ r_out >= 1, "r_in and r_out must be >= 1");
constraint assert(OBJ_MODE in 0..2, "obj_mode must be 0, 1 or 2");
constraint assert(DATA in 1..2*n, "data_log2 must satisfy 1 <= data_log2 <= " ++ show(2*n));
constraint assert(-1 <= SEED_I /\ SEED_I < 2*n,
                  "unknown_bit_position_i must satisfy 0 <= i < " ++ show(2*n));
constraint assert(-1 <= SEED_J /\ SEED_J < 2*n,
                  "unknown_bit_position_j must satisfy 0 <= j < " ++ show(2*n));

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

% Optional unknown seeding of the distinguisher input
constraint forall(i in 0..3, w in 0..word-1) (
  if   word*i + w     == SEED_I then XU[0, i, w] = -1
  elseif word*i + w + n == SEED_I then YU[0, i, w] = -1
  else true endif
);

% SSb layer: one joint constraint per shared input nibble
constraint forall(r in 0..rounds-1, j in 0..word-1) (
  ssb_box([XU[r,i,j] | i in 0..3],
          [G0_U[r,i,j] | i in 0..3],
          [G1_U[r,i,g1out(j)] | i in 0..3])
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

% Optional unknown seeding of the distinguisher output
constraint forall(i in 0..3, w in 0..word-1) (
  if   word*i + w     == SEED_J then XL[rounds, i, w] = -1
  elseif word*i + w + n == SEED_J then YL[rounds, i, w] = -1
  else true endif
);

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

% Key Recovery ===============================================================
% Input side : XL_KR[r], YL_KR[r] = (Delta x_r, Delta y_r),        0 <= r <= r_in
%              (XL_KR[r_in], YL_KR[r_in]) = distinguisher input  (XU[0], YU[0])
%              (XL_KR[0],    YL_KR[0])    = plaintext set        {Delta_in}
% Output side: XU_KR[r], YU_KR[r] = Delta at round r_in+rounds+r, 0 <= r <= r_out
%              (XU_KR[0],     YU_KR[0])     = distinguisher output (XL[rounds], YL[rounds])
%              (XU_KR[r_out], YU_KR[r_out]) = ciphertext set       {Delta_out}
array[0..r_in, 0..3, 0..word-1] of var D: XL_KR;
array[0..r_in, 0..3, 0..word-1] of var D: YL_KR;
array[0..r_in-1, 0..3, 0..word-1] of var D: G0_L_KR;
array[0..r_in-1, 0..3, 0..word-1] of var D: G1_L_KR;
array[0..r_out, 0..3, 0..word-1] of var D: XU_KR;
array[0..r_out, 0..3, 0..word-1] of var D: YU_KR;
array[0..r_out-1, 0..3, 0..word-1] of var D: G0_U_KR;
array[0..r_out-1, 0..3, 0..word-1] of var D: G1_U_KR;

array[0..r_in-1, 0..3, 0..word-1] of var 0..1: c_in;   % bit conditions, round r
array[0..r_out-1, 0..3, 0..word-1] of var 0..1: c_out; % bit conditions, round r_in+rounds+r
array[0..r_in-1, 0..word-1] of var 0..1: k_in;         % nibble w of sk_r guessed
array[0..r_out-1, 0..word-1] of var 0..1: k_out;       % nibble w of sk_(r_in+rounds+r) guessed

% Truncated G-box: zero nibble -> zero, active nibble -> unknown nibble
predicate gt_box(array[int] of var D: a, array[int] of var D: b) =
  let { var bool: z = forall(k in index_set(a))(a[k] = 0) } in
  forall(k in index_set(b))(b[k] = if z then 0 else -1 endif);

% nibble w of a 3-d state is active (not the all-zero difference)
function var bool: active(array[int, int, int] of var D: s, int: r, int: w) =
  exists(i in 0..3)(s[r, i, w] != 0);

% Input side: backward from the distinguisher input to the plaintext -------
constraint forall(i in 0..3, w in 0..word-1)(
    XL_KR[r_in, i, w] = XU[0, i, w] /\
    YL_KR[r_in, i, w] = YU[0, i, w]
);

constraint forall(r in 0..r_in-1, j in 0..word-1) (
  gt_box([XL_KR[r,i,j] | i in 0..3], [G0_L_KR[r,i,j] | i in 0..3]) /\
  gt_box([XL_KR[r,i,j] | i in 0..3], [G1_L_KR[r,i,g1out(j)] | i in 0..3])
);

constraint forall(r in 0..r_in-1, j in 0..3, w in 0..word-1) (
  XL_KR[r, j, w] = YL_KR[r+1, j, w] /\
  YL_KR[r, j, w] = XOR(G0_L_KR[r, j, P[w]], G1_L_KR[r, j, P[w]], XL_KR[r+1, j, w])
);

% c_in: Delta x_{r+1} = P_n(dG(x_r)) xor Delta y_r with P_n(dG) unknown
% (=> YL_KR[r] = -1) while the target bit Delta x_{r+1} is fixed (0 or 1)
constraint forall(r in 0..r_in-1, i in 0..3, w in 0..word-1)(
  c_in[r, i, w] = bool2int(YL_KR[r, i, w] = -1 /\ XL_KR[r+1, i, w] != -1)
);

% need_in[r, w]: the value of x_r[w] must be computed (see header)
% G-box inputs feeding output column c of P_n: columns P[c] and P[c]+1
function set of int: feed(int: c) = {P[c], (P[c] + 1) mod word};
array[0..r_in-1, 0..word-1] of var bool: need_in;
constraint forall(r in 0..r_in-1, w in 0..word-1)(
  need_in[r, w] = (
       (r >= 1 /\ active(XL_KR, r, w))
    \/ exists(c in 0..word-1 where w in feed(c) /\ r+1 <= r_in-1)(need_in[r+1, c])
    \/ (r+2 <= r_in-1 /\ need_in[min(r+2, r_in-1), w]))
);

% k_in: sk_r[w] is needed iff the value of x_{r+1}[w] is needed, 0 <= r <= r_in-2
constraint forall(r in 0..r_in-1, w in 0..word-1)(
  k_in[r, w] = if r <= r_in-2 then bool2int(need_in[min(r+1, r_in-1), w]) else 0 endif
);

% Output side: forward from the distinguisher output to the ciphertext -----
constraint forall(i in 0..3, w in 0..word-1)(
    XU_KR[0, i, w] = XL[rounds, i, w] /\
    YU_KR[0, i, w] = YL[rounds, i, w]
);

constraint forall(r in 0..r_out-1, j in 0..word-1) (
  gt_box([XU_KR[r,i,j] | i in 0..3], [G0_U_KR[r,i,j] | i in 0..3]) /\
  gt_box([XU_KR[r,i,j] | i in 0..3], [G1_U_KR[r,i,g1out(j)] | i in 0..3])
);

constraint forall(r in 0..r_out-1, j in 0..3, w in 0..word-1) (
  YU_KR[r+1, j, w] = XU_KR[r, j, w] /\
  XU_KR[r+1, j, w] = XOR(G0_U_KR[r, j, P[w]], G1_U_KR[r, j, P[w]], YU_KR[r, j, w])
);

% c_out: Delta y_t = P_n(dG(x_t)) xor Delta x_{t+1} (decryption) with
% P_n(dG) unknown (=> XU_KR[r+1] = -1) while Delta y_t is fixed (0 or 1)
constraint forall(r in 0..r_out-1, i in 0..3, w in 0..word-1)(
  c_out[r, i, w] = bool2int(XU_KR[r+1, i, w] = -1 /\ YU_KR[r, i, w] != -1)
);

% need_out[r, w]: the value of x_t[w], t = r_in+rounds+r, must be computed
array[0..r_out-1, 0..word-1] of var bool: need_out;
constraint forall(r in 0..r_out-1, w in 0..word-1)(
  need_out[r, w] = (
       active(XU_KR, r, w)
    \/ exists(c in 0..word-1 where w in feed(c) /\ r-1 >= 0)(need_out[max(r-1, 0), c])
    \/ (r-2 >= 0 /\ need_out[max(r-2, 0), w]))
);

% k_out: sk_t (t = r_in+rounds+r, 1 <= r <= r_out-1) is needed iff the value
% of x_{t-1}[w] is needed
constraint forall(r in 0..r_out-1, w in 0..word-1)(
  k_out[r, w] = if r >= 1 then bool2int(need_out[max(r-1, 0), w]) else 0 endif
);

% Summary quantities -------------------------------------------------------
var 0..4*word*r_in:  C_IN  = sum(r in 0..r_in-1, i in 0..3, w in 0..word-1)(c_in[r, i, w]);
var 0..4*word*r_out: C_OUT = sum(r in 0..r_out-1, i in 0..3, w in 0..word-1)(c_out[r, i, w]);
var 0..4*word*r_in:  K_IN  = 4 * sum(r in 0..r_in-1, w in 0..word-1)(k_in[r, w]);
var 0..4*word*r_out: K_OUT = 4 * sum(r in 0..r_out-1, w in 0..word-1)(k_out[r, w]);
var 0..2*n: D_IN  = sum(i in 0..3, w in 0..word-1)(bool2int(XL_KR[0, i, w] = -1) + bool2int(YL_KR[0, i, w] = -1));
var 0..2*n: D_OUT = sum(i in 0..3, w in 0..word-1)(bool2int(XU_KR[r_out, i, w] = -1) + bool2int(YU_KR[r_out, i, w] = -1));

% Data complexity C_N of Eq. (1) with N = N_min = 2^(c_in + c_out) must stay
% below the full codebook 2^(2n).  In log2 and multiplied by 2:
%   max(min(c + 2n+1 - |D_in|, c + 2n+1 - |D_out|), 2(c + 2n+1 - |D_in| - |D_out|)) < 2(2n)
constraint let { var int: c = C_IN + C_OUT } in
  max(min(c + 2*n + 1 - D_IN, c + 2*n + 1 - D_OUT),
      2 * (c + 2*n + 1 - D_IN - D_OUT)) < 4*n;
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

var int: objective =
  if   OBJ_MODE = 0 then K_IN + K_OUT
  elseif OBJ_MODE = 1 then
    ((K_IN + K_OUT) * (4*word*(r_in + r_out) + 1) + C_IN + C_OUT) * (4*n + 1)
    + (4*n - D_IN - D_OUT)
  else C_IN + C_OUT endif;
solve minimize objective;

% Output (adjusted for better readability)
function string: pat(var D: v) = if fix(v) = -1 then "?" else show(fix(v)) endif;

output [ "XU_" ++ show(r) ++ ": \"" ++ join("", [pat(XU[r, i, w]) | i in 0..3, w in 0..word-1]) ++ "\"\n" | r in 0..rounds];
output [ "YU_" ++ show(r) ++ ": \"" ++ join("", [pat(YU[r, i, w]) | i in 0..3, w in 0..word-1]) ++ "\"\n" | r in 0..rounds];
output ["\n"];
output [ "XL_" ++ show(r) ++ ": \"" ++ join("", [pat(XL[r, i, w]) | i in 0..3, w in 0..word-1]) ++ "\"\n" | r in 0..rounds];
output [ "YL_" ++ show(r) ++ ": \"" ++ join("", [pat(YL[r, i, w]) | i in 0..3, w in 0..word-1]) ++ "\"\n" | r in 0..rounds];
output ["\n"];

output ["PL: \"" ++ join("", [pat(PL[i+4*w]) | w in 0..word-1, i in 0..3]) ++ "\"\n"];
output ["PR: \"" ++ join("", [pat(PR[i+4*w]) | w in 0..word-1, i in 0..3]) ++ "\"\n"];
output ["CL: \"" ++ join("", [pat(CL[i+4*w]) | w in 0..word-1, i in 0..3]) ++ "\"\n"];
output ["CR: \"" ++ join("", [pat(CR[i+4*w]) | w in 0..word-1, i in 0..3]) ++ "\"\n"];
output ["\n"];

% Appended rounds, labelled with the round index of the attacked cipher
output ["--- input side (rounds 0.." ++ show(r_in) ++ ") ---\n"];
output [ "dx_" ++ show(r) ++ ": \"" ++ join("", [pat(XL_KR[r, i, w]) | i in 0..3, w in 0..word-1]) ++ "\"  " ++
         "dy_" ++ show(r) ++ ": \"" ++ join("", [pat(YL_KR[r, i, w]) | i in 0..3, w in 0..word-1]) ++ "\"\n" ++
         if r < r_in then
           "c_in_" ++ show(r) ++ ": \"" ++ join("", [show(fix(c_in[r, i, w])) | i in 0..3, w in 0..word-1]) ++ "\"  " ++
           "sk_" ++ show(r) ++ " nibbles: \"" ++ join("", [show(fix(k_in[r, w])) | w in 0..word-1]) ++ "\"\n"
         else "" endif
       | r in 0..r_in];
output ["--- output side (rounds " ++ show(r_in+rounds) ++ ".." ++ show(r_in+rounds+r_out) ++ ") ---\n"];
output [ "dx_" ++ show(r_in+rounds+r) ++ ": \"" ++ join("", [pat(XU_KR[r, i, w]) | i in 0..3, w in 0..word-1]) ++ "\"  " ++
         "dy_" ++ show(r_in+rounds+r) ++ ": \"" ++ join("", [pat(YU_KR[r, i, w]) | i in 0..3, w in 0..word-1]) ++ "\"\n" ++
         if r < r_out then
           "c_out_" ++ show(r_in+rounds+r) ++ ": \"" ++ join("", [show(fix(c_out[r, i, w])) | i in 0..3, w in 0..word-1]) ++ "\"  " ++
           "sk_" ++ show(r_in+rounds+r) ++ " nibbles: \"" ++ join("", [show(fix(k_out[r, w])) | w in 0..word-1]) ++ "\"\n"
         else "" endif
       | r in 0..r_out];

output ["\nContradiction sources: bitwise = " ++
        show(sum(r in 0..rounds-1, i in 0..3, w in 0..word-1)(
          fix(contradict_x[r,i,w]) + fix(contradict_y[r,i,w])
          + fix(contradict_g0[r,i,w]) + fix(contradict_g1[r,i,w]))) ++
        ", joint-SSb = " ++
        show(sum(r in 0..rounds-1, j in 0..word-1)(fix(contradict_ssb[r,j]))) ++ "\n"];

output ["\nR_atk = r_in + r_delta + r_out = " ++ show(r_in) ++ " + " ++ show(rounds) ++ " + " ++ show(r_out) ++
        " = " ++ show(r_in + rounds + r_out) ++ "\n"];
output ["c_in = " ++ show(C_IN) ++ ", c_out = " ++ show(C_OUT) ++ "\n"];
output ["k_in = " ++ show(K_IN) ++ " (" ++
        join(" + ", [show(4*sum(w in 0..word-1)(fix(k_in[r, w]))) ++ "@sk_" ++ show(r) | r in 0..r_in-1]) ++ "), " ++
        "k_out = " ++ show(K_OUT) ++ " (" ++
        join(" + ", [show(4*sum(w in 0..word-1)(fix(k_out[r, w]))) ++ "@sk_" ++ show(r_in+rounds+r) | r in 0..r_out-1]) ++ ")\n"];
output ["|Delta_in| = " ++ show(D_IN) ++ ", |Delta_out| = " ++ show(D_OUT) ++ "\n"];

% Complexity estimate with N = N_min = 2^(c_in + c_out)  (Eq. (1), (2))
%
% With 2^D plaintexts (D >= log2 C_N) one can build S = floor(2^(D - log2 C_N))
% different sets of N_min pairs.  Assuming independence between the sets,
% each set keeps a wrong key with probability p_k ~ 1/2, so
%   T(D) = 2^D + S * (N_min + 2^|k_in u k_out|) * C_E' + 2^|K| * (1/2)^S,
% where C_E' = (r_in + r_out) / R_atk.  S = 1 (D = log2 C_N) is Eq. (2) with
% p_k = 1/2.  T(D) is listed for every integer D from ceil(log2 C_N) to 2n;
% the line marked "<-" is D = data_log2.
function float: T_of(float: lD, float: lS, int: c, int: k, float: ce) =
  pow(2.0, lD) + pow(2.0, lS) * (pow(2.0, int2float(c)) + pow(2.0, int2float(k))) * ce
  + pow(2.0, int2float(key_size) - pow(2.0, lS));

output [
  let {
    int: B   = 2*n;                       % block size
    int: c   = fix(C_IN) + fix(C_OUT);
    int: k   = fix(K_IN) + fix(K_OUT);
    float: lCN = max(min(int2float(c + B + 1 - fix(D_IN)) / 2.0, int2float(c + B + 1 - fix(D_OUT)) / 2.0),
                     int2float(c + B + 1 - fix(D_IN) - fix(D_OUT)));
    float: ce  = int2float(r_in + r_out) / int2float(r_in + rounds + r_out);   % C_E'
    float: lM  = int2float(c) + log2(int2float(B) * 4.0 / 8.0);
    int: D0    = ceil(lCN);
    % S = floor(2^(D - log2 C_N)) (number of C_N sets); lS = log2 S
    array[int] of float: lS = [log2(int2float(floor(pow(2.0, int2float(d) - lCN)))) | d in D0..B];
  } in
  "log2 N_min = " ++ show(c) ++ "\n" ++
  "log2 C_N (data for one set) = " ++ format(0, 2, lCN) ++ "\n" ++
  "log2 T (one set, p_k = 1/2) = " ++ format(0, 2, log2(T_of(lCN, 0.0, c, k, ce))) ++ "\n" ++
  "log2 M (memory, bytes; N_min x 2n x 4 / 8) = " ++ format(0, 2, lM) ++ "\n" ++
  "\nNumber of C_N sets S and time T for 2^D plaintexts (T in R_atk-round encryptions):\n" ++
  "   D   log2 S   log2 T\n" ++
  concat([ format(4, d) ++ format(9, 2, lS[d - D0 + 1]) ++
           format(9, 2, log2(T_of(int2float(d), lS[d - D0 + 1], c, k, ce))) ++
           (if d = DATA then "   <- data_log2" else "" endif) ++ "\n"
         | d in D0..B ]) ++
  (if DATA < D0 then "data_log2 = " ++ show(DATA) ++ " < log2 C_N: not enough data for one set\n" else "" endif)
];

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
