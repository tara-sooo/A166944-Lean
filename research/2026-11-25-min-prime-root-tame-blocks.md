# Gain halos, clean label episodes, and a defect-density theorem for tame high blocks

2026-11-25 JST. Continuation of dc1b7e5e054399a0ad56e11f39e1d0e3c78eaa84 on research/min-prime-root-repeat-energy-2026-11-25. Actual canonical MIN trajectories, not the independent CRT ghost. Elementary paper deductions using prior dense-word deletion and donor-propagation bounds; no Lean compilation, no external novelty claim, twin-prime infinitude OPEN.

## 1. Geometric dilation of any previously bounded event set

Keep the preceding notation: prime roots M in [X,2X), N such roots, B=ceil(sqrt(7X)), l=log log B, original source-specific cutoff K(M), selected p_i, pre-gain g_i, and selected weight V(S)=sum of p_i over source-tagged incidences. Each actual event has gain interval I_i=[g_i,g_i+p_i-1), with disjoint interiors within a source. The previous checkpoint supplies a marked set S (fixed and adaptive caps, actual light-return endpoints, dense union, long spans, finite-depth donor closures) with
    V(S)=O(XN/l^(3/4)).
Do not include the extra relaxed light HORIZON deletion in S, since only its r-cost, not its selected weight, was bounded. The relaxed deletion remains separate as before.

For any real radius R>=1, let A_R(S) be the union, within each ORIGINAL source, of all event intervals fully contained in [g_j-Rp_j,g_j+Rp_j] for some j in S. In particular S is contained in A_R(S). The total gain of the events in one anchor interval is <=2Rp_j by disjointness, hence
    V(A_R(S)) <= 3 R V(S)
because p_i<=1.5(p_i-1). No assumptions on labels or on physical mergers. This is an incidence deletion, not a rerun of the dynamics. It can include events of entirely different prime labels and need not follow a return/donor edge.

Choose two radii
    R_1=max(1,floor(l^(1/8))), R_2=max(R_1,floor(l^(1/4))).
Write A_1,A_2 for the resulting nested halos. Their selected weights are O(XN/l^(5/8)) and O(XN/l^(1/2)), respectively.

## 2. New defect-density result in a comparable high block

Use the earlier short-return parameter K and donor comparability parameter D, both max(2,floor((log l)^(1/4))) for sufficiently large B. They are NOT the source cutoff K(M). Let Q=ceil(B/log B) and z=ceil(sqrt B); eventually Q>=z. Let J_d=floor(l^(1/4)) and K_d=max(2,floor(l^(1/4))) be the existing dense-word parameters in edffc245. A tame high block is a contiguous segment of the actual list of selections p>=Q, with minimum label U, maximum <=D U, and with intervening background gain <=J_d between consecutive listed events (excluding the preceding high jump). It retains all background events in the original interval. Since z>J_d+1 eventually, such a block is also contiguous in the list of p>=z; an intermediate label >=z would alone contribute >J_d.

Put
    m=ceil(2KD)+2, W=2^(2m).
As B grows, m=O(sqrt(log l)), W(D+1)=l^o(1). Thus eventually
    W(D+1)<=K_d,
    R_2 >= R_1[1+4W(D+1)].
All subsequent statements about W-blocks are in that asymptotic range. For a block of exactly W listed events let I be the interval from its first pre-gain to its last post-gain. Including background, |I|<=W(DU+J_d)<=W(D+1)U.

### 2a. Two-radius exclusion

Suppose any LISTED event i of the block is in A_1, with anchor j in S. Since its gain interval of length p_i-1>=U/2 fits in the inner halo, p_j>=U/(4R_1). Every point of I is within |I| of that event's interval. Hence all of I lies inside the outer halo around j, using
    R_1 p_j+|I| <= R_1[1+4W(D+1)] p_j <= R_2 p_j.
Therefore, if the block contains any event outside A_2, EVERY listed event is outside A_1. A very small marked background event is not a valid witness for this argument; the witness must be listed.

### 2b. Finite-alphabet lemma and the required defects

Call a listed event a defect if it is globally first-use of its label or its original immediately preceding same-label pre-gain span S_i satisfies S_i>K p_i. Every distinct label whose first occurrence IN THIS BLOCK is after the initial m positions must have such a defect there. Indeed, its previous occurrence is before the block (or nonexistent). The first m listed jumps already contribute >=m(U-1)>KD U>=K p_i, so that first-in-block occurrence cannot be short. Consequently if e is the number of defects AFTER the initial m listed positions and h is the number of distinct labels, then
    h<=m+e.
This is valid even if the labels were discovered far earlier in the trajectory.

Elementary dense-free lemma: a word with at most h distinct symbols and no nonempty contiguous subword in which every symbol present occurs at least twice has length <=2^h-1. Proof by induction: a nonempty dense-free word itself has some singleton symbol; deleting its one occurrence splits the word into two dense-free words on at most h-1 symbols. Their lengths are each <=2^(h-1)-1. The bound is sharp as a purely combinatorial statement: recursively Z_0=empty and Z_h=Z_(h-1) h Z_(h-1). Any subword containing the new symbol has a singleton, and every other subword is in one copy. These abstract words are NOT asserted realizable MIN transcripts.

If e<=m, then h<=2m, and length W=2^(2m) forces a dense subword. Its first-to-last span is <=|I|<=K_d U<=K_d times its own minimum. Its intervening background gains obey J_d, and its labels >=z. Thus it belongs to the dense class already marked in S by edffc245. In particular some listed event lies in S subset A_1. The two-radius exclusion then places the entire W-block in A_2.

We conclude the following deterministic property:
    Any tame high W-block meeting the outer residual contains MORE than m defects after its first m positions, all outside A_1.
Since global first uses and long-return endpoints are in S, every such defect is actually an intermediate-span return:
    K p_i < S_i <= min(H p_i,F p_i^2),
with H,F as in dc1b7e5. This is an arithmetic-plus-combinatorial obstruction to arbitrarily long locally comparable short-return runs in the residual. It does NOT assert that arbitrary high sequences satisfy the bounded background/comparability hypotheses, or that such a block has a defect outside A_2 rather than A_1.

## 3. A new block ledger for the high residual

Partition each source's high list greedily into consecutive runs: append the next high event if the ratio of maximum to minimum of the run remains <=D and its intervening background gain is <=J_d, otherwise start a new run. Split each run into disjoint complete W-blocks and a final tail of fewer than W listed events. The definition is deterministic; any partition into tame blocks and tails works.

For every complete block with some outer-residual listed event, let D_block be the intermediate defects from section 2 after its first m positions. Then sum of their selected primes >=(m+1)U, while the sum of ALL listed selected primes of the block is <=WD U. Therefore the weight of outer-residual high events of complete blocks is at most
    [WD/(m+1)] sum over these intermediate defects p_i.
The blocks are disjoint, so there is no repeated defect charge. Let I_1 be the selected weight of all intermediate-span high endpoints outside A_1 in the full ensemble, and T_2 the selected weight of outer-residual high events in the run tails. This yields the exact upper bound
    R_high,outer <= V_high,outer <= [WD/(m+1)] I_1 + T_2.
The factor WD/(m+1)=l^o(1). This reduces the complete-block portion of the high linear budget to intermediate-span defects plus the high run-boundary tails. In particular it treats short returns in blocks even when their comparable-donor chains do not reach any old seed within the previous propagation depth.

An alternative sufficient condition to the high energy estimate is
    I_1=o(XN (m+1)/(WD)), T_2=o(XN)
along the same windows as the remaining medium moment. It may be useful for a direct gain-based proof. It is not asserted easier than energy in all regimes. I_1,T_2 count selected weight p, not just r(C); cheap clocks can have large jumps, so no conversion from an r-energy estimate to these weights is made. Small tails, cross-scale changes and large background gaps are not automatically negligible. In particular the bound does not prove the middle-span or tail estimates.

## 4. Exact same-label dilation, independent of gain distance

A second new deletion works even for events far apart in gain. Given any source-tagged set A, let L_t(A) contain every original occurrence of a label within t positions in the same-label occurrence list of some occurrence in A, in either direction. Each anchor p can cover at most 2t+1 occurrences, ALL of weight p, so
    V(L_t(A)) <= (2t+1)V(A).
This uses source tags and original occurrence numbering, not the list remaining after accounting deletion. It is different from the earlier donor-edge closure: no span threshold, comparability or distribution assumption is needed.

Take t=max(1,floor(l^(1/8))) and final marked set S*=L_t(A_2). Then
    V(S*)=O(XN/l^(3/8))=o(XN).
All previous accounting deletions can be kept. For every surviving occurrence p, the preceding t occurrences of p exist and NONE belongs to A_2, because the first use was marked. Any of the next t occurrences that exist are outside A_2 as well. In particular all t preceding return endpoints (and the surviving one) lie outside S and satisfy the previous long-span constraints. This forces long clean same-label episodes, not just a single repeated event. No assertion is made that every intervening donor in a clean episode is unmarked.

More precisely, within each original source and prime, take the maximal consecutive runs of occurrences outside A_2 in its same-label list. A run of length b bounded on both sides by A_2 loses min(b,2t) occurrences; a terminal run with no right marked boundary loses min(b,t). There is no unbounded-left run since the first use is in A_2. Consequently the exact remaining multiplicity after S* is
    sum over internal unmarked runs (b-2t)_+ + (b_terminal-t)_+
(with absent terminal run contributing zero). The previous relaxed-light-horizon deletion can further decrease it. This is an exact episode-tail reformulation of the medium second moment: its terms now involve the squared sums of long clean episode lengths after erosion, instead of all repetitions. It does not bound the tails.

The growing LOW primorial L<=(loglog B)^(1/4) of edffc245 still fits this stronger deletion: extra LOW attachment O(L V(S*))=O(XN/l^(1/8))=o(XN). Prior full relaxed light-horizon deletion is accounted separately. Thus the joint sufficient condition remains
    Z_m=O(N B log^3 B), E_h,late=o(X^2 B)
on the same unbounded dyadic windows, now after S* and previous deletions; or use the alternative high linear ledger from section 3. By the old clock contradiction these imply twin-prime infinitude, but all such asymptotic conditions remain OPEN. The new operations supply unconditional reductions of incidence families only.

## 5. Reproducible tests

Standalone ECMAScript research/min_prime_root_tame_block_audit.mjs, final exact remote readback at c7584e513f88425ed41ce9ca6f581595abf3bd17, blob 67406e5839954b37f069d9b1b03fe04d16fec79f. Run:
    node research/min_prime_root_tame_block_audit.mjs 256 1024 4096 16384 65536 262144
Executed the audit function in the available ECMAScript runtime (not separately launching Node), four modes times six windows, original prime roots and cutoffs. Same previous exact clock/seed checks, 1724 independent literal parity-GCD comparisons per mode at X256/1024. Checks each per-source halo weight and nesting, exact geometric coverage of all events (including background) inside any witnessed block, actual comparable subwindows up to length eight, dense subword via singleton recursion, alphabet bound, label-dilation weights, exact episode-eroded multiplicities, clean prior/future hits for every final residual occurrence, and BigInt energies. The finite wideGate for the FULL asymptotic W-block theorem is false in these sizes; no actual complete W-block exists. The individual geometry and combinatorial statements are independently tested, not an experimental proof of the combined asymptotic theorem. The code avoids materializing hypothetical enormous W blocks unless they fit the actual list. Analytic caps erase all events at tested scales as before, and all analytic depths remain zero.

Independent finite combinatorial oracle: all words over alphabets h=1..3 of lengths 1..2^h, 9872 total (including duplicate words across alphabets), 7296 forced dense instances, singleton recursion checked against independent brute subword enumeration; 29616 exact bounded-index-lag alphabet inequalities. Eight extremal Zimin words (length 1 through 255) have no dense subword as predicted. These are combinatorial tests, not MIN trajectories.

Diagnostics fixed/wide inherit k=1, no adaptive extra, K=6,D=3,H=16,F=4, three earlier A/B rounds, J_d=2,z=7; fixed Q=ceil(B/log B), wide Q=7. Inner radius 1, outer radius 4. Narrow mode uses Q=7, both radii 1, t=2. Fixed and wide large halos often erase all finite high residual, so narrow mode is a nonvacuous test of same-label dilation and remaining clean episodes. All diagnostic parameters are NOT the asymptotic budget choices.

| X | narrow additional halo clock | narrow additional label clock | final surviving incidences | final high clock |
|--:|--:|--:|--:|--:|
|256|310|183|1|0|
|1024|857|276|0|0|
|4096|6380|2576|7|0|
|16384|31555|9239|8|0|
|65536|140977|26347|40|0|
|262144|635708|87574|226|0|

At X262144 N=20390, original events=616116, R=16687054 unchanged. Fixed outer halo adds 176674 incidences, actual clock779374 including high9703. Wide outer halo adds 171468 incidences and clock723960. Narrow halo adds 157738 incidences, then same-label dilation adds 13504 incidences; high clock removals 172076+53125=225201. Narrow high energy after halo 570071, final high energy 0. Remaining 226 incidences are below Q=7 (clock 678; label prior checks452, future41). Wide comparable subwindows at largest X:395878, 107 forced dense, 286 contain a dense subword, 546732 exact witnessed geometry checks; narrow geometry checks484316. The previous seed by itself has selected weight19005176 in wide/narrow, versus 19785710 for the full trajectories, so these finite halos are not evidence for the asymptotic saving. Actual label-dilation residual checks are nonempty in narrow mode.

## 6. Remaining research

The new two-radius theorem rules out a long defect-free comparable high block with bounded intervening background in the residual; the episode dilation forces every surviving medium/high hit to be deep inside a clean label run. Next targets: control the high intermediate defects I_1 and short-run tails T_2 (or the residual high far energy); for medium labels, bound the episode tail moment, potentially via the exact p-deleted shadow and the restriction S_i<=F p_i^2 for all clean returns. No proof of the joint estimates or of the conjecture. No main or other branch changes.
