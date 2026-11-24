# Small physical terminal classes: first height passage and phase-averaged signed LOW drift

2026-11-24 JST. Continues 38905a4006db146848580722ad7a2a742c8edeae on the SAME research/min-cycle-forest-2026-11-24 branch. Paper deductions from MIN clocks, the physical forest, the per-prime sieve and LOW barrier, plus exact finite diagnostics. No Lean compilation. Full stopping deficit and twin-prime conjecture remain open.

## 1. Small terminal physical classes bound every earlier physical incidence

Keep canonical MIN, original odd M in [X,2X), N=X/2, B=ceil(sqrt(7X)), individual cutoffs, Y=c log log B for a sufficiently small fixed c>0, L=2 product_(3<=p<Y prime)p<=log^(1/4) B, barrier-cell admission threshold T=ceil(X/log^2 Y), and full inverse projected cap ceil(B^2/p) at p>=Y. Thus R_pre=O(X^2/log^2 Y). Use the actual cell-stop crossing classes (q,A,u) from the preceding note, where A is pre-horizon and u is the crossing event clock. These are terminal physical classes, with attained entry horizon A+q-1. Choose a>=1; let E be all noninitial cell-stop tags whose terminal physical crossing class has mass <=a. No condition on the gateway label is needed here.

Retain only these tags and their actual executed paths to cell entry, with no change to original stops/cutoffs. Every actual physical event (p,C,n) on these paths carries <=a of these tags. Indeed two retained tags reaching this same event acquire the same physical post-state, and the deterministic suffix, including the original accounting stops, is common whenever both remain in the process. Original individual cutoffs can truncate a suffix but cannot redirect it; since both retained tags reach an accounting stop, neither naturally terminates first. Thus all such tags have the same terminal crossing class. If one enters a stopped cell on this event, so do all. This reasoning uses actual clocks, not projected-key equality. It applies at all labels, including p<Y. The bound holds for the retained subpopulation even if the original projected mass is far larger than a.

Let H>6 and truncate these paths again at the FIRST attained height h=2t-C>=H if it occurs before or at cell entry. Write Z(H) for the number of retained tags hitting H; we can use just their truncated prefixes in upper bounds. At all included post-states h<=H+4B, since the prior height is <H and one event wait is <=2r(C)<=2B. Assume H>=BL and H>=10B for the phase-counting results below (H=X/log^4 Y in the preceding residual easily satisfies these for large B). At a fixed high projected key (p,C), possible event times are in one residue class modulo 2p, hence post-heights in a progression of step 4p. There are O(H/p) actual possible clock classes in the truncated paths. Total retained incidence at this key is therefore O(a H/p), independently of the original inverse cap. This is the essential improvement: the physical mass bound and the first-passage height bound work together.

## 2. Unconditional signed height decomposition

For each event define
    delta h = 2(n-t)-(p-1).
A positive increment is at most 4r(C); no assumption that height is monotone. At high p>=Y let P_hi(i) be the sum of positive increments along tag i's truncated prefix. With the prior per-prime eligible-horizon sieve S_p^cost=O(X/log^2 p) (uniform in p) and the incidence bound above,
    sum_i P_hi(i)
       <= O(a H X sum_(p>=Y prime) 1/(p log^2 p))
        = O(a H X/log^2 Y).
Thus if a=o(log^2 Y), for every fixed eta>0 only o(X) of the first-passage tags have P_hi(i)>=eta H. This is an all-depth SOURCE bound, not a count of event types. In particular no substantial first-passage population of small terminal physical classes can acquire most of H from positive increments at high labels.

For a maximal consecutive LOW block on the truncated prefix, define its peak signed increment as the maximum of 0 and the cumulative delta h at its successive events, measured relative to the height at the block's start. This includes the last partial block if first passage occurs inside it. Its true net increment is at most its peak. A LOW block of gain <L and elapsed <3 gain has peak <=5L (apply the barrier also to every prefix). Denote the sums of these peak increments by P_init(i) for the initial block, P_big(i) for blocks following an executed high q>=Z0, and P_mid(i) for blocks following Y<=q<Z0. Empty blocks have zero. Exact height telescoping and h_initial=6 imply
    H-6 <= P_hi(i)+P_init(i)+P_big(i)+P_mid(i)
for every first-passage tag. The negative high increments and negative parts of low net changes are not counted as positive credit; the inequality is an upper envelope for actual signed gain.

The initial-block total is <=5LN=o(XH). The number of high incidences at labels q>=Z0 is
    O(a H X sum_(q>=Z0 prime) 1/q^2)
      = O(a H X/(Z0 log Z0)),
since for fixed q the number of eligible horizons is O(X/q), and the number of clock classes is O(H/q). Each high incidence is followed by at most one low block. Consequently
    sum_i P_big(i) = O(a H X L/(Z0 log Z0)).
Take a=ceil(log^(1/4) Y) and Z0=ceil(L^2+Y^2), which is <=O(log^(1/2) B) for sufficiently large B with the chosen Y (in particular Z0<B). Both high-positive and big-followup terms are o(XH); L/H tends to zero. By Markov's inequality, except for o(X) tags, any first passage to H among E must have
    P_mid(i) >= H/2.
Since each block supplies at most 5L, such a tag has at least H/(10L) low blocks with positive peak following high labels in [Y,Z0). These are distinct actual preceding high events on the trajectory. No restriction on the final gateway prime is used, and the result holds uniformly for H>=max(BL,10B). For H=X/log^4 Y this is a new necessary condition on the high-height small-class residual from the preceding note. It isolates the origin of that height accumulation to repeated low blocks after relatively small high primes. It does not show those repetitions are rare. The earlier R_pre bound is not enough to establish that.

## 3. Replace maximum clock phase by an average, for this small-class population only

Define a periodic ghost on even horizons and integer clock phase t modulo L: choose the earliest next clock among eligible low primes p<Y, ties by smaller p, until no low prime eligible. As before any consecutive actual LOW segment is a prefix of this ghost (the full process may instead select a high prime or terminate sooner). The ghost ends within its LOW barrier. Define D_Y(C,t) as its maximum nonnegative signed height increment over prefixes, including the empty prefix. It depends only on C mod L and t mod L. At an eligible low event with next wait w and selected p its recursion is exactly
    D_Y(C,t)=max(0, 2w-(p-1)+D_Y(C+p-1,t+w)).
The terminal value is zero. Compute backwards on even C in [0,L], with time modulo L; the choice of clock uses the original side-dependent period 2p. The state need not be a reachable canonical state, since this envelope covers all phases. The signed increment is measured relative to the starting height, so translating C or t by L changes no future increments. Let
    A_+(Y) = (2/L^2) sum_(even C mod L, t mod L) D_Y(C,t).
It is an average of the MAXIMUM SIGNED PREFIX gain, not average final net drift, nor maximum over t at each C, nor mean of actual source trajectories. Clearly 0<=D_Y<=5L. The finite test also checks D_Y<=4 times the corresponding complete ghost r-cost.

In the earlier note's full inverse cap argument for ALL tags, averaging over t was not legitimate: a projected key may concentrate all its mass at one clock. For the first-passage prefixes of E, the physical bound <=a permits an entirely different argument: enumerate the clock phases, upper-bounding each physical incidence by a, without assuming any actual equidistribution.

Fix a high label q>=Y and a pre-horizon divisibility side. Post-horizon C lies in an even progression with step 2q, since q divides C or C+2. Its window length is O(X). For any fixed even residue C0 mod L, that progression contains O(1+X/(q L)) candidate C, because gcd(q,L)=1. Since L<=log^(1/4) B and q<=B, this is O(X/(q L)) uniformly. At such a projected key the actual possible post-event time n lies in one residue class mod 2q, in a height window 0<=2n-C<=H+4B of length O(H). For any fixed clock phase t0 mod L of the correct parity, CRT (gcd(2q,L)=2) gives O(1+H/(q L)) candidate n, which is O(H/(q L)) under H>=BL and H>=10B. Wrong parity has no candidates. Each candidate physical incidence contributes at most a tags, and its following LOW peak is <=D_Y(C0,t0). Including both sides, and if desired overcounting both parities, total possible LOW peak after this q is
    O(a X H/(q^2 L^2) sum_(C0 even,t0 mod L) D_Y(C0,t0))
     = O(a X H A_+(Y)/q^2).
No probability assumption: this is a deterministic count over a full residue rectangle, with the actual tags bounded above by its per-state capacity. In particular using a phase mean in this argument does not assert that real clocks are uniform. Each event has at most one following LOW block. Summing over q>=Y and adding the initial block gives
    sum_i (P_init+P_big+P_mid)(i)
       <= O(X L + a X H A_+(Y)/(Y log Y)).
Together with section2,
    Z(H) <= O(X L/H
                 + a X [1/log^2 Y + A_+(Y)/(Y log Y)]).
This is an unconditional inequality for all the stated parameters, but it gives a vanishing relative bound only with an additional estimate on the ghost mean. It differs from the previous conditional A(Y) criterion, which had no small-class restriction but required the maximum over clock phases and aimed to abolish cell stops. The new criterion concerns first passage in small terminal classes, uses signed prefix drift rather than r-cost, and takes an actual average over all possible clock phases.

## 4. Consequence of the signed ghost criterion (conditional)

Suppose along some diverging sequence Y the quantity A_+(Y)/(Y log Y) tends to zero. Then let Y(B) grow sufficiently slowly on that sequence to satisfy Y<=c log log B, and choose integer a tending to infinity sufficiently slowly with a<=ceil(log^(1/4) Y) and a A_+(Y)/(Y log Y)=o(1). Choose D=floor(sqrt(a)), with D tending to infinity. Take H0=X/log^4 Y. The new bound gives Z(H0)=o(X). The preceding landing-divisor deletion applies to this slowly growing Y as well: Q=ceil(L log B) gives S_c(q>=Q)=O(X log^2 Y/log Q)=o(X). The small-class low-height count in that note used log log Q=O(log Y), which need NOT hold for arbitrarily slowly growing Y. In this conditional corollary it can instead be bypassed by counting all small classes at cell stops with height <=H0 using the exact landing-horizon divisor bound, OR more simply by choosing a different H0. Use the following latter choice to avoid that issue:
    W=1+log log(3B), H0=X/(log^4 Y * W).
Then H0>=max(BL,10B) eventually, and the elementary harmonic bound gives
    small-class, q<Q, height<=H0 mass
       <= O(a log^2 Y [Q+H0 W])=o(X).
Here Q is polylog B; this proof is valid for arbitrarily slowly growing Y. The first-passage inequality still gives Z(H0)=o(X). Thus ALL small physical classes at cell stops together have o(X) mass, under the ghost condition. Root injections at cell stops are o(X) since L=o(T). The remaining cell-stop physical classes have size >a; their terminal variance at scale D is >=S_c/2-o(X). The prime-stop capped-clock moment gives terminal within-clock variance >=S_p/2-o(X), since D=o(log^2 Y). Restrict the physical forest to these tags. The harmonic near deletion at d=floor(D/log^(1/2+epsilon)(2D)) yields the conditional necessary inequality on no-twin windows
    2 P_phys,far >= N-o(X).
Thus the ghost condition would eliminate the high-height small-class cell residual entirely, but not the independent physical far-coalescence problem. Neither the condition on A_+ nor the far-merge deficit is proved here.

## 5. Finite diagnostics

Saved research/min_small_class_height_passage_audit.mjs and research/min_small_class_height_passage_results.json with exact remote readback at 6536a950dbf66388023248edf5bf69c43de0bded. Executed X=256,1024,4096,16384,65536,262144; original diagnostic barrier-cell caps Y=11,13, A=max(2,floor(B/4))*B and T=max(floor(L/4)+1,ceil(X/256)), full inverse comparison and combined rule. For noninitial cell-stop tags with actual terminal clock-class mass <=8, replay unchanged paths to their actual attained endpoint, or first attained height H for H in {32,128,max(32,floor(B/4)),max(32,B)}. Verify exact signed height update and identity h=6+sum positive high+sum negative high+sum low net, overshoot bound, decomposition of low peak by preceding high label, and per-physical-high-state incidence <=8 among all such first-passage tags. Check all prior barrier/cell/prime conservation and moment assertions. The finite large-cut diagnostic is max(Y,ceil(sqrt B)), not asymptotic Z0; the tested H do not satisfy H>=BL, so these are algebraic checks, NOT tests of the asymptotic deletion theorem.

At X262144,Y13, SCell16921, 8258 crossing tags, 300 in small classes <=8. At H=B1355, 55 of those 300 attain H before or at cell entry, although only 51 have entry height >B in the earlier diagnostic. The total positive high drift of these 55 truncated paths is 105532, signed negative high drift -2954, net LOW drift 3372, giving exact aggregate net gain 105950. Total LOW peak 3428 (initial248, after q>=37 1328, after q<37 1852). All 55 have high positive drift >=(H-6)/2 and none have LOW peak >=(H-6)/2. These finite values are not evidence for the opposite asymptotic first-passage class: a=8,Y13,H=B do not satisfy the asymptotic separations. The maximum retained physical high-state incidence is8; 94 distinct such states occur in the first-passage prefixes. At Y11 no cell stop in this window.

Exact backward integer DP also computes signed-prefix envelope D_Y at every even residue and every clock phase for Y=5,7,11,13:
    Y   A_+(Y)    A_+/(Y log Y)   mean over C of max over t D_Y
    5   3.333333   0.414223       6.666667
    7   7.724444   0.567083      14.800000
    11 13.276825   0.503351      29.142857
    13 17.987521   0.539447      46.129870
At Y13 the all-phase complete ghost cost mean is 14.770232; it is a different quantity. Maximum signed prefix drift is192, even-phase mean17.923279 and odd-phase mean18.051764. Values are exact finite sums with rounded display ratios. The four tested ratios do not establish a decay toward zero. No larger phase rectangle was computed in this audit. The previous permissive-cost envelope's increase likewise cannot disprove the new signed-phase criterion.

## 6. Next task

The first-passage bound removes the contribution of high positive increments and LOW blocks following sufficiently large labels, for the retained small terminal classes. The remaining near-X height accumulation must be generated by LOW blocks after polylog-size high events, unless the signed phase-average criterion can remove it altogether. A next analytic task is to estimate D_Y on the actual complete residue rectangle, perhaps using signed increments over consecutive LOW portions rather than summing positive per-event bounds. The result here establishes the legitimacy of averaging phases for small physical classes, not the required smallness of the mean. No full deficit, no twin-prime proof, no new branch, no main edit, no Lean compilation.
