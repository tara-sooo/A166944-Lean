# Negative MIN: primorial barriers, split cancellation and signed boundary-flux moments

2026-11-27 JST. Continuation of [735c8e6](https://github.com/tara-sooo/A166944-Lean/commit/735c8e6f74e8dcd76022b7e9313068ece74f9bda). The user requests continued research toward unconditional twin infinitude, independent verification and Lean formalization. The age-frontier analysis identified actual low/idle coalescences as the major late entropy cost. Here change the representation to coarse spatial cells: all movement by a prescribed small-prime alphabet is invisible, and splitting entropy is subtracted exactly. Then eliminate time from the coarse calculation via signed total boundary flux. The result is a sufficient asymptotic moment target for an arithmetic object built solely from actual crossings; the needed moment estimate is open.

## 1. Primorial barrier for Negative MIN

Let a be an even center, n the event clock, p an odd prime winner, and the new center a'=a-p+1. The arithmetic eligibility is p|a+1 (even n) or p|a-1 (odd n). Fix q0 a positive multiple of 6, and use cells of width Q=K q0, K positive integer, with boundaries b in a single residue class modulo Q, itself a multiple of q0. If p|q0, no jump with label p crosses a boundary b downward (meaning a' < b <= a). Indeed then j=a-b is even, 0<=j<p-1, and j=+1 or -1 mod p. Neither is possible: j=1 is odd, and j=p-1 is excluded. Landing exactly on b is not crossing. This uses eligibility, not an assumed random distribution of centers. In particular q0 can be 2 times the product of all odd primes <=z, with 3 included. Every label <=z stays in its coarse cell; neither its gain nor its coalescence needs separate entropy charges.

Use actual synchronized windows of 1d0e2c5. Prior to their births place stationary ghost roots at their own initial positions A; on birth they become live without changing position. Ghosts do not participate in the live MIN dynamics or merge permanently before birth. They are only accounting mass, so no creation of mass enters the coarse ledger. At the start of each window every root is at A and a cell holds at most M=Q/6 initial roots. At retirement all are live. For any time the coarse conditional entropy given the cell is N^-1 sum f(m_j), f(m)=m log m and f(0)=0, with the window index included in conditioning for the per-window ledger.

## 2. Exact merge/split cancellation

At a single clock in one window let m_i be cell mass before the step. Aggregate all crossing jumps from cell i to j<i into a positive mass c_ij. Let s_i=m_i-sum_j c_ij be the mass staying in cell i (including intraceil moves and ghosts). Define arriving cross mass b_j=sum_i c_ij. After the clock m'_j=s_j+b_j. Then
    F_j=f(s_j+b_j)-f(s_j)-sum_i f(c_ij),
    S_i=f(m_i)-f(s_i)-sum_j f(c_ij),
    sum_j f(m'_j)-sum_i f(m_i)=sum_j F_j-sum_i S_i.     (1)
F_j,S_i are nonnegative mixing and splitting entropies of the cell-label contingency matrix, not physical coalescence or splitting of actual trajectories. Summing over clocks and windows telescopes. H(A|Y,J) is at most the final coarse conditional entropy, since a cell is a deterministic function of position Y; their difference is at most log(Q/2). The global entropy H(A|Y) differs from H(A|Y,J) by at most log B0=O(1) as before. Thus
    L_end <= log M + O(1) + (sum F - sum S)/N.        (2)
The signed term is necessary: bounding only F charges many harmless movements.

An alternative local representation orders crossing edges by increasing source cell, then increasing destination cell. Lower source cells have already shipped their own outgoing traffic before any arrivals from higher ones. For each edge of mass c, let r be the remaining mass in its source cell after removal and s the current mass in its destination before addition; these are nonnegative and computable in the ordered batch. The potential increment is exactly
    D=Phi(c,s)-Phi(c,r), Phi(c,b)=f(c+b)-f(c)-f(b).
It is nonpositive for s<=r. For s>r, concavity of b->Phi(c,b), its zero value at b=0, and the explicit logarithms give
    0<D<=Phi(c,s-r),
    D<=c log((s+c)/(r+c))+c.
For the first inequality, a concave increasing function vanishing at zero is subadditive. For the second, expand Phi(c,b)=c log((c+b)/c)+b log(1+c/b), the latter term in [0,c]. Summing the ordered increments equals the same net change (1), and their positive parts upper-bound it. In particular only transfers to a cell more crowded than the remaining source are charged. If C=N^-1 sum c and E=N^-1 sum(s-r) over such positive edges, log-sum yields the coarse bound Phi(C,E) on the normalized positive changes. The local sum or signed net is stronger. This is not yet an asymptotic bound.

## 3. Remove time: signed total flux gradient

Now combine ALL windows, using the actual final map Y(A) at each root's own window retirement. The map satisfies Y(A)<=A; no common absolute final clock is needed. For any even boundary b in q0 Z define
    F(b)=# {A: Y(A)<b<=A}.
It equals the sum of masses of completed events crossing b: each root decreases monotonically and crosses a given boundary at most once. In particular F(b) has NO contribution from labels dividing q0. The global flux is a finite-support function on this lattice. For cells [b,b+Q) in any shifted grid, let a_b be the initial mass and m_b the terminal mass. Exact identity:
    d_b=F(b+Q)-F(b),     m_b=a_b+d_b.                 (3)
It follows by subtracting the counts of initial/final roots to the left of each boundary, including roots landing on boundaries. Here a_b<=M and all occupied initial cells except at most two boundary cells have a_b=M. Also sum d_b=0. This representation has no window-index penalty and no clock coding. For an event interval (a',a], its contribution to the flux gradient is c[1_{a'<b+Q<=a}-1_{a'<b<=a}]. It cancels if the same event crosses both boundaries. Over different events of one root, internal transit likewise cancels, leaving only initial/terminal membership. Any estimate treating both boundary terms independently loses this structural cancellation.

## 4. One-sided and signed fractional-moment bounds

For 0<s<=1 use Jensen for the size-biased terminal cell mass distribution:
    L_end <= H(A|cell(Y)) <= (1/s) log(sum_b m_b^(1+s)/N).
(The leftmost inequality is data processing.) Let d_+=max(d,0), E_s^+=sum d_+^(1+s), E_s=sum |d|^(1+s). Minkowski and m<=a+d_+ give the first bound
    L_end <= log M + ((1+s)/s) log(1+(E_s^+/(N M^s))^(1/(1+s))).   (4)
There is a sharper signed bound using the contiguous initial lattice. For a,m>=0 and d=m-a,
    m^(1+s) <= a^(1+s)+(1+s)a^s d+|d|^(1+s).
This follows by integrating the derivative and |x^s-y^s|<=|x-y|^s for x,y>=0. Also
    sum a^(1+s)<=N M^s,
    sum a^s d = -sum (M^s-a^s)d <=2 M^(1+s).
The latter uses sum d=0, full initial cells give zero, cells with a=0 have d>=0, and each of the at most two partially occupied initial cells contributes at most M^(1+s) since d>=-a. Hence
    L_end <= log M + (1/s)log(1+E_s/(N M^s)+2(1+s)M/N).   (5)
Since d_-<=a<=M and sum d_-<=N, E_s<=E_s^++N M^s. Thus a one-sided version is
    L_end <= log M + (1/s)log(2+E_s^+/(N M^s)+2(1+s)M/N). (6)
For s=1 the Taylor step is exact and the boundary loss can be improved, but the displayed bound suffices. All these inequalities use global endpoint masses, not actual physical collision counts.

Allow K=Q/q0 shifts, each in q0 Z modulo Q. Their cell boundary sets partition q0 Z, so the average E_s^+ is exactly
    (1/K) sum_{b in q0 Z} [F(b+Q)-F(b)]_+^(1+s).         (7)
Similarly for E_s. There exists a shift attaining no more than its respective average. Because L_end is independent of shift, any such upper bound is valid. No statistical independence or random uniformity of the actual root ensemble assumed. For s=1 the full signed lattice energy is exactly 2(sum F(b)^2-sum F(b)F(b+Q)), which emphasizes the need to bound a difference of correlated fluxes rather than their individual large masses.

Define R-dependent q0|Q, Q divisible by 6, M=Q/6 and
    U_s = (1/(K N M^s)) sum_{b in q0 Z} [F(b+Q)-F(b)]_+^(1+s).
Then (6),(7) and the outgoing-label penalty Q_R (notation from 5e932c4; distinct from cell width Q) give a new sufficient condition
    liminf [log M + (1/s)log(2+U_s+2(1+s)M/N)+Q_R]/loglog R <3.  (8)
For example if Q=(log R)^(a+o(1)) and U_s <= (log R)^(b s+o(1)) with a,b>=0, then L_end <=(a+b+o(1))loglog R. If a+b<=2, the existing positive terminal-minus-small-repeat occupation margin suffices. With a+b<2, a weaker occupation estimate would suffice. It is enough to prove (8) on unbounded slabs. Primorial q0 of polylogarithmic magnitude excludes the small-prime alphabet from the flux. No such U_s asymptotic bound is proved here.

One can split F into label bands F_I, with each a sum of actual mass-weighted crossing intervals. For fixed shift, ||(Delta_Q F)_+||_(1+s) <= sum_I ||(Delta_Q F_I)_+||_(1+s), since positive part is subadditive. This is a sufficient route if individual high bands can be bounded, but it discards cancellations between bands and can be weaker than estimating their signed correlations. No assumption of decorrelation is warranted. Next mathematical target: actual pair correlation of opposite boundary crossings (or a signed first/last-crossing estimate) for growing q0 and polylog Q. Seek a transfer from small-prime deletion and first-use/repeat bounds to this *mass-weighted* signed flux, rather than total crossing counts. Compare s near zero against s=1 if rare crowded cells dominate. Neither moment bound nor time-occupation bound is established asymptotically.

## 5. Finite verification and exact remote sources

Both standalone scripts were executed as ECMAScript functions before commit and after fetching their committed content, over R=12000,48000,192000,480000,1000000,2000000. They use the same actual prime-factor clock as previous audits. No Node process, independent proof reviewer or Lean kernel was used.

A. [Primorial flux audit 4f137dd](https://github.com/tara-sooo/A166944-Lean/blob/4f137ddd43be42a1dafea4a6cb3e374ee1c7fc5a/research/min_local_negative_primorial_flux_audit.mjs), blob 835d1bdac50d5a2183951d49c6d6600ef2864738.
    roots                         622004
    occupied-component jumps      2110844
    ordered cell transfer edges   2060917
    small-label barrier checks    4657295
    counted structural checks     3745082
Reproduce: node research/min_local_negative_primorial_flux_audit.mjs
At R=2000000 (within-window fine entropy 3.57735857):
    Q      initial   mixing     splitting   net        final
    6      0         4.002418   .425060     3.577359   3.577359
    30     1.602387  4.748307   2.753238    1.995070   3.597457
    210    3.502963  3.654689   3.326035    .328654    3.831617
    2310   5.375608  1.028675   1.398795   -.370120    5.005488
These demonstrate cancellation; increasing Q also increases the initial budget and need not improve the sufficient bound. In particular Q=2310 has negative net increase but a larger final upper bound.

B. [Boundary moments audit ce2cb47](https://github.com/tara-sooo/A166944-Lean/blob/ce2cb4762fb023f7ef61d4b9e8d2cbed9884f6d7/research/min_local_negative_boundary_flux_moments_audit.mjs), blob 763ffa892127278d7582ff3d919779312996b59c.
    roots                         622004
    occupied-component jumps      2110844
    barrier checks                3376184
    actual crossing intervals     2049729
    counted structural checks     5368356
Reproduce: node research/min_local_negative_boundary_flux_moments_audit.mjs
Independent accumulation of event interval flux and terminal prefix mass identity, multiple shifts and widths, exact cell mass identities, ordinary and sharper signed/positive moment inequalities for s=1 and 1/2. All assertions passed. At R=2000000 (global fine entropy 3.98901644):
    q0=Q   E_1/(NM)   E_1^+/(NM)  coarse entropy  actual Renyi2  bound (5)
    6      82.733045  81.775060   3.989038        4.427626       4.427634
    30     16.136569  15.308788   4.021857        4.450613       4.450656
    210    2.087521   1.646588    4.362780        4.682509       4.682853
For q0=210,Q=2310, shift selected by positive second moment: normalized signed energy .092972, coarse entropy 6.000830, bound (5) 6.046362. Coarser cells reduce normalized energy but increase baseline; no finite trend proves (8). These are global quantities, not the within-window ledger in A. For the finite controls the quadratic signed bound was stronger than the fractional Taylor bound; this is not an asymptotic comparison.

No unconditional proof, no independent mathematical certification, no Lean formalization. Main and sibling branches unchanged. The prior age-frontier route remains available; this new representation removes all local low-prime entropy and gives a signed flux-gradient target, but the required arithmetic correlation estimate is a major unresolved step.