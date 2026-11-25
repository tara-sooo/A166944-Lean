# Wait-jump births: exact prior RESET, short-age two-label support, and long-age roughness

2026-11-26 JST. Continues [56e329bc7ccc](https://github.com/tara-sooo/A166944-Lean/blob/56e329bc7ccc9da30d26e8e6981e07fdfb6589ec/research/2026-11-26-min-unified-birth-pair-lifetime-support.md) and [590c13723c1a](https://github.com/tara-sooo/A166944-Lean/blob/590c13723c1ad5ff49553e06ad6f64d22f74921c/research/2026-11-26-min-unified-compatible-birth-transport.md). Independent heads verified unchanged at preflight: prime-root 1a4005f2f336ede61cca1a9656c158a559338b72; stable-heavy e1ad9e2b434c652699e1bc9a0797887631e0ea6d. New: exact prior even RESET at every RESET wait-jump birth, actual two-label keys even when only one branch jumps at the meeting tick, distinct-label short-age support and long-age rough support, exact charge refinement and new thin payments on the formerly dominant wait-jump sector. No final upper contraction, twin-prime proof or Lean compilation.

## 1. Frozen ensemble and charge

Retain X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, original prime roots M in [X,2X), C0=2M-2, completed gain-stopped MIN paths, actual event gain g=p-1 and wait w<=2r<=3g. Original true deficit d=2t-C in [0,6+5H]. Under finitely many twins eventually all tags reach T and W_all>=N(T-6)/2. Same original masks, grids P_j, average denominator m, P_max<=B^.25, c_a=3(1+2/u^.25), rank parameter tau>=1/log ell ->0, and physical source slot lower bound b_min=B^(1-o(1)) from 590c137. No recomputation of trajectories, counts, word classes or source pairs.

Start with the exact residual birth-pair measure B_pair,rem of 56e329b AFTER its old projected-destination and true-birth-pair thin payments. Preserve the exact frozen charges and every old source mask. Only reindex surviving ordered pair-incidences having one incoming jump and one incoming wait at their true first meeting U=(t,J). Keep other types and forward defect residual unchanged. At an original source crossing the resampled compatible clock gave per-pair per-atom charge <=c_a P/b, where b>=b_min is the full original source physical slot. Both source orientations are counted as before. There is no additional resampling.

## 2. Record the waiting member's actual previous arrival

The waiting member at U came from (t-1,J), and its actual completed event at horizon J begins at its recorded arrival time t0<t and ends at v>t. The latter exists because both original members continue through the common source departure. Set h=t-t0, s=t mod 2, s0=t0 mod 2. In particular
    1<=h<w=v-t0<=2r(J)<=2B.                         (1)
Here r(J) is the least eligible odd prime factor of J-1 or J+1 (at most B); it is not r(J-p+1) of the incoming jump. If this arrival at J was the member's root, record q=0; otherwise let q be its immediately preceding actual selected jump label, whose poststate is (t0,J). There can be different q,t0 for different members of the full waiting branch. Record actual original pair's q,t0, not a representative of all waiting tags.

For the incoming jump p at U and any preceding jump q on the waiting side, exact exit congruences give
    p|(J+2s), p|(t-2s), q|(J+2s0), q|(t0-2s0).
Together with parity these determine t mod 2p and t0 mod 2q. Define k=(2t-J-6s)/2, k0=(2t0-J-6s0)/2. With q>0, k,k0 are nonnegative integers and p|k, q|k0. Moreover
    k-k0=h-3(s-s0).
If q=p, then the two J congruences force s=s0 (p odd), and h is a positive multiple of 2p. Thus h<=R implies p<=R/2 in the equal-label case. Distinct p,q need not be close in size. No assertion that both labels divide the same birth deficit unless their arrival times coincide.

For q=0, J=2M-2, t0=M+2 and M prime >B. If t were odd, the incoming jump would have p|J+2=2M, impossible. Therefore t is even, p|M-1, and p|(h+3) by p|t. In particular p<=R+3 for short root waiting age h<=R. This is not the original root-injection-at-U type, in which h=0; that old type remains separate.

## 3. RESET wait-jump birth is exactly a three-tick bridge

If k=0 (incoming jump RESET), then 2t-J=6s. The waiting member's nonnegative deficit at arrival is 2t0-J=6s-2h. If s=0 then h>0 is impossible. Thus s=1 and h<=3. The earlier arrival deficit is one of 4,2,0. A root arrival has deficit 6, impossible. An earlier completed jump has postdeficit 6s0+2q k0' with k0'>=0 integer and odd prime q>=3. Of 4,2,0 only 0 is possible. Hence necessarily
    h=3, s0=0, t0=J/2, 2t0-J=0, q>0,
    q|J, p|J+2, p!=q.                                (2)
Conversely these are necessary arithmetic conditions, NOT a sufficient condition for an actual MIN birth: both incoming jumps and the intervening waits must actually occur. In particular J=0 mod4. This identifies a true earlier even RESET and a later odd RESET, with exactly three elapsed ticks. It includes any different q among actual waiting members at that earlier reset. There is no root-start waiting member in this sector.

Refine an old wait-jump birth key (U,p,wait) by q and t0. For RESET births, t0 is forced, so the refined key is just (J,p,q) with parity and t determined. For fixed distinct p,q the CRT support count is O(X/(pq)), since J in an interval of length O(X), J=0 mod q, J=-2 mod p, and pq<=B²=O(X). This is the same support size as a true double-jump RESET, although the two jumps occur three ticks apart and only one enters U. It was absent from the old single incoming label bound. We do not assume the refined key is a new independent birth or add a second copy of its charge.

## 4. Short-age and long-age non-RESET sectors

Choose R=floor(u^.5), Q=B/u (asymptotic parameters). In non-RESET births k>0 separate by h<=R versus h>R. For short age and q>0, q!=p, use refined key (J,t,p,q,h); t0=t-h. At fixed h and the parity choices s,s0 forced consistently by h, spatial CRT yields O(X/(pq)) J. For fixed J, t mod 2p and t-h mod 2q determine at most one residue mod 2pq, while t lies in an interval of length O(H) at fixed J from the deficit slab. Thus at most O(1+H/(pq)) times per J. Summing h<=R gives
    S_short(p,q) << X R/(pq) * (1+H/(pq)).             (3)
No use of H/(pq) alone when pq>H. This is an ordered label support (p is incoming, q earlier), so the constant includes both orders when needed. It is not a prime-pair difference estimate. For equal q=p and h<=R, keep the original unrefined support and cutoff (p<=R/2 is an additional restriction); aggregate by old birth key for this sector. For short root waiting (q=0) p<=R+3 and p|M-1, h=-3 mod p; the root prime M determines J. Uniform upper bound for primes in this progression is O(X/(p u)), by the elementary one-form upper sieve with modulus p<=R+3 (exclude p from sieving; interval length X/p and log(X/p)~u). For each M there are O(R/p+1)=O(R/p) possible h since p<=R+3, so support O(XR/(p²u)). Each such refined waiting root subset consists of only one original tag, even when another earlier jump joined that root state at its origin.

For long age h>R use (1): r(J)>R/2. Aggregate all long-age contributions by the OLD birth key (U,p,wait), without multiplying by the number of prior arrivals. The full J support for fixed p,s now has
    #J << X/(p log²(2+R)).                              (4)
Proof: write J=p a-2s. The two forms p a-2s-1 and p a-2s+1 have distinct roots at every odd prime l !=p. Both avoid odd primes up to z=floor((R/3)^(1/40)) by r(J)>R/2; exclude p (and 2). Use the same dimension-two upper Selberg sieve with squarefree cutoff z and O(z^8) remainder as prior local support estimates. Parameter interval length O(X/p), >=order B for p<=B, log z comparable log R, remainder R^.2 negligible. Removing the one possible prime p from the sieve changes constants by a uniformly bounded factor (at odd primes local avoidance factor >=1/3). Unlike the old r(C) bound, the two forms here are at the shared J, where the waiting member is located. The positive k for the incoming jump has O(H/p) choices; hence long nonreset old key support
    S_long(p) << X H/(p² log²(2+R)).                   (5)
The RESET sector never has long age once R>3.

## 5. Refined lifetime bounds and explicit new thin payments

For any refined key let A be the full original incoming jump tag set at U, and A' the subset of the full waiting branch with that actual recorded arrival t0 and label q (q=0 for a root). Both sets are fixed independently of the later source. All contributing pair tags belong to these sets; they follow the same physical suffix from U. Apply the proof of section 2 of 56e329b to these subsets: with b_1=|A|, b_2=|A'| and L_i(x)=# roots in that set with C0+H>x, the exact refined charge is bounded by
    2 c_a [integral_J^(J+H) F(L_1(x),L_2(x)) dx + P_max F(b_1,b_2)],
    F(x,y)=xy/max(b_min,x+y).
In particular <=2 c_a(H+P_max)F(b_1,b_2). For the long and equal-label aggregated sectors one can use the old full branch upper bound, or the subset of waiting tags satisfying the chosen age/label predicate. No independence between refined keys. Reindexing is exact: the sum of refined and aggregated sector charges equals the original wait-jump residual, with no change in the other birth charges.

Let nu count high labels >=Q among p,q in the following two-label cuts; nu=0,1,2. Pay the exact charge of each key if it is <= its cutoff:
    RESET refined:         H u^nu/(u ell³).
    Nonreset short distinct: [H pq/(H+pq)] u^nu/(u ell³ R).
    Nonreset short root:    H p/(R ell²).
    Nonreset long aggregate: p log²(2+R)/(u ell²), multiplied by u if p>=Q.
Keep the old equal-label short and other type masks, which have already been applied. The nonreset short distinct scale H pq/(H+pq) is comparable to min(H,pq). Multiplying by (3) cancels 1+H/(pq) and R exactly, giving O(XH u^nu/(u ell³ pq)) per p,q. The RESET product-support gives the same bound. Sum over ordered prime labels using sum_{p<=B}1/p=O(ell) and sum_{Q<=p<=B}1/p=O(ell/u); the u^nu is canceled in each sector. Each total O(NT/ell). The short root cutoff times its support gives O(XH/(u ell² p)), again O(NT/ell) after summing. The long cutoff times (5) gives O(XH/(u ell² p)) and the high gain cancels by the same reciprocal bound. All new masks together cost O(NT/ell)=o(NT).

For long age log R~ell, the new absolute cutoff increases by order ell² versus the old nonreset wait-jump cutoff in each high/ordinary p band. This applies to the aggregated long piece even if the total old birth charge exceeds its old cutoff. For RESET, the refined cutoff with both labels high is H u/ell³, versus old sole-high H/ell². Thus all such refined high-high keys with min(b_1,b_2)<=u/(32 ell³) are payable, by the harmonic envelope and 2c_a(H+P_max)<=24H eventually. The threshold constrains the actual prior-arrival subset, not the entire waiting branch; a huge full waiting branch can be divided among several small arrival subsets. The earlier q is not the selected departure ending the wait. For short distinct, comparing with the old nonreset single-label cutoff p u^[p>=Q]/(u ell²) gives a gain factor
    [H q/(H+pq)] u^[q>=Q]/(R ell).
This need not exceed one for small q. The old payment is kept first so there is no loss in the sufficient objective. In the short distinct high-high sector with pq>=H, the cutoff is >= H u/(2 R ell³); the harmonic bound pays every key with min(b_1,b_2)<=u/(64 R ell³), a growing threshold for R=u^.5. These are sufficient all-mass deletions, not necessary estimates of actual charge. In all sectors one may use the lifetime envelope as a sufficient check against the respective cutoff. No assertion that the full harmonic envelope summed over all keys is small.

## 6. Resulting sufficient condition

Let B_wait,rem be the new remaining birth-pair charge, including all other birth types unchanged. Exact reindex and additional payment imply B_wait,rem<=B_pair,rem and B_pair,rem-B_wait,rem=O(NT/ell). Under finitely many twins the previous route yields
    NT/2-o(NT) <= B_wait,rem+(3+o(1)) D_all,rem.
Consequently
    liminf_(dyadic X) [B_wait,rem+3D_all,rem]/(NT)<1/2
is sufficient, implied by 56e329b's condition. This is a new structural reduction, not an improved constant-margin threshold (the additional payment is little-o). The large-charge long waits, short equal-label, short root and heavy two-label sectors remain, as do other birth types and forward defect charges. Neither final upper estimate has been established. Main and both independent source branches unchanged. No Lean verification.

## 7. Finite audit

[Standalone source](https://github.com/tara-sooo/A166944-Lean/blob/355b39dae8d86637a7ede0979fa183ae457ed12f/research/min_unified_wait_birth_refinement_audit.mjs), exact committed remote readback verified at 355b39dae8d86637a7ede0979fa183ae457ed12f. Seven runs passed in available ECMAScript runtime, four normal and three focus. Reproduce: node research/min_unified_wait_birth_refinement_audit.mjs 1024 4096 16384 65536. Derived from 54a3231. Same finite trajectories, source room, cell, first-meeting and resampling settings as that audit. Finite age threshold R=8, not asymptotic sqrt(u). For each ordered routed wait-jump pair records actual prior arrival and preceding jump label of waiting member, checks age<event wait<=2r, previous jump congruences, same-label period, root-origin congruence, exact RESET three-tick even-arrival condition. Independently reconstructs full refined incoming root sets and verifies discrete lifetime upper bound and exact parent/global charge conservation (up to floating point tolerance). For numerical diagnostics it refines long and equal-label groups too, then reports their summed sector charges; the analytic thin caps use aggregated long/equal keys, NOT the count of the finite refined keys. Does not implement analytic sieve census/cutoffs, earlier cumulative masks or Lean proof. Finite old projected payment is illustrative, not used as an asymptotic inference.

| X/mode | distinct refined keys | ordered age checks | RESET checks | refined envelope checks |
|---:|---:|---:|---:|---:|
|1024|42|994|114|84|
|4096|177|14976|1384|436|
|16384|800|136588|17772|1958|
|65536|3229|852296|102412|7828|
|4096 focus|110|940|76|196|
|16384 focus|631|10970|1591|1233|
|65536 focus|2715|94532|13768|6063|

Largest ordinary: 5709 roots, 140255 completed events, no diagnostic T reaches; 36614 root-arrival checks, 27438 short same-label incidence checks, 595440 long-age incidence checks (counts across grids and pair roles, not distinct keys). P=6 wait-jump charge 968149.822232 partitioned exactly: RESET 122519.645987; nonreset short distinct 153795.891368; nonreset short equal 35797.159690; nonreset short root 33019.913135; nonreset long 623017.212052. Distinct positive refined keys at P=6: 369/562/135/299/1864 respectively (3229 total). P=30 and P=210 totals 802745.670689 and 777371.019163. Largest focus: 2886 T reaches, 75256 completed events; P=6 wait-jump 200740.920687 with RESET 27447.750516, short distinct 45764.550007, short equal 11660.332930, short root 24977.813819, long 90890.473415. Finite long-age sector large under R=8. No quantitative inference of asymptotic rarity or final contraction. All exact equalities/inequalities tested as specified passed.
