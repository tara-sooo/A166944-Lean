# Negative MIN: arbitrary-scale two-sided relay sieve, periodic relays, and one cheap-history criterion

2026-11-27 JST. Continuation of [302ece5](https://github.com/tara-sooo/A166944-Lean/commit/302ece57ea3bb86dc8727a078649b63da8c65c08). The goal is unconditional twin infinitude. Here the first-pair sieve is strengthened by a nonzero height-factor count for fast successors and a two-sided roughness sieve for slow successors, including unequal scales. Then the positive branch's periodic terminal map is transferred to arbitrary negative MIN postheights with capped actual inherited mass. This removes the relay length summation for all-small relays, enlarges the lower cutoff of the unresolved intermediate labels from loglog R to a power of log R, and gives one clipped cheap-history retention statistic in place of two separate asymptotic hypotheses. A greedy ledger computes it exactly. The positive asymptotic retention estimate remains open; no twin proof.

## 1. Capped cohorts; time capacity without departure-phase entropy

Use synchronized windows of width W=6 floor(T/6), T=ceil sqrt(2R+1), N~R/6 canonical roots A in [R,2R], birth n_A=3-A/2, latest birth n0 in each window J and retirement n0+T. Observe the T postticks in [n0,n0+T). Every completed event of prime p decreases the even center x by p-1; all gains through retirement <=3T+6. Each observed stationary segment has length ell<=min(T,2q(x)), q(x)=min(lpf(x-1),lpf(x+1)). At a completed event ell<=min(T,2p). At most B0=ceil((3T+6)/W)+2=O(1) windows can visit a fixed x in the expanded slab I=[lo-3T-6,hi].

Allow ANY selected cohort C with at most M roots per (J,Y), Y the actual retirement position; no bound on the FULL fiber is required. In particular a cohort can retain min(M,m_J(Y)) roots in each window endpoint. At fixed x and firing clock n within J, all roots visiting that departure phase have identical future and endpoint, so at most M selected roots contribute. A source phase thus has normalized time weight at most M min(1,2p/T), where weight is sum ell/T across selected roots. Given x,p, there are O(1+T/p) possible firing clocks per visiting window, and hence total weight O(M). Equivalently fix the source sign e=-1 or +1 with x=pu+e and postheight h=n+(x-p+1)/2. The even firing for e=-1 gives h=0 mod p, the odd firing for e=+1 gives h=3 mod p. All actual h are between 0 and O(T). There are O(1+T/p) possible h; fixing x,p,h determines n. This equivalent parameterization is useful for the periodic sieve.

The terminal non-twin time on C is unconditionally at most
    (B0 M/N) sum_(x non-twin in I) min(1,2q(x)/T)
      << M/(log R)^3.                                      (1)
Here use the dwell sieve of 66f63e3. Each selected terminal fiber contributes at most M times its one-root dwell cap; no light-fiber assumption or majority phase is needed.

Write L=log R. For later use fix 0<d<1. Completed sources with p>=Y0 and observed ell<p^d have total time O(Y0^(d-1)) per root, by sum p=O(T). At all remaining sources q(x)>=ell/2>=p^d/2. For fixed p and sign the two neighbor forms on x=pu+e are u and pu+2e. The ordinary two-root Selberg upper sieve gives O(R/(p log^2 p)) possible rough sources uniformly for Y0<=p<=O(T) when Y0 grows at least as exp(L^gamma) for fixed gamma>0. Indeed use sieve primes below p^d/2, level p^c for sufficiently small fixed c; progression length R/p>>sqrt R, error O(p^(6c)) negligible, omit p and 2,3. By the phase weight cap and dyadic prime upper count,
    completed time fraction p>=Y0 on C
      << Y0^(d-1)+M/log^2 Y0.                             (2)
For the narrower band p>=Pmax=T exp(-L^alpha), 0<alpha<1,
    completed time fraction p>=Pmax
      << Pmax^(d-1)+ M(1+L^alpha)/L^3.                     (3)
The latter uses log p comparable to L and O(1+L^alpha) dyadic bands. All time fractions here and below are normalized by FULL N and T, not by |C|.

Important obstruction to a tempting shortcut: with M=L^beta, beta<2, (2) makes all completed labels above Y0=exp(L^gamma), beta/2<gamma<1, negligible. But the ordinary twin upper sieve itself gives O(R/L^2) twin centers, whose total capped endpoint mass is O(N M/L^2)=o(N). Thus a positive capped retention together with negligible low repeat time cannot both hold unconditionally at this small cap. This is NOT a viable unconditional sufficient condition for the desired proof. Below use beta>2 and the stronger near-square-root bound (3). This corrects the initial small-cap exploration.

## 2. Fast successor eliminated by its height factor, even at unequal scales

Consider two successive completed HIGH events relative to a fixed threshold Y0: source p>=Y0 at x=pu+e, its next completed r>=Y0 at y=rv+f, e,f in {-1,+1}, with only labels <Y0 between them. Let E=x-p+1-y be the intervening gain, an even nonnegative integer. The source fires at n, the target at n+D. For source observed time >0, n is after n0; all waits following it through r are full, not left-truncated. Every completed wait is <=3 times its gain. With target full wait w_r,
    D<=3E+w_r.
Let h=n+(x-p+1)/2 be the source postheight. The height immediately before the target jump (after increment of its clock) is h+D-E/2. By the target firing congruence,
    r divides H = 2h+2D-E+1     for f=-1,
    r divides H = 2h+2D-E-5     for f=+1.                  (4)
The postheight after target is nonnegative, so H>=r-6>0 for r>6. In particular the degenerate zero factor cannot occur. Also H=O(T) for an actual pair. This is a useful difference from a bare reset congruence for the target POSTheight, which can be zero.

Fix dyadic bands P<=p<2P, Q<=r<2Q, P,Q>=Y0/2, P,Q<=O(T), and 0<=E<=B<Y0-3. Exact spatial relation:
    rv=p(u-1)+a, a=e+1-E-f.                               (5)
Since a is odd, nonzero, |a|<=B+3<p, p!=r. Suppose the target is fast, w_r<r^d. Then 1<=D<=3B+(2Q)^d. Count source tuples with possible actual firing phase:

- O(P/log P) source primes and two signs.
- O(T/P+1)=O(T/P) source heights in the class 0 or 3 modulo p.
- O(B+1) choices of E, O(B+Q^d+1) choices of D, two target signs.
- For fixed p,h,E,D,e,f the nonzero H in (4) has at most O(log R/log Q) prime factors r>=Q. This uses only the integer size bound.
- For each such r, the two independent spatial congruences modulo p and r give O(R/(P Q)+1)=O(R/(P Q)) possible x in I; the last comparison uses P,Q<=O(sqrt R).
- Fixing x,p,h determines n, and time weight is O(M P/T) over at most B0 windows.

Divide their product by N~R. The resulting unconditional capped time bound for fast targets in this pair of bands is
    << M(B+1)(B+Q^d+1)/(Q log P) * log R/log Q.           (6)
No source roughness is needed for (6), nor any upper restriction on P/Q or reset assumption. In particular if Y0=exp(c L^alpha), M polylog R, and B<=Y0^nu with fixed nu<min(1/2,1-d), summing the O(L^2) band pairs is o(1), bounded crudely by
    O(M(B+1)L^3 [(B+1)/Y0+Y0^(d-1)]).
This controls actual inherited mass by phase, rather than applying the unweighted fast-successor count to arbitrary roots.

## 3. Both slow: five exclusions, arbitrary scales

For an observed source with ell>=p^d and a successor w_r>=r^d, both source neighbors are p^d/2-rough and both target neighbors r^d/2-rough. In (5), the following five restrictions hold at every sufficiently small sieve prime l>5:
    r!=0, v!=0,
    rv!=-2f, rv!=a-p, rv!=a-p-2e mod l.                  (7)
The three product residues are nonzero distinct integers when p>=11 and E>=0 (a<=3); their pairwise differences and product form a nonzero integer Delta of size R^O(1). At primes not dividing Delta, the forbidden r=0 or v=0 fibers have 2l-1 points; each of the three nonzero product fibers has l-1 points and they are disjoint. Hence exact local forbidden count is 5l-4. For exceptional primes omit them. Uniformly for a nonzero integer |Delta|<=R^C, the product of the omitted factors 1+O(1/l) is <=(loglog R)^C' for a fixed C': split at l=log R, use Mertens on the small primes and at most O(L/log L) large prime factors.

Here is an unconditional count over arbitrary polynomial-scale bands, P,Q>=R^epsilon/2. Fix small eta=1/128. If 4P Q<=R^(1-eta), fix p,r,e,f,E. The x progression has length O(R/(pr)), at least R^eta in scale; impose the four linear forms x-1,x+1,y-1,y+1. For primes not dividing pr times d0(d0-2)(d0+2), d0=p-1+E, they have four distinct forbidden residues. A Selberg sieve on the progression of level R^c, c sufficiently small depending on epsilon,d,eta, gives
    O(R/(pr L^4) (loglog R)^C')
possible x. The local count remainders O(4^omega(d)) and weights <=d give quadratic error O(R^(6c)), negligible for c<eta/16. The truncated Euler product/Markov argument is as in 14c6176 and 66f63e3. Sum p,r using Chebyshev's upper count, e,f and E<=B; the resulting tuple count is
    O(R(B+1)(loglog R)^C'/L^6).                          (8)

If 4P Q>R^(1-eta), both P,Q>=c R^(1/2-eta). For fixed p,e,f,E use rv=a mod p, rectangle r in [Q,2Q), v in [1,O(R/Q)]. The elementary Kloosterman estimate O(p^3/4) of 14c6176 applies to every nonzero frequency because a!=0 mod p. On arbitrary arithmetic progressions in this rectangle the normalized Fourier l1 bounds are O(log p+Q/p) and O(log p+R/(Qp)). Both ratios are O(R^eta). Hence the congruence count on each residue pair mod any sieve modulus coprime to p is its area main term plus O(R^(3/8+2eta) L^2). Replacing progression cardinalities by length/modulus introduces only smaller rounding errors. The main scale is R/p>>R^1/2. Apply the five-condition Selberg sieve (7), omitting Delta primes; use level R^c with c<=1/256 and sufficiently small for roughness. Its quadratic error multiplies the preceding error by O(R^(8c)), still power-saving relative to R/p. The truncated Euler product has size >> L^5/(loglog R)^C'; local densities 5/l-4/l^2 and omitted primes give this by the same Euler-product argument. Thus fixed p contributes O(R/(p L^5)(loglog R)^C'), and summing source primes proves (8) also in the high product regime. This extension does not assume comparable magnitudes, only the actual gain cap and the polynomial lower threshold.

With the O(M) time weight per source tuple, (8) and (6) show all short-relay high pairs with E<=B, observed source slow and arbitrary scales have total capped time
    << M(B+1)(loglog R)^C'/L^4 + o(1)                    (9)
for polynomial Y0 and polylog B. If bands are restricted to comparable P,Q, only O(L) pairs of bands occur and the denominator improves to L^5. Source fast time is already negligible by section 1. This improves the old one-sided comparable estimate L^3 in 302ece5 and permits B=L^b with beta+b<4 (arbitrary scales) or beta+b<5 (comparable scales).

For subpolynomial Y0=exp(c L^alpha), use min(P,Q)^c for the four-root sieve level in the low product case; this gives a denominator (log min(P,Q))^4 log P log Q instead of L^6. The high product case is unchanged. Summing over dyadic indices k=log_2 P,l=log_2 Q uses
    sum_(k,l>=k0, <=O(L)) 1/(k l min(k,l)^4)
       << log L/k0^4,
so (9) is replaced by O(M(B+1)(loglog R)^C''/(log Y0)^4)+o(1). This is useful for fixed short relays, but the next section removes B altogether for relays with a restricted alphabet.

## 4. Transfer the periodic terminal map at arbitrary postheight

Use the terminal-map idea of the positive branch [6667063, sections 1–4](https://github.com/tara-sooo/A166944-Lean/blob/6667063eb3ea9a7c6ac316279a526854dcc08ca9/research/2026-11-26-min-primorial-periodic-relay-sieve.md), but allow every negative postheight h, not only the singular heights 0 and 3. Define
    z=floor(c0 log Y0),  Q_z=2 product_(3<=q<=z odd prime) q.
Choose c0>0 small enough by Chebyshev so Q_z<=Y0^nu with fixed nu<min(1/2,1-d). Here and in section 5 Y0=exp(theta L^alpha), 0<theta<1, so z is of order L^alpha. The letter Q_z is a period, distinct from the target band Q.

Retain only labels <=z, with exactly the same clock/least-prime rule. Each retained jump is confined to its initial common-multiple cell of width Q_z (e173792). Thus the restricted computation from any even position and clock terminates, gain E<Q_z, and its entire gain/time/event count is periodic in position and clock modulo Q_z. This follows from strict spatial decrease and divisibility of the period by every 2q. The terminal state is the first state having no eligible retained prime.

In an actual consecutive Y0-high pair whose intervening events ALL have labels <=z, suppose the target wait is slow, w_r>=r^d>2z. Every actual preceding retained jump is exactly the restricted winner. At the target source no retained prime can be eligible, since otherwise its firing would occur within 2z ticks. Hence the relay gain is exactly the restricted terminal gain from (x-p+1,n). For fixed p,e,h and x mod 2Q_z, the time n=h-(x-p+1)/2 is fixed mod Q_z and so is the starting position mod Q_z. Consequently E is fixed on that progression. No reset assumption or upper bound on the number of retained events is needed.

Count both-slow sources by a four-linear-form upper sieve. Fix p,e,h,b=x mod 2Q_z. Then x=pu+e, u is on one class mod 2Q_z (p>=Y0>z), with progression length O(R/(p Q_z)) and scale >>R^(1/2-o(1)). The exact E fixed as above gives y=x-d0, d0=p-1+E. Both neighbors of x and y are Y0^d/2-rough; impose the four forms on the progression at primes >z below a small power of Y0. Their distinctness fails only at divisors of d0(d0-2)(d0+2), a nonzero integer of size R^O(1). Omit those primes. In fact their extra singular-factor cost is bounded for this growing z: the sum of reciprocals of primes between z~c L^alpha and L is O_alpha(1) by Mertens, and the contribution of divisors >L is O(1/log L). The same Selberg construction with level Y0^c has negligible error, since Y0=R^o(1) and the progression is of power size in R. Its main product gives
    # x << R/(p Q_z) * (log z)^4/(log Y0)^4.             (10)
The bound is uniform in the progression, sign, p, h and its individually determined E. There is NO multiplication by Q_z for relay gains.

Sum over the O(Q_z) residues b; the period denominator cancels. There are O(T/p) heights and time weight per x,p,h at most O(M p/T); these factors cancel too. Finally sum source primes using sum_(Y0<=p<=CT)1/p=O(log L). Thus the total time fraction of these arbitrary-postheight both-slow small-only relays on C is
    << M (log L)^5/(log Y0)^4.                           (11)
All-small relays ending at a fast target have E<Q_z, so use (6) with B=Q_z; it is o(1) by Q_z<=Y0^nu. Source fast time is o(1) by section 1. The final conclusion is:
    If M=L^beta, beta<4 alpha, then capped time on sources of
    consecutive Y0-high pairs with only labels <=z between
    them is o(1).                                       (12)
This actually uses both the height-factor fast count and the sibling periodic map. It controls arbitrary low relay depth, arbitrary postheight, and arbitrary relative sizes of p,r. The large primorial gain Q_z was absorbed by the periodic map rather than summed in the sieve; the fast case uses the power saving to absorb it. It does NOT control relays with labels in the intermediate band (z,Y0).

## 5. A single moving-band cheap-history sufficient condition

Choose fixed parameters
    2 < beta < 12/5,
    beta/4 < alpha < 3-beta,
    0<theta<1, 0<eta0<1.
The interval for alpha is nonempty precisely when beta<12/5. Put
    M=floor L^beta, Y0=exp(theta L^alpha),
    z=floor(c0 log Y0), Pmax=T exp(-L^alpha),
    H_R=floor exp((1-eta0)L^alpha).
Here c0 is chosen as in section 4. In particular Q_z<<Y0 and Y0<<Pmax for all sufficiently large R.

For each actual root define K(A) to be the TOTAL number of completed labels z<p<Y0 from birth through its own window retirement (including events before n0). K_rep(A) counts only repeated labels in that band, with previous use on the same root. Then K(A)-K_rep(A)<=Y0 since each distinct label has one first use.

Take any C as in section 1 and its subset C_bad of non-twin endpoints. The terminal time of C_bad is o(1) by (1). Completed time p>=Pmax is o(1) by (3), since beta+alpha<3. For remaining high sources Y0<=p<Pmax:
- The last high source on each root contributes at most 2 Pmax/T=o(1).
- If its next high event exists and its intervening labels are all <=z, the total time is o(1) by (12), since beta<4 alpha.
- Otherwise its intervening interval contains at least one label z<p<Y0. The intervals between consecutive Y0-high events are pairwise disjoint on a root. Thus all such remaining source time is bounded by (2Pmax/T) K(A).

The low completed time p<Y0 can ALSO be bounded by K(A), without any repeat estimate at p<=z. Each maximal run of <=z events stays in one Q_z cell and has gain <Q_z. The number of runs is <=1+N_high(A)+K(A), where N_high counts completed p>=Y0 and is <=(3T+6)/(Y0-1). Band event gains are <=Y0 K(A). Thus
    G_<Y0 <= Q_z(1+N_high(A)+K(A))+Y0 K(A).
Their observed waits are <=3 times their gain. Therefore the total low time is bounded by
    O(Q_z/Y0 + Q_z/T) + O((Y0+Q_z)/T * K(A)).
Since Y0+Q_z << Pmax, this is <=o(1)+O(exp(-L^alpha) K(A)).

Combine the full observation time on C_bad with these inequalities:
    |C_bad|/N <= o(1)
            + O(exp(-L^alpha) * (1/N) sum_(A in C_bad) K(A)).      (13)
The o(1) is uniform in C. It consists of the terminal/non-twin and near-square-root sieve terms, (11), the fast-target bound (6) with B=Q_z, source fast, last high, and Q_z/Y0. Every term tends to zero for the chosen parameters. Because exp(-L^alpha) Y0=o(1), K in (13) may be replaced by K_rep. This is a genuine reduction of both previously unresolved time phenomena to repeated events in one moving band, with lower endpoint now of order L^alpha rather than loglog R. No condition on arbitrary small-prime repeat occupation, terminal time, global endpoint entropy, or high-label relay gain is needed in (13).

Define the CHEAP clipped retention
    Rho_R(M,H_R)=(1/N) sum_(J,y) min(M,
                   # {A in J : Y(A)=y, K(A)<=H_R}).
Choose that many roots per fiber among the cheap roots. In (13) their total K is <=N H_R, and exp(-L^alpha) H_R=o(1). Hence
    Rho_R(M,H_R) <= B0 M * # {twin centers in I}/N + o(1).         (14)
Under finite twins Rho_R ->0. Conversely, a positive limsup of Rho_R for the displayed M,H_R is sufficient for twin infinitude, and yields >> R/log^beta R distinct twin centers along the relevant slabs. This is one precise statistic instead of separate retention and path entropy estimates. The exponent beta>2 is compatible with the ordinary upper sieve, unlike the shortcut in section 1. For example beta=2.1, alpha=.8, theta=.5, eta0=.1 gives z~c log Y0~c L^.8 and a permitted band-event budget exp(.72 L^.8). This budget is asymptotically subpower of R but much larger than any fixed power of log R. These are sufficient parameters, not an assertion that Rho_R has positive limsup.

## 6. Exact greedy history ledger and attempted closure

The cheap statistic has a simple exact online description using the synchronized merger forest. Each actual occupied component carries the sorted list of the M smallest additive band counts of its ancestor roots (or all counts if fewer). Birth adds [0]. A band event adds 1 to each entry; other events and idle clocks add zero. At a merger take the union of the incoming lists and keep the M smallest counts. The M smallest of a union can be recovered from the M smallest of each member, and a common additive increment preserves the ordering. Induction therefore proves that at retirement these lists are EXACTLY the M cheapest histories of each full endpoint fiber. Repeated-use count is not used for sorting (it is not additive across a common future); the total K is additive.

One may discard every entry whose count exceeds H_R, permanently. Costs never decrease, and discarding these entries cannot remove any future cheap history. At a merger keep the M smallest remaining costs as before. Thus the exact retained fraction satisfies
    Rho_R = 1 - D_merge - D_cross,                         (15)
where D_merge counts normalized discarded cheap entries at actual mergers and D_cross counts entries killed when a band event raises their cost from H_R to H_R+1. These losses are disjoint; they telescope from the N births. Without the threshold, the sum of costs in the final lists plus the sum of costs deleted at merges equals cumulative capped band traffic (each band event increments one unit per live token). This cost identity is also exact.

Apply the earlier age frontier to (15): choose u=floor M (so M_u=1+floor((2u+6)/6)<=M eventually). Use the original full component's maximum ancestor age to define young/old, not the ages of surviving cheap tokens; old status is permanent even if a token is removed. Young submass at a node <=M_u, hence its internal clipped loss is zero. Mixed cheap loss is <=original young mass entering old groups, and old-only cheap loss <=sum of clipped cheap minority groups. Because H_R>>u, a young root cannot die from the budget. Consequently
    Rho_R >= 1-lambda_u-A_cap^cheap(u)-D_cross.             (16)
The exact mixed and old losses can be used in place of their upper bounds. This explicitly reuses the earlier age-frontier proof with the cost-filtered lists.

Attempted closure of (15),(16): since a token must accumulate H_R+1 band events before its threshold death, D_cross<=cumulative capped band traffic/(N(H_R+1)). However the deterministic gain cap gives at best O(T/(z H_R)) here. This tends to infinity (H_R=R^o(1)). Counting all possible band source phases with cap M, R/p admissible positions and T/p clocks per position, gives O(M T/(z log z H_R)), also too large. The clipped age-minority estimate still requires actual collision sparsity; replacing it by all admissible clock counts is similarly too coarse. The full low CRT period up to Y0 is vastly larger than R, so the exact formal deletion law in 326eb62 cannot be used as independence on this growing band. The period used in section 4 is ONLY for labels <=z and was transferred on genuine residue progressions. These are explicit barriers encountered after applying (13)-(16); none proves positive Rho_R. A next proof must control actual capped traffic of band labels z~L^alpha<p<exp(theta L^alpha), or bound the cheap merge/budget losses jointly. Elementary time/gain and phase counting do not suffice.

## 7. Executed verification and persistence

All scripts below were executed as ECMAScript functions before writing and on exact committed source after fetching. No standalone Node or Lean invocation; no independent analytic reviewer. Finite checks validate the identities, arithmetic pins and greedy selection, not the asymptotic sieve or a lower bound for Rho_R.

A. [Two-sided clock pair audit 23f9f56](https://github.com/tara-sooo/A166944-Lean/blob/23f9f56e1ebaa57e770ea7ad99b60c0c1df591a8/research/min_local_negative_two_sided_clock_pair_audit.mjs), blob a90fed0756f3ef702153ced24e1a9c974703ea46. Four slabs R12000..480000, 122004 roots, 2641688 root events and the same number of replay events, 2383913 counted structural checks (1554188 height pairs,376521 rough-form checks), 15643 exact local product-density enumerations incl zero/colliding products. Overlapping threshold controls contain 249393 fast targets and281547 slow targets with the stated finite source/relay test. Exact nonzero target-height factor, source-height residue, relay time, spatial CRT count, capped source/terminal weights and five exclusions checked. Largest slab M222 retains all roots in its window fibers; cap of order L^1.8 retains .998200. Fixed small thresholds used for finite validation, not the asymptotic Y0.

B. [Greedy history audit 83cf0a4](https://github.com/tara-sooo/A166944-Lean/blob/83cf0a447d4fe3610732adc9eb5d10ee2c13860a/research/min_local_negative_minimum_band_history_audit.mjs), blob dabcff4d703c63c85b956caecc724e8de01d873c. Six slabs R12000..2000000, 622004 roots, 2110844 occupied-component jumps,555743 mergers,17010526 independently replayed root events,3127042 counted checks plus exact subcap/threshold mass and cost identities. Uses fixed z5,Y47,B32 and practical Pmax=T/2 for finite disjoint-relay tests; the asymptotic parameters in section 5 need much larger R. At R2e6, fixed band (5,47):
    cap     retention    mean retained cost/N    total capped traffic/N
    1       .0553201     .1530542                1.2601123
    4       .1828112     .6850087                3.3114843
    16      .4868585     2.9310629               6.7758128
    64      .8976489     8.3472503               9.9851590
    275     1            10.5138615              10.5138615
At cap64 and budget16, Rho=.74131274, cheap merge loss .06322806, budget crossing loss .19545920; their sum with Rho is 1 exactly in integer counts. With cap275 and budget16 Rho=.77869878, merge loss0, threshold loss .22130122. These include actual existing twin endpoints, not asymptotic hypotheses.

C. [Arbitrary-height periodic relay audit 974bbd6](https://github.com/tara-sooo/A166944-Lean/blob/974bbd62bf364a434df0ff17e566b6642cb53d27/research/min_local_negative_periodic_relay_height_audit.mjs). Three slabs R12000/48000/192000, 42003 roots,775263 actual completed root events,1319413 pair controls,744456 exact terminal map/translation comparisons,424518 non-reset strong controls and117576 rough-form checks. Fixed z3,5,7,11,13. Example A192006,x191958,p19,source postheight41,next r59,intervening gain12,relay time25,target wait31: exact restricted terminal match despite nonzero noncanonical height. The arithmetic map is compared at both translated source residues and actual clocks, not assumed from a singular return.

No changes to main or sibling branches. All new sufficient criteria are conditional on actual cheap retention; no full proof, Lean kernel verification or claim of external mathematical novelty.

## 8. Further use: asymmetric cutoffs force a narrow-band / near-maximal-count alternative

The periodic sieve in section 4 need not use the same lower bound for source and successor. This permits a further actual consequence of (10)-(13), rather than simply proposing a new task.

Let Y0=exp(L^gamma0), P1=exp(L^gamma1) with fixed 0<gamma0<=gamma1<1; also allow P1=R^epsilon with fixed 0<epsilon<1/2, denoting its logarithmic exponent by gamma1=1. Require source p>=P1, next completed r>=Y0, all intervening labels <=z=floor(c0 log Y0). Keep Q_z<=Y0^nu and d as in section 4. The fast-target count (6) with B=Q_z remains o(1), uniformly after summing all bands. For slow sources and targets the periodic E at fixed p,e,h,b is the same as before.

For (10) use level D=p^c with c sufficiently small and fixed. On the progression in u impose all FOUR linear forms at primes below min(D,Y0^d/2), and only the TWO source forms above that threshold. The local count g(l) is 4/l or 2/l, omitting z, p and the discriminant primes as before. The error O(D^6) is negligible compared with progression length R/(p Q_z) of power size in R. For the truncated Euler product on primes <=D^t, t sufficiently small, Mertens gives reciprocal main form
    >> (log p/log z)^2 (log Y0/log z)^2.
Indeed the first product uses 2/l across the entire range; the ratio (1-2/l)/(1-4/l) supplies the additional two powers up to min(D^t,Y0^d/2). Its logarithm is comparable to log Y0 since p>=Y0. The omitted discriminant primes >z have bounded reciprocal sum for z~L^gamma0, and the expectation of log divisor is O(t log D); Markov retains at least half the product as before. Thus the progression count is
    << R/(p Q_z) * (log z)^4/(log p)^2(log Y0)^2.
Sum over residues and heights with the same capped phase weight as section 4, then sum source primes by the dyadic bound sum_(p>=P1)1/(p log^2 p)<<1/log^2 P1. The resulting capped time is
    << M (log z)^4/[(log P1)^2(log Y0)^2] + o(1).          (17)
This tends to zero if beta<2(gamma0+gamma1). The o(1) includes the fast-target and fast-source cases.

As in section 5, take alpha<3-beta, gamma0<alpha, Pmax=T exp(-L^alpha). For all sources p>=P1, discard p>=Pmax by (3), the last Y0-high event by its tiny time, and the small-only relays by (17). Each remaining source is one of the consecutive Y0-high pairs, and its interval contains an event z<p'<Y0. The intervals are disjoint even though the source threshold is larger. Thus on any capped cohort C,
    eta_(p>=P1)(C) <= o(1)+O(exp(-L^alpha) E_C^* K_(z,Y0)),
                                                            (18)
where E_C^* is the sum over C divided by N. Replace total band count by repeated band count since Y0 exp(-L^alpha)=o(1). No endpoint roughness assumption is needed in (18).

For instance beta=2.1 and alpha=.8 permit gamma0=.15 and gamma1=.95 (sum1.10>1.05), far smaller target cutoff than in the symmetric criterion. Suppose the capped retained non-twin cohort has size >=delta N. Its terminal time is o(1). If at least delta/2 time (up to o(1)) lies on p>=P1, (18) forces
    E_C^* K_rep(z,Y0) >>_delta exp(L^alpha).               (19)
Otherwise at least delta/2 time lies on p<P1. Apply the same small-run argument to the broader band (z,P1): gain of <=z runs <=Q_z(1+N_(>=P1)+K_(z,P1)), and gain of the band <=P1 K_(z,P1). Here N_(>=P1)<=O(T/P1). Consequently low time <=o(1)+O(P1/T E_C^* K_(z,P1)), and
    E_C^* K_rep(z,P1) >>_delta T/P1,                      (20)
provided P1^2/T=o(1), so first uses are negligible. This is true for gamma1<1, and for the polynomial choice epsilon<1/4. For subpolynomial P1, T/P1=R^(1/2-o(1)). Thus under finite twins any positive capped retention forces at least one of: enormous repeated counts in a much narrower small band, or nearly the maximal possible power of R in repeated event count over a broader band. This is a quantitative alternative, not an upper estimate on either count. With beta>2 no conflict with the ordinary twin upper sieve is manufactured. In particular a proof of positive capped retention of roots satisfying both K_rep(z,Y0)=o(exp(L^alpha)) and K_rep(z,P1)=o(T/P1) would suffice; the second budget is much larger than the earlier all-event entropy bound. However deterministic gain gives only O(T/z) for the broader count, and the direct phase supply count O(M T/(z log z)); neither is o(T/P1). The narrow count still lacks a repeated-label estimate. Thus the asymmetric improvement does not close the proof.

[Asymmetric charge audit d4ae7b2](https://github.com/tara-sooo/A166944-Lean/blob/d4ae7b2782ecb5d750efe7edf011dee8751bdc3e/research/min_local_negative_asymmetric_band_charge_audit.mjs), blob a320e6c121652cce4aeb48fb51becbf60f4feb60. Executed as ECMAScript before commit and exact remote readback/reexecution. Four slabs R12000..480000,122004 roots,2641688 actual root events,596016 root/control checks,263179 first-high pairs of which184259 had target below the source cutoff,291453 source-form and11092 additional target-form checks. Finite cutoffs (z,Y0,P1)=(3,11,47),(5,23,97),(7,47,193),(5,97,193),(7,193,389), Pmax=T/2; extra larger-threshold controls added because initial finite controls had no eligible primes in the two-sided target-form interval. All source/target roughness, disjoint relay charges, low-gain and first-use bounds passed. No standalone Node or Lean kernel, no independent analytic verification. Periodic relay audit in section 7C was also re-executed on exact remote blob 20fba54672358331049bf004dadfbe466283a6c2, with the reported counts. Main and sibling branches unchanged.
