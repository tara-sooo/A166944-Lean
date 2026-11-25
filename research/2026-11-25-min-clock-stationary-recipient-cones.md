# Stationary-recipient slot cores and the long-age LOW-donor cone

2026-11-25 JST. Continues 6852f2c6d631f1da620963b77eabbc273b0b66a1. New paper results: exact first-contact cross-arrival partition in a completed recipient slot; independent r-weighted donor and receiver capacities over all first-contact events in that slot, avoiding the small growth-rate capacity of a large receiver; long-age separation at an explicit earlier horizon cut; and nonreset donor-anchor reduction for a LOW jump into a long-wait rough recipient. Arithmetic support bounds on these anchors pay a further absolute quota and identify a sparse physical near-top anchor sector. Heavy small/medium anchor source mass remains open. No Lean compilation; twin infinitude OPEN.

## 1. Setup and exact recipient-slot ledger

Keep X dyadic, N=X/2 odd original sources M in [X,2X), B=ceil(sqrt(7X)), u=log B, s_M=M+2, C0=2M-2, H=4B and original gate K(M)=floor((7M-1)/4). Original complete waits end at the first recorded event at or beyond s_M+H or twin termination, e_M<=s_M+H+2B. Each completed wait from b to v at J has length <=2r(J)<=2p_out<=3(p_out-1). The original horizon and clock gain are O(B), C<=2t, and d=2t-C<=12B+6. Original masks, upward-origin levels, terminal classification and any frozen prior payments remain as in 629f56a through 6852f2c. Aggregate each unordered original pair's actual remaining old terminal charge across every original A and level into W_ij<=U=6B+3. This cap is per pair, not per origin. No new reference pairs or occupation.

Focus on true jump-stationary first contacts at (t,J), with incoming selected prime p at t for the donor, and the other tag (recipient) already at J since its own recorded arrival a<t. Both visit the same completed recipient slot S=(J,v), where v is the unique next event after t at J. It is completed in both original prefixes since the positive old charge is supported at or after this first contact, at a completed rough slot. The donor's preceding wait is <=2p. Recipient age A=t-a satisfies 1<=A<2r(J). 

For all actual tags in S partition by actual arrival clock b. Any two tags with distinct arrivals b<b' at this slot meet physically for the first time exactly at (b',J): an earlier shared state would imply identical next arrivals by determinism, contradicting distinct b. The later arrival cannot be a stationary continuation from elsewhere; it is either root injection or a jump. The former is a separate first-contact type. Thus all jump-stationary pairs form a subset of the complete cross-arrival graph, with each edge directed from the later (jumping) arrival to the earlier arrival. If n_b is the actual number of tags entering at b, the total potential cross-arrival pair count is exactly sum_b n_b sum_(c<b)n_c. The actual aggregate weight of the selected jump-stationary sector is <=U times this count; this does NOT say that every such pair has positive old charge. Different arrival clocks are disjoint source cohorts. Each pair is assigned to exactly one first-contact slot across its entire original energy history, even if it has charges at many later origins. No partition by first contact of thinned masks.

## 2. NEW r-weighted bilateral slot capacities, with anchor-specific receiver refinement

Set m=u^(11/4). Work on the actual aggregate jump-stationary edges whose recipient slot has r(J)>=R=cB/u^2 (fixed c>0), r(J)>0. In each slot put a donor-role constraint per vertex on ALL its outgoing edges at this slot, with capacity r(J)m. Put a recipient-role constraint per vertex on ALL its incoming edges at this slot, also with capacity r(J)m. A tag may serve both roles at one slot but is charged at most twice. For every tag, since each slot occurs on an original completed wait and r<=p_out<=1.5(p_out-1),
    sum_(its distinct recipient slots) r(J) <= 1.5 total original gain=O(B).
Thus the sum of these capacities over all tags and slots is O(XB m). Repeatedly pay all current incident edges of any constraint with total current degree <=capacity. Each constraint pays at most once and each edge at most once. No sum over arrival times at a recipient vertex, and no dependence on the growth-rate of the already large recipient cohort. Surviving edges satisfy both role-degree inequalities. In particular each endpoint must have more than r(J)m/U=Omega(u^(3/4)) actual aggregate charged partners at that slot in the relevant role. This controls the receiver even when its first-contact forest logarithmic growth in 6852f2c is very small. These are aggregate pair partners at original first contacts, not all reference ancestors.

Refinement using the actual long-LOW donor anchors defined in section4: choose even primorial L<=u^(1/16) largest, largest prime y, and f=u^(1/16). At each slot, classify a long-age LOW donor by its actual last nonLOW anchor g=(J_a,t_a,q), and call it comparable if q>=r(J)/f. Let k_comp be the number of distinct such comparable anchors occurring in the actual edges at this slot. Keep the same donor-role cap. For each recipient split its incoming edges into one pooled other sector with cap r m and one constraint per actual comparable anchor with cap r m/max(1,k_comp). The sum of recipient capacities is <=2rm per vertex. Hence total cost including donor capacities is still
    P_slot=O(XB u^(11/4))=o(XB u^3).                 (1)
For each surviving comparable edge the recipient has >r m/(U max(1,k_comp)) distinct actual charged donors from that specific anchor. As shown in section4, k_comp=O(L f)=O(u^(1/8)), so the bound is Omega(u^(5/8)). Noncomparable pooled receiver constraints still yield Omega(u^(3/4)) partners at the slot. The donor-side role constraint always yields Omega(u^(3/4)), across earlier recipients. This does not bound individual source mass of a high-density group.

Use fixed weights and capacities during the deletion process; its remaining support is the greatest subgraph satisfying all strict degree bounds. One can apply earlier entropy/multiscale/origin/contact payments first on actual unpaid pair-level weights, aggregate, apply (1), and allocate paid aggregate back consistently to its original pair-levels. Subsequent fractional payments can destroy strict degree bounds, so re-peel if using them later. The numerical comparison below applies slot caps independently on the same raw sampled pairs, not cumulatively.

## 3. NEW explicit long-age clock-separation witness

For a jump-stationary pair at (t,J), let a=t-A be the earlier recipient's actual arrival. The donor has started by a+3: its root horizon <=J, so s_D=C0(D)/2+3<=J/2+3<=a+3. If A>=15, put
    h=2 floor((A-3)/12),  K0=J-h.
At true tick a+3 the donor is active and has not yet arrived at J. From that tick through its actual jump into J, the elapsed time is bounded by three times the remaining gain, since the remaining partial first wait is <=the full bound and all subsequent waits finish by t. Hence
    J-C_D(a+3) >= (A-3)/3 >= 2h.
The recipient is already at J. In particular donor has not crossed K0 at a+3, while recipient has crossed it or started above it by a. The donor's first crossing of K0 lands at J_D in (K0,J] at clock b_D>a+3. The completed remaining gain to J is J-J_D<h, so t-b_D<=3h. If b_R is the recipient's earlier crossing time or root injection above K0, b_R<=a. Therefore
    b_D-b_R >= A-3h >= (A+3)/2.                     (2)
This is an actual clock separation at a shared horizon cut, not just different predecessor labels and not a bound on source separation. K0 is even but not necessarily a primorial multiple; it can be used in the exact first-crossing partition of 253a240. One can choose any even K in the permitted shorter interval instead (same inequalities with h=J-K). Choosing a primorial multiple there is possible when the interval is wider than L, with the same separation bound. No proof that the separated crossing fibres have small multiplicity. Equation (2) applies independently of the incoming p, even if a donor is a much older original source. It is proved only for the actual original paths up to the observed first contact, not a hypothetical reference arrival.

## 4. NEW long LOW donor anchor is nonreset and unique

Now p<=y, r(J)>=R, recipient age A>3L+3. Let g=(J_a,t_a,q) be the donor's actual last selected q>y before its jump into J, or its root if none. The LOW-only suffix from that state through the jump into J cannot cross an even primorial boundary. Thus delta=J-J_a satisfies p-1<=delta<L, t-t_a<=3delta. In the root-only case take J_a=C0(D), t_a=s_D; that state has d_a=6. At first contact d(t)=2t-J=2A+d(a)>=2A. The LOW-tail gain/clock identity gives
    d(t)=d_a+2(t-t_a)-delta<=d_a+5delta,
    d_a>=2A-5delta>6.                                (3)
Hence neither a root-only LOW donor nor a genuine RESET donor anchor d_a=6s (s=t_a mod2) is possible. In particular the last q>y exists, and is nonreset with positive phase d_a=6s+2q k,k>=1. The odd q=3 special phase is immaterial since eventually y>=5; direct inequality (3) also excludes every d_a<=6 without a phase convention. This eliminates entire classes of actual long-age paths, rather than simply paying them with a quota.

Because r(J)>y, J is the first endpoint of the deterministic LOW suffix at which no next LOW event can occur, provided the suffix reaches this rough target. Thus a fixed actual labeled donor anchor has at most one such rough recipient slot (J,v) and unique donor arrival t. Other original tags reaching the same anchor have the same deterministic suffix or stop earlier. This is not the last nonLOW anchor of the recipient, nor the first entry into the block. It may be a small/medium nonLOW q, even when recipient r is huge. All long LOW jump-stationary aggregate pair charges can be assigned to their unique donor anchor (across all actual recipient arrival ages and later old origins), since donor orientation is fixed by the first contact.

At a fixed recipient slot, t in [v-2r+1,v-1], J_a in (J-L,J), and t_a in [v-2r-3L,v-1]. Comparable q>=r/f>=cB/u^(2+1/16), so for each J_a and parity there are O(1) eligible prime factors of J_a+2s. The clock progression has O(1+(r+L)/q)=O(f) times. There are O(L) possible J_a. Consequently k_comp=O(Lf), proving the receiver-specific refinement of section2. No bound of this form for all small q.

## 5. NEW uniform donor-anchor key support and global aggregate quotas

Let S_q count possible distinct long LOW donor anchors with fixed q>y that can have such a rough recipient target. Bound by relaxed tuples (J,delta,t_a,s,q) with delta even, 2<=delta<L, J_a=J-delta, q|(J-delta+2s), t_a=rho(q,s) mod2q, 6<d_a<=12B+6. For each J,delta,s,q the clock possibilities are O(B/q) (indeed phase k>=1). Count J in an O(X) range, and require actual r(J)>=R and <=B. Actual deterministic suffix and MIN only reduce support. The count of tuples upper bounds distinct anchors; use their actual unique target only when grouping real charges.

Direct two-form sieve on J-1,J+1 in the congruence J=delta-2s mod q gives O(X/(q u^2)) horizons uniformly. Use sieve primes ell<=z0=B^(1/64) excluding 2 and q; the two roots are distinct for each ell and removal of q changes the Mertens factor by a bounded constant. The progression length >=cB absorbs the same O(z0 log(2z0)) remainder as the established Ford Theorem2.4 application in research/2026-11-24-min-growing-cutoff-sieve-weighted-reset.md. If q divides one neighbor and q<R the true rough class is empty, so relaxing that prime is harmless. Summing offsets and clock phases,
    S_q=O(XB L/(q^2 u^2)).                            (4)
For q<=B^(1/8) strengthen as in the previous small-recipient two-congruence proof. Choose r'=r(J) in [R,B], sign sigma, r'|J+sigma. The primes r',q are distinct in this band. CRT gives J mod 2qr', with interval length >=c B^(7/8), so the uniform sieve on (J+sigma)/r', J-sigma excluding q saves u^2; determinant relation -2sigma makes the forbidden roots distinct. Sum r' reciprocal O(log u/u) and phases to get
    S_q=O(XB L log u/(q^2 u^3)), q<=B^(1/8).          (5)
For q in near-top band Q0=ceil(c B/u^(2+1/16))..B (constant c from R), (4) and Chebyshev sum 1/q² give
    sum_(q>=Q0) S_q = O(XB L/(Q0 u^3))
                     = O(X u^(-7/8))=o(X).           (6)
In particular the actual comparable long LOW donor keys are a sparse set of physical events, regardless of their source multiplicity. The estimate uses roughness of the target, not of the donor pre-wait; counts are not ancestor numbers. The stronger conditional two-prime sieve (5) is not used for near-top q (CRT intervals there can be very short).

Split small q<=B^(1/8), medium B^(1/8)<q<Q0, near-top q>=Q0 (eventually ordered). For each actual donor anchor aggregate its remaining pair weights over every original old origin/level and recipient tag. Pay min(actual anchor charge, cap_q), where
    cap_q=q u^(23/4)/L in small or near-top band,
    cap_q=q u^(19/4)/L in middle band.
The small reciprocal sum is O(log u), the middle sum O(1), near-top O(log u/u). By (4),(5),
    P_anchor=O(XB u^(11/4)(1+log u)^2)=o(XB u^3).    (7)
This pays actual energy on the aggregated key, independent of how many subsequent old charges occur. Asymptotically these caps can be much smaller than U per pair for fixed q; no conclusion that arbitrary tiny-label pairs are all paid. Equation (6) does not imply o(X) source tags in this class. In particular a single q=11 anchor may already contain many roots. Previous large-label contact caps, entropy and slot constraints can be combined on actual unpaid weights, not by adding overlapping measured payments.

## 6. Finite verification and new concentration example

Standalone research/min_clock_stationary_recipient_cone_audit.mjs, initial commit 20484704cc26440385ef8101bb9370cf64d8900e, final 8b84b1d15d735a9942ac2508b5c7a6fe6aae9d0d, exact remote blob 7a8ec9e1e8ef318d9b9d24a943e95c54ac906fac. Retains the prior literal MIN, exact inverse sampled targets, pair-level uniqueness, first physical contact and entropy checks. New actual donor/recipient record lookup, shared slot and distinct arrival checks, donor preceding wait, exact age and (2) via literal state lookup and actual crossings, full LOW suffix nonreset tests (3), unique actual anchor target and arrival, aggregate role-weighted fixed core with independent repeated-removal oracle, individual r-sum against total actual gain, cross-arrival pair count, and direct relaxed donor anchor-target phase support. All final assertions passed.

Run:
    node research/min_clock_stationary_recipient_cone_audit.mjs 4096 16384 65536
    node research/min_clock_stationary_recipient_cone_audit.mjs 65536 --wide-comparable
Actual functions executed in available JS runtime, not separate Node invocation. Final 12 normal stress window/base/occupation combinations and 2 extra wide-comparable control combinations. Uses 12 selected original rough slot/level targets per X, previous delayed masks and multiscale/entropy controls unchanged; base1/8 for new slot quota base*r/B and anchor quota base*q/B, R=max(y+1,ceil B/16), L30,y5, comparison f4; P=max(y+1,floor sqrt(B)/2), Q=max(y+1,ceil B/4) for finite anchor bands. Extra independent recipient f32 control changes ONLY this diagnostic comparison threshold, not the previous masks or pair weights. These are not the asymptotic parameters/caps of (1),(7). The two arithmetic sieve bounds and the asymptotic k_comp estimate are paper results; direct enumerations provide finite relaxed support checks, not a fitted sieve constant. Independent slot and anchor payments on same sampled raw pair weights, not cumulative. No future extension/type split.

| X | original occupation | rough-recipient jump-stationary raw | base8 slot paid | base8 slot residual |
|---:|---|---:|---:|---:|
|4096|late HIGH|480.03216|15.54619|464.48597|
|4096|full positive|796.55889|37.84016|758.71873|
|16384|full positive|54.88833|54.88833|0|
|65536|full positive|14000.33105|264.93804|13735.39301|

Largest X65536: 31 sampled recipient slots, 15 fully paid at base8, 1664 tag-slot memberships with sum r=235870, slot capacity3460.96755. 24425 actual long-age cut checks (A>=15, across all jump-stationary sampled pairs, not just rough recipients); max age153. Max six occupied arrival times per sampled recipient slot. Base1 paid4.53791. Long-LOW rough-recipient aggregate charge8634.74845, all retained by slot peeling at both bases. Smaller windows have no sampled long-LOW sector for L30 age>93. At X65536 short-LOW rough sector4621.79379 includes root-only254.27806 and reset anchor590.40880, which do not contradict (3).

All long-LOW sampled mass concentrates on exactly two actual NONRESET donor anchors:
| anchor (J_a,t_a,q) | recipient J | donor arrival | donors in sampled edges | distinct pair edges | aggregate weight |
|---|---:|---:|---:|---:|---:|
|(203038,101860,11)|203040|101862|92|13156|5485.62455|
|(165478,82892,17)|165480|82896|22|4246|3149.12390|

Both suffixes have gain2, so each consists of a single LOW p=3 event (elapsed2 and4 respectively). Anchor deficits682 and306. Thus the entire long-LOW sampled sector consists of two small/medium earlier nonreset labels, not near-top donor labels. In these sampled bipartite groups pair counts equal 92*143 and22*193 respectively (this equality does not assume all actual ancestors beyond the sampled edges). Finite f4 comparable sector empty; independent f32 makes both comparable and exercises the per-anchor receiver constraints, still no payment of these heavy groups. This is a concentration diagnosis, not an asymptotic upper bound. Direct relaxed anchor support in finite small/middle/top bands12733333/5567333/265018, actual1/1/0. Finite anchor quota base8*q/B pays only0.33038348 combined. At all finite windows the long-LOW near-top branch is empty, so (6) is paper-only as a sparse-sector statement.

## 7. Next target

For long-LOW rough-recipient contacts the old charge can be traced uniquely to an earlier NONRESET donor anchor with large deficit d_a>=2A-5L, with a demonstrably separated precontact clock cut. Use nonreset arithmetic reverse reachability for the actual donor cohort at that anchor, especially small/medium q, and explore whether repeated such anchors can be charged by a strict accumulated gain/deficit inequality rather than another partial quota. The p=3 after q=11 or17 examples are concrete diagnostic targets. Near-top donor keys are sparse but heavy masses remain; short-age or nonrough recipients remain outside this reduction. Prior original immediate/later, heavy distinct-slot, low-r anchor and MED/full positive terms remain open. No full energy estimate and no Lean compilation. Main and other branches unchanged.
