# Hypothetical infinite MIN worlds XVII: coupled clock directions and wide-label affine supply

2026-11-26 JST. Independent continuation of [XVI asymmetric and repeat](https://github.com/tara-sooo/A166944-Lean/blob/cde2bbc23ed52618b546ff4e9eb15557b8e6182a/research/infinite-orbit/asymmetric_repeat.md), [XII joint factor-clock pair](https://github.com/tara-sooo/A166944-Lean/blob/dfde7f8c2b3fb63361d25959793931971ad5db95/research/infinite-orbit/close_factor_clock.md), and [XV nonrank capacity](https://github.com/tara-sooo/A166944-Lean/blob/eadacc275f0200ddb1c184035b8b2ed0f6227c68/research/infinite-orbit/nonrank_capacity.md). Sibling preflight [direct 14c6176 modular hyperbola](https://github.com/tara-sooo/A166944-Lean/blob/14c6176473bd6b30599d06a02e49cc2679c227ae/research/2026-11-26-min-direct-modular-hyperbola-three-root-source-sieve.md), [unified 14f1820 cycle-gap saturation](https://github.com/tara-sooo/A166944-Lean/blob/14f18204b4e23643529cd1d529a3d1b0c6e2eee0/research/2026-11-26-min-unified-cycle-gap-saturation.md). Here the three labels may be widely separated; there is no small label-difference assumption or prime-cofactor assumption. The new conditional classes are parallel corrected shift directions, zero transition determinants, and a polylogarithmically thin fixed rational FIRST-label ratio together with a nonzero second transition determinant. These are different from the horizon-only rank in XIII-XVI and from unified's fourfold cycle gap or inverse-polylogarithmic relative ratio interval. Paper deductions and finite diagnostics, no Lean or external novelty claim.

## 1. Exact two-coordinate transport

Fix the physical pre-horizon window [X,lambda X), T>=eta sqrt X, B=floor sqrt(lambda X+1), fixed positive eta and lambda>1. Retain a fixed ordered selected high list (T<=p_i<=B) on an actual MIN ray in the canonical necessary time envelope H/2<=t<=3H+3. Words are consecutive in the same selected list. Every intervening omitted physical event contributes to the actual relay gain and elapsed time. No primality condition on cofactors. For three selected events let labels p,r,v be pairwise distinct; use index i=0,1,2. For post-state (J_i,n_i), arrival side s_i, define
    a_i=(J_i+2s_i)/p_i=q_i+1,
    c_i=(n_i-2s_i)/p_i.
These are integer quotients; a_i even and c_i parity s_i. Both are Theta(T) uniformly in the envelope. For the first and second transitions (j=1,2), E_j is the gain of all intervening unselected events, V_j=n_j-n_(j-1)>0, sigma_j=s_j-s_(j-1). (E_j is a LOCAL relay, not a cumulative offset.) Put
    D_j=E_j-1+2sigma_j, d_j=V_j-2sigma_j.
D_j is odd and nonzero. d_j is nonzero: if sigma_j=0, V_j is a positive even integer; if sigma_j=+-1, V_j is positive odd. d_j can be negative in the even-to-odd unit-time case. Exact horizon and clock rows are
    p_j(a_j-1)=p_(j-1) a_(j-1)+D_j,
    p_j c_j=p_(j-1) c_(j-1)+d_j.                   (1)
Eliminate p_(j-1) using these equations modulo p_j. Since successive prime labels are distinct,
    ell_j=(D_j c_(j-1)-d_j a_(j-1))/p_j
is an integer and
    D_j c_j-d_j a_j=p_(j-1) ell_j-d_j.              (2)
In particular for L=E_1+E_2, W=V_1+V_2,
    |ell_j|=O(L+W+1).
The integers ell_j are NOT the horizon rank determinants or the adjusted-deficit multipliers. They may vanish, in which case the source quotient slope equals d_j/D_j exactly. This is a simultaneous clock-product identity and has no dependence on primality of any q_i.

## 2. Parallel directions: the outer-label recurrence

Assume D_1 d_2=D_2 d_1. Write (D_j,d_j)=t_j(D,d), with primitive integer pair gcd(D,|d|)=1, D>0 odd, d!=0, t_j odd nonzero (may be signed). Set xi_i=D c_i-d a_i. By (1) and distinct prime labels, r divides xi_0, v divides xi_1, so write xi_0=m_0 r, xi_1=m_1 v. Combining the two rows of (1) along the primitive direction gives
    r(xi_1+d)=p xi_0,
    m_1 v=m_0 p-d.                                (3)
This holds exactly even when the label differences are of order T. If |d|<T, neither m can vanish: if m_0=0, then |m_1 v|=|d|<v, forcing m_1=0 and d=0, impossible; if m_1=0 the same argument uses p. They have the same sign, and |m_0| and |m_1| are comparable because p,v in [T,B] and |d|=o(T). Their absolute values are O(D+|d|). Also m_0 has parity s_0 and m_1 parity s_1 since D odd and a even. For a longer word whose successive shifts all lie along the same primitive direction, the same computation yields
    m_(i+1) p_(i+2)=m_i p_i-d
for every consecutive triple of distinct successive labels, with m_i=xi_i/p_(i+1). If the total elapsed time is less than T-2 then all labels in the word are distinct, by the two-clock repeat spacing of XVI. The capacity proof below is for triples; no long-word count is claimed.

## 3. Two-prime affine supply for parallel directions

Let E_1+E_2<=L, V_1+V_2<=W, where L>=0,W>=2 are bounded by fixed powers of log X. Set P=L+4, Q=W+2, S=P+Q. We count necessary horizon/phase candidates on the full physical block and hence actual triple occurrences on any ONE ray. Fix the three sides, (D_1,d_1),(D_2,d_2) (these determine E_1,E_2,V_1,V_2) and primitive m_0,m_1. Equation (3) puts p in one residue class mod |m_1|/gcd(|m_0|,|m_1|), or has no integer solution. The p,v forms have nonzero determinant since d!=0; both primes >=T. Along the progression, a fixed-dimensional translated upper Selberg sieve with sufficiently small fixed-power cutoff yields
    # prime p,v << T*gcd(|m_0|,|m_1|)/|m_1|
                   *(loglog X)^2/log^2 X.         (4)
Here and below coefficient and determinant sizes are polylogarithmic, exceptional prime factors cost at most the indicated power of loglog by the product over primes up to a fixed power of log X, and the progression is polynomially long in T after padding. The fixed-dimensional sieve error can be absorbed with small fixed-power cutoff as in XIII. For fixed cutoffs the loglog factor is unnecessary.

For each prime pair p,v and fixed shift data, the first arrival n_0 has one residue mod 2pv (or no solution), since the total elapsed V_1+V_2 is fixed and the endpoint clocks are fixed. The global envelope has length O(X), so at most O(1) arrivals. Given n_0, r must divide n_0+V_1-2s_1; this positive integer is O(X) and has at most O(1) distinct prime divisors >=T (at most two for sufficiently large X). Then H_0 is fixed mod pr by the first two horizon factors and fixed E_1, so O(1) possible horizons. We do not count every such candidate as actual; each is only necessary. A given physical source horizon occurs at most once on one increasing ray, and its consecutive triple is unique in the fixed selected list. No ensemble multiplicity or ancestry is inferred. The CRT length here is SHORT and used for an upper count of O(1), not for a sieve in that progression.

For fixed primitive (D,d), write S_0=D+|d|. By comparability of the m's, for each |m_1|<=C S_0 only |m_0|<=C' |m_1| need be summed. The elementary gcd divisor identity bounds
    sum_(m0,m1) gcd(|m_0|,|m_1|)/|m_1|
          << sum_(1<=m<=C S_0) tau(m)
          << S_0 log(2+S_0).
Signs cost constant. Now group the aligned shift pairs by t=max(|t_1|,|t_2|)>=1. There are O(t) signed multiplier pairs at this maximum, and D<=P/t, |d|<=Q/t. Dropping the primitive/parity restrictions only enlarges the upper bound. The sum of S_0 over these primitive possibilities is O(P Q(P+Q)/t^3). Hence the summed shift and m cost is O(P Q S log(2+S)), since sum t^(-2) converges. Weight each actual triple by at most C_w T, fixed constant. We get
    F_parallel(L,W)
       << X P Q S log(2+S) (loglog X)^2/log^2 X.   (5)
For fixed L,W this is O(X/log^2 X). It applies with arbitrary composite cofactors and arbitrary label gaps. It is an absolute full-window bound, not a proportionally localized Hspan bound: the remaining horizon CRT supplies O(1) regardless of Hspan. There is no inference of asymptotic phase rejection from finite diagnostics.

## 4. Nonparallel directions and two coupled congruences

Let Qdet=D_1 d_2-D_2 d_1. From (2) at the middle event and the second transition,
    D_1 c_1-d_1 a_1=p ell_1-d_1,
    D_2 c_1-d_2 a_1=v ell_2.
Without any division these imply
    Qdet c_1=d_2(p ell_1-d_1)-d_1 v ell_2,
    Qdet a_1=D_2(p ell_1-d_1)-D_1 v ell_2.         (6)
When Qdet!=0 they reconstruct the middle quotient coordinates from the three labels and two determinants. From r c_1=p c_0+d_1=v c_2-d_2, reduce the first row of (6) multiplied by r modulo p and v. In the polylog short-elapsed regime d_1,d_2 are nonzero and smaller than the labels in absolute value, hence invertible at the respective primes. We obtain
    r(v ell_2+d_2) = -Qdet mod p,
    r(p ell_1-d_1) = -Qdet mod v.                 (7)
These congruences also hold for Qdet=0 under the same invertibility assumption. For Qdet!=0, |Qdet|=O(P Q), smaller than T for polylog cutoffs. In particular the hyperbola residues in (7) are nonzero. These are two simultaneous necessary congruences, not independent uniform distribution hypotheses. The general count of the nonparallel, two-nonzero-ell, widely separated class is still open.

One degeneracy is tractable. If ell_1=0, (7) says v divides Qdet-r d_1; if ell_2=0 it says p divides Qdet+r d_2. The numerator in either case is nonzero eventually because |Qdet|=o(T), and the resulting integer quotient b is nonzero and O(Q). Fix the four shifts, signs, and this b. For ell_1=0 the two labels r,v obey b v=Qdet-r d_1; for ell_2=0 the pair p,r obey b p=Qdet+r d_2. They are two nonconstant nonproportional prime forms, because Qdet!=0. Use an integer progression as in (4), bounded by O(T (loglog X)^2/log^2 X) candidates even if the progression spacing is ignored in the main term. The two fixed labels and known relative time give O(1) arrival phases by CRT, the third label divides its corresponding corrected time and thus has O(1) possibilities, then O(1) horizons as above. Sum four shifts O(P² Q²), b choices O(Q), and bounded signs. This gives the coarse bound
    F_nonparallel,zero(L,W)
       << X P² Q³ (loglog X)^2/log^2 X.            (8)
Fixed L,W removes loglog. It is valid without any cofactor primality. A sharper sum over primitive coefficients might reduce the powers in (8), but is not needed for the fixed-cutoff result. The audit checks the general congruences; no zero-ell triple was observed in the fixed actual corpus.

## 5. Three-prime sieve from a narrow rational FIRST-label ratio

This gives a different tractable part of the general all-distinct class, and uses the clock relation even when |r-p|=Theta(T). Fix coprime positive M,N independently of X. Suppose
    N r=M p+h,    |h|<=A,
where A>=1 is polylogarithmic. For sufficiently large X, h!=0 since p,r are distinct primes larger than M,N. Do NOT assume the shift directions parallel. From the first congruence of (7),
    h ell_2 v + C = k p,
    C=h d_2+N Qdet,                               (9)
for some integer k. Suppose ell_2!=0. All coefficients are polylogarithmic, |h ell_2|<p and |C|=o(T). C cannot be zero, since p would divide h ell_2 v, whereas p!=v and p cannot divide the nonzero small factor h ell_2. Also k!=0 because v>=T and |C|=o(T). Uniformly |k|=O(|h ell_2|) by v/p=O(1).

Fix h, all four shifts and sides, ell_2, k. The three labels are now nonconstant affine forms of one integer parameter p:
    p,    r=(M p+h)/N,    v=(k p-C)/(h ell_2).
p,r and p,v are nonproportional since h,C nonzero. If the r,v forms are proportional, their ratio is a rational with numerator and denominator polylogarithmically bounded; it cannot equal the ratio of two distinct primes >=T. Thus any such tuple has no valid all-distinct prime candidates, and can be discarded. This gives three nonproportional prime forms even with ALL cofactors composite. Congruence h ell_2 | k p-C gives a single p progression with step |h ell_2|/g, g=gcd(|k|,|h ell_2|), or no solutions. The extra r-integrality requirement can only reduce the set; alternatively include the fixed modulus N. Apply the fixed-dimensional upper sieve, omitting primes dividing the denominators, with count
    << T g/|h ell_2| *(loglog X)^3/log^3 X.
For each such p,r,v, E_1,V_1 and sides fixed, the source horizon and time are each determined mod pr (or 2pr for parity), hence O(1) possibilities in the envelope. Sum k of size O(|h ell_2|) with gcd weight: O(tau(|h ell_2|)). Then sum 0<|h|<=A, 0<|ell_2|<=C S using tau(ab)<=tau(a)tau(b); cost O(A S log(2+A) log(2+S)). The four shifts and sides cost O(P² Q²). Thus
    F_ratio,nonzero(A,L,W)
       << X P² Q² A S log(2+A) log(2+S)
                    (loglog X)^3/log^3 X.         (10)
For fixed A,L,W this is O(X/log^3 X), stronger than a two-label ratio-only sieve by one logarithm, and does not require an upward source. If ell_2=0, (9) requires C=0 for short cutoffs, and such triples are in the zero class of (8): a parallel short triple cannot have ell_2=0 by (3). We do not apply (10) to this degeneracy. The first-pair ratio is fixed M/N; for M!=N, all relevant first label differences are of order T. The ratio bound requires |N r-M p| polylog, not merely |r/p-M/N|<=1/polylog. In particular unified's current near-saturation ratio theorem does not force this narrow strip.

## 6. Aggregate implications and limits

Consider a collection of actual all-distinct triples in the same fixed selected list with disjoint time spans and disjoint strict relay interiors, each weight <=C_w T and total weight >=rho X. Use actual U=sum(E_1+E_2) and Vtot=sum(V_1+V_2). Under U=O(T log^alpha X), Vtot=O(T log^beta X), alpha,beta>=0, choose slightly larger logarithmic cutoffs L,W and discard o(X) weight by Markov tails. Equation (5) then makes parallel-direction weight o(X) if
    alpha+beta+max(alpha,beta)<2.
Equation (8) also makes the nonparallel zero-ell weight o(X) if 2alpha+3beta<2 (which implies the preceding inequality). Under both budgets with 2alpha+3beta<2, macro weight must therefore come from nonparallel directions and two nonzero ell's. In addition, for any fixed finite collection of first-label ratios M/N and strip width A=O(log^gamma X), (10) makes their nonzero-ell weight o(X) if
    2alpha+2beta+gamma+max(alpha,beta)<3.
The same tail and (8) handle zero ell when its hypothesis holds. These are conditional population restrictions, not a claim that the whole actual fast population has these budgets or must be near one fixed ratio. They require genuinely polylog average elapsed time, much stronger than fast in the usual sense 4w<=p-1. They also do not control the time between disjoint words, and no signed-deficit or missing-wait budget is automatically improved. Counts are absolute O(X) bounds; summing over tags is legitimate with the same full physical X scale, but a short lifetime Hspan needs new localization or additional hypotheses. No multiplication by an empirical rejection fraction.

## 7. Finite verification

[Audit 5d11adf](https://github.com/tara-sooo/A166944-Lean/blob/5d11adf4f154dcfad37d27b3f03a6ae878bc9d16/research/infinite-orbit/clock_direction_audit.mjs), blob ab5324d6d1603cf055393d66c0c7259f562c24d3, exact remote readback. Run node research/infinite-orbit/clock_direction_audit.mjs. Actual ECMAScript execution in tool runtime, not separate Node. The first census version underestimated the factor table's required maximum: corrected arrival integers can be as large as 3 times the physical horizon ceiling. Expanded to 12*65536+4096, added explicit factor-domain checks and reran; final assertions pass. Counts below are final, superseding initial incomplete census.

Same prior actual corpus: X=4096,16384,65536, [X,4X), T=ceil(sqrt X/2), B=floor sqrt(4X+1). 64,512 canonical roots, 9,959 targeted valid intermediate starts (no established canonical ancestry), 1,616,573 actual events, 74,191 stops, 280 exits, zero unresolved cap, 85,254 high visits, 162 independent literal tick gcd checks. All 21,921 consecutive high triples, 20,739 all-distinct triples satisfy (1),(2),(6), with 20,456 paired congruence checks where both clock offsets are invertible at their respective labels. None of those all-distinct actual triples had parallel directions or zero ell. 19 all-distinct triples had E_1+E_2<=16 and V_1+V_2<=16, all nonparallel with nonzero ell. These are finite incidences, not statistical evidence that parallel directions are impossible.

Independent aligned census: (L,W)=(0,4),(2,6),(4,8), all three X. One route enumerates source clocks, factors the two later corrected clocks, checks the horizon CRT and eligibility; the other route enumerates the affine outer-label relation (3), recovers possible arrivals and middle labels, then checks the horizon conditions. 60 shift-configuration incidences, 9 exact candidate set equalities, 664 compatible physical/phase candidates across overlapping cutoffs. Actual incoming feasibility and deterministic MIN continuation accept 181 of those incidences, with 84 having |v-p|>=T/2; 64 have prime source cofactor. For the accepted local examples the minimum chosen incoming wait is never positive-drift; this is not a statement about all possible incoming waits. They are intermediate states without certified canonical ancestry. Thus parallel directions are locally possible, including wide gaps, despite being absent in the ordinary sampled corpus.
| X | L=0,W=4 candidate/actual | L=2,W=6 | L=4,W=8 |
|---:|---:|---:|---:|
|4096|28/10|28/10|69/12|
|16384|51/21|51/21|158/25|
|65536|56/26|56/26|167/30|

Example actual local parallel triple (X4096,T32):
    H_0=12428, labels 43,37,61, cofactors 289,337,205;
    first arrival n_0=29154, V_1=V_2=2, E_1=E_2=0, sides all even.
    (D_1,d_1)=(D_2,d_2)=(-1,2), primitive (D,d)=(1,-2).
    m_0=34,m_1=24; 24*61=34*43+2.
The first event is realizable at t=29153. This is an exact fast word with composite source and final cofactors. It is not a canonical root history.

Near-ratio diagnostics on actual corpus: six fixed ratios M/N=1,2,3,3/2,2/3,1/2, |h|<=16, E_total,V_total<=16. 20 actual congruence controls (overlapping ratio incidences), 14 within explicit finite small-coefficient condition |h ell_2|,|C|<p with nonzero ell_2, all C nonzero. Example canonical p,r,v=107,71,163, source H=29640,q=277, first arrival14980, E_1=2,E_2=12, V_1=3,V_2=13, sides0,1,0. M=2,N=3,h=-1, Qdet=36, d_2=15, ell_2=-27, C=93; equation (9) gives 27*163+93=42*107. Both later waits are 1, target cofactors 419 and 183. This is an actual large-gap three-label case, not a claim of asymptotic scale behavior. No analytic sieve constant or population-budget test. No Lean kernel verification.

## 8. Remaining problem

The remaining broad class now has two coupled modular congruences in three distinct prime labels, with nonzero determinant Qdet and nonzero ell's, but can avoid all thin rational first-pair strips and allow larger elapsed times or relays. The modular-hyperbola sieve of the sibling lane does not by itself yield the necessary simultaneous count at the scale of short words. A next target is to bound simultaneous solutions of (7), including the case of fixed small offsets but unrestricted label ratios, or to build a relaxed diverse-label/clock survivor that tests which actual local constraints remain essential. The same physical relay and elapsed resources are not counted again in other ledgers. No full all-constraint infinite model, general uncapped mixed-run bound, Lean proof or finite-twin contradiction. Main and sibling branches not modified by this work.
