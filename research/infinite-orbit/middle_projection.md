# Hypothetical infinite MIN worlds XVIII: exact coupled inverse and middle-clock projection sieve

2026-11-26 JST. Continuation of [XVII coupled clock directions](https://github.com/tara-sooo/A166944-Lean/blob/893d1f8a15b0ea8570395b3dbaffa3ce2e390ece/research/infinite-orbit/clock_direction.md), [XVI asymmetric and repeat](https://github.com/tara-sooo/A166944-Lean/blob/cde2bbc23ed52618b546ff4e9eb15557b8e6182a/research/infinite-orbit/asymmetric_repeat.md). Sibling preflight [direct 14c6176](https://github.com/tara-sooo/A166944-Lean/commit/14c6176473bd6b30599d06a02e49cc2679c227ae), [unified 74032ff](https://github.com/tara-sooo/A166944-Lean/commit/74032ffab29ee99639c9680febdaa621ff552692). New: the simultaneous nonparallel congruences admit an exact inverse with one middle label per outer pair and coefficient tuple. A separate projection identity gives three prime affine forms under a narrow rational MIDDLE clock/horizon strip, not a narrow label-ratio strip. This includes small middle deficit multiplier, all composite cofactors and order-T label jumps. The short relay and short elapsed assumptions remain quantitative; the broad nonparallel class is not eliminated. Paper deductions and finite arithmetic checks, not Lean proof or external novelty claim.

## 1. Setting and exact inverse of the simultaneous congruences

Use the fixed selected high list of XVII in a physical window [X,lambda X), T>=eta sqrt X, B=floor sqrt(lambda X+1)=O(T), fixed lambda>1, eta>0. A triple of successive selected events with pairwise distinct prime labels p,r,v in [T,B] retains all actual physical relays. All prehorizons H_i=p_i q_i+e_i, q_i odd >=p_i, e_i=1-2s_i. Post coordinates J_i=H_i+p_i-1, n_i are arrival tick and horizon, a_i=(J_i+2s_i)/p_i=q_i+1 even, c_i=(n_i-2s_i)/p_i of parity s_i. The canonical necessary envelope H_i/2<=t_i<=3H_i+3 and w_i<=2p_i implies a_i,c_i=Theta(T). Intermediate states satisfying this envelope are allowed for local feasibility, not presumed canonical ancestry.

Let E_j>=0 even be the actual LOCAL relay gain preceding selected event j=1,2, V_j=n_j-n_(j-1)>0 the actual elapsed time, sigma_j=s_j-s_(j-1). D_j=E_j-1+2sigma_j odd nonzero, d_j=V_j-2sigma_j nonzero. Exact rows from XVII:
    p_j(a_j-1)=p_(j-1)a_(j-1)+D_j,
    p_j c_j=p_(j-1)c_(j-1)+d_j.
With distinct successive labels,
    ell_j=(D_j c_(j-1)-d_j a_(j-1))/p_j
is integer and D_j c_j-d_j a_j=p_(j-1)ell_j-d_j.
Assume E_1+E_2<=L and V_1+V_2<=W with L>=0, W>=2 polylogarithmic. Write P=L+4, Q=W+2, S=P+Q. Then |ell_j|=O(S), |D_j|<=P, |d_j|<=Q. Denote the determinant by Z=D_1 d_2-D_2 d_1, to distinguish it from cutoff Q.

For Z!=0 the exact middle coordinates are
    c_1=[d_2(p ell_1-d_1)-d_1 v ell_2]/Z,
    a_1=[D_2(p ell_1-d_1)-D_1 v ell_2]/Z.             (1)
The two simultaneous congruences from XVII are
    r(v ell_2+d_2)=-Z mod p,
    r(p ell_1-d_1)=-Z mod v.                         (2)
Since 0<|Z|=O(PQ)=o(T), its residues at p,v are nonzero; each coefficient of r in an actual solution is invertible at the corresponding prime. Thus fixed p,v, shifts and ell_1,ell_2 give ONE residue class of r modulo pv, or no solution. Since B<pv eventually, at most one r in [T,B] is possible. No small label gap or ratio assumption.

There is also a converse at the level of necessary product/clock coordinates. Compute a_1,c_1 by (1), rejecting nonintegers. Compute r by (2), rejecting an invalid label or noninvertible coefficient. Define
    a_0=(r(a_1-1)-D_1)/p, c_0=(r c_1-d_1)/p,
    a_2=(r a_1+D_2)/v+1,   c_2=(r c_1+d_2)/v.        (3)
The clock integrality in (3) follows from (1),(2) when Z,d_1,d_2 are invertible modulo the respective primes (as in the short regime). Indeed Z r c_1 = d_2 r(p ell_1-d_1)-d_1 rv ell_2; reduction mod p or v gives the requisite r c_1=d_1 mod p, r c_1=-d_2 mod v. The horizon integrality then follows from the two defining middle determinant rows and invertibility of d_1 mod p and d_2 mod v. The shifts and determinant rows follow by substitution. Still check positivity, parity, H_i in the window, eligibility p_i²<=H_i+1, actual gain/elapsed data and first arrival envelope; these are not supplied by CRT alone. Recover H_i=p_i(a_i-1)+e_i and n_i=p_i c_i+2s_i. This reconstructs all necessary candidate horizons and arrival ticks from the outer labels and the bounded coefficient tuple. Exact incoming feasibility and deterministic forward MIN must still be checked. This is not canonical ancestry. The O(T²) unrestricted outer-label search remains too large for a submacroscopic bound on one ray.

## 2. Rational projection, independent of the rank determinant

Fix positive coprime M,N independently of X, representing the slope M/N. Define the projected integer h_i=N c_i-M a_i and local shift b_j=N d_j-M D_j. Combining the two exact rows gives
    p_j(h_j+M)=p_(j-1)h_(j-1)+b_j.                   (4)
This is an exact transport identity even with all cofactors composite, arbitrary ell_j and Z, and unrestricted label ratios. It differs from XVII's fixed rational FIRST-label ratio. The middle strip is |h_1|<=A, for A>=0 polylogarithmic, i.e. |c_1/a_1-M/N|<=A/a_1. The actual reduced denominator of c_1/a_1 need not be small.

Let h=h_1, f=h_0, g=h_2+M. Then
    p f=r(h+M)-b_1,
    v g=r h+b_2.                                   (5)
Since p,r,v comparable and |b_j|=O_M,N(S)=o(T), |f|=O(|h+M|+1), |g|=O(|h|+1). All are polylogarithmic and smaller than T in magnitude eventually.

If h!=0,-M, then f,g,b_1,b_2 are nonzero. For instance f=0 forces r(h+M)=b_1, impossible at small shifts; b_1=0 forces r(h+M)=p f, which with distinct primes and small coefficients forces h+M=f=0. The second row is analogous. The only degenerate projections are:
    h=0: g=b_2=0, f and b_1 nonzero;
    h=-M: f=b_1=0, g and b_2 nonzero.
They cannot occur together for M>0. In the first case h_1=0 and b_2=0 imply ell_2=0; in the second h_0=0 and b_1=0 imply ell_1=0, by proportionality of (D_j,d_j) to (N,M). The converse (ell_j=0 always implies the corresponding projection degeneracy) is not claimed. No nonparallel assumption is needed in (4)-(5).

If N is even, neither degeneracy can occur: b_j=0 would give N d_j=M D_j and hence N|D_j since gcd(M,N)=1, contradicting D_j odd. This is a genuine arithmetic distinction between slopes, not a bound on all slopes.

## 3. Three-prime affine sieve with summed progression lengths

Retain nondegenerate middle strips, h!=0,-M. Fix shift data (E_1,E_2,V_1,V_2,sides), h,f,g. Then the three labels are the affine forms in r
    r,   p=[(h+M)r-b_1]/f,   v=[h r+b_2]/g.          (6)
They are nonconstant and neither of the latter is proportional to r because b_1,b_2!=0. If p and v were proportional, their ratio would be the ratio of two nonzero products of polylog-sized coefficients; after reduction its numerator and denominator are both smaller than T for large X. This cannot be the ratio of the two DISTINCT primes p,v>=T. Such a tuple therefore has no valid candidates. This proves the requisite nonproportionality without any cofactor-prime assumption.

The integrality of (6) either is inconsistent or puts r in a single residue modulo
    k=lcm(|f|/gcd(|f|,|h+M|), |g|/gcd(|g|,|h|)).
On that class use one integer parameter in a padded interval of length comparable to T/k+1. This length is polynomially large in T for polylogarithmic A since k=O((A+1)^2) with constant depending on M,N,lambda,eta. All three prime forms are >=T in valid tuples. The usual fixed-dimensional translated upper Selberg bound used in XIII-XVII gives
    # prime label triples << (T/k) (loglog X)^3/log^3 X.
For clarity, the nonzero determinants and leading coefficients are polylog-sized after clearing denominators and restricting to the progression; omit primes dividing them and the finitely many small primes. Their exceptional product is O((loglog X)^3) by the product over primes up to a fixed power of log X. A sufficiently small fixed-power cutoff in the padded length absorbs the polynomial remainder of the fixed-dimensional sieve. Fixed cutoffs A,L,W remove the loglog factor. No independence of actual visits is assumed.

For fixed p,r and the first shift and sides, H_0 and n_0 are separately fixed modulo 2pr (or the class is inconsistent). Each ranges over O(X), so O(1) candidates. The third endpoint is determined by gains and times. Even a single-ray bound can use this upper count; each increasing physical source horizon occurs at most once and the triple in the fixed selected list is unique. Exact MIN could only reduce this count. We do not multiply by any empirical phase-rejection rate.

Sum progression lengths rather than the raw number of coefficient tuples. Put B_0=C(A+1). For each h!=0,-M and f,g in the stated ranges, write f'=|f|/gcd(|f|,|h+M|), g'=|g|/gcd(|g|,|h|). At each f' at most tau(|h+M|) possible |f|, and similarly at g'. Therefore
    sum_(f,g) 1/k
      << tau(|h+M|) tau(|h|) sum_(1<=u,v<=B_0) gcd(u,v)/(uv)
      << tau(|h+M|) tau(|h|) log^3(2+A).
The last step uses gcd(u,v)=sum_(d|u,d|v) phi(d) and two harmonic sums. Sum over h with |h|<=A excluding 0,-M. Cauchy-Schwarz and tau(n)^2<=d_4(n), sum_(n<=Y) d_4(n)=O(Y log^3(2+Y)), give
    sum_h tau(|h+M|) tau(|h|) <<_M (A+1) log^3(2+A).
Thus summing 1/k over all projection tuples costs O((A+1) log^6(2+A)), not O((A+1)^3). Finally the shift tuples cost O(P²Q²), and each triple is weighted by <=C_w T with C_w fixed. We obtain the absolute full-window capacity
    F_middle,nondeg(A,L,W)
      << X P² Q² (A+1) log^6(2+A)
             (loglog X)^3/log^3 X.                   (7)
In particular fixed A,L,W give O(X/log^3 X). This covers all nondegenerate projections, not just nonparallel triples or nonzero ell. It is a count of necessary candidates valid for actual weighted triples on one ray, not a lower bound or a normalized short-lifetime estimate.

## 4. Degenerate projections and even denominator

When h=0, the first relation is r M=p f+b_1 with f nonzero O(1) and b_1 nonzero. For fixed shifts and f, p,r form two nonproportional prime forms with small coefficients. Fixing these primes and shift data gives O(1) possibilities for H_0,n_0 by CRT. The final v divides the known positive corrected final clock n_0+V_1+V_2-2s_2=O(X), hence has O(1) possible distinct high prime divisors. When h=-M, use v g=-M r+b_2 with g nonzero O(1) and b_2 nonzero. Fix r,v, recover middle H_1,n_1 by CRT, and recover p from the known positive corrected first clock. In either case the two prime forms can be counted by the same translated two-form sieve, O(T (loglog X)^2/log² X) with fixed tuple, and bounded weight per candidate.

One of the two shifts satisfies b_j=0, so (D_j,d_j) is an integer multiple of (N,M). For fixed ratio this costs only O(min(P,Q)) choices, rather than O(PQ). The other shift costs O(PQ), and the finitely many sides and bounded f or g cost O(1). Thus
    F_middle,deg(L,W)
       << X P Q min(P,Q) (loglog X)^2/log² X.         (8)
For fixed cutoffs the loglog factor is absent. For even N the left side is identically zero eventually, as shown above. The bounds (7),(8) count all distinct-label triples with the given strip and short total shifts, irrespective of prime cofactors or the rank determinant. They impose no bound on general triples outside that strip.

## 5. Middle adjusted deficit, and aggregate conditional consequences

For M=1,N=2, the projected coordinate is exactly
    p_i h_i=2 n_i-J_i-6s_i.
This is the adjusted ordinary post-deficit; for a nonreset height of the form 2 h_def p_i+6s_i, h_i=2 h_def. Thus the three-prime bound (7) applies to ALL distinct-label short triples with small middle adjusted deficit multiplier (no degeneracy since N even). Exact h_1=0 is impossible under these small-shift, distinct-label hypotheses. This is an alternative to requiring a small label ratio or small horizon rank. It also applies to arbitrary other fixed positive slopes with even denominator, not just the deficit projection.

Let an actual collection of distinct-label triples in the same selected list have disjoint strict relay interiors and disjoint elapsed intervals, weight per triple <=C_w T, total weight F>=rho X. Suppose actual summed relay U=O(T log^alpha X), summed elapsed Vtot=O(T log^beta X), and either every triple is in the given middle strip of width A=O(log^gamma X), or summed absolute projection over the collection is O(T log^gamma X), with alpha,beta,gamma>=0. In the latter case discard the large-projection tail by weight <=C_w T times that sum divided by the enlarged cutoff. Choose L,W,A slightly larger log powers so all required tails are o(X). Equation (7) makes the remaining nondegenerate strip weight o(X) when
    2 alpha+2 beta+gamma<3.                            (9)
For even N this eliminates the whole strip population. For odd N also require alpha+beta+min(alpha,beta)<2 to eliminate the possible degenerate weight by (8). Equivalently, under these budgets a macro short distinct triple population must escape the designated small middle projection. A fixed finite set of rational slopes can be handled by summation. No statement for a growing family of all rational slopes is made here. If the usual fast condition only gives waits O(T), or if low relay is o(T) rather than polylog, (9) does not follow. Neither the current sibling transport inequalities nor finite twins alone imply these quantitative budgets. The counts are absolute full-window estimates; shorter original lifetimes require additional localization or explicit summation over actual physical windows. No new independent charge to omitted mass, deficit recovery or tag multiplicity.

The inverse from section 1 and the projection estimate leave the remaining nonparallel, nonzero-ell, unrestricted-label-ratio class outside every fixed narrow middle strip. A small middle projection is an additional assumption, not a consequence of (2). The broad class might use large denominator slopes and order-T projections, or larger total relay/elapsed times. This note supplies no general count of its simultaneous modular hyperbola solutions.

## 6. Finite verification and reproducibility

[Audit 86d3129](https://github.com/tara-sooo/A166944-Lean/blob/86d3129e02a30cca42de4fcaea5bf9ca737c0650/research/infinite-orbit/middle_projection_audit.mjs), blob 292d9ad6de377f61ffc18bba6cdad2589d255c48, exact remote readback. Run node research/infinite-orbit/middle_projection_audit.mjs. Actual ECMAScript executed in available tool runtime (not a separate Node invocation). First audit 41a62ad checked nonzero ell only; final version extends census to both degeneracies and arbitrary ell. All final assertions pass; full arrival factor-domain check retained from XVII.

Same deterministic actual corpus as XVII: X=4096,16384,65536, [X,4X), T=ceil(sqrt X/2), B=floor sqrt(4X+1). 64,512 canonical roots, 9,959 targeted valid intermediate starts (not certified canonical ancestry), 1,616,573 events, 74,191 finite stops, 280 exits, zero cap unresolved, 85,254 high visits, 162 independent literal tick gcd checks. Among 21,921 consecutive high triples, 20,739 pairwise-distinct, all nonparallel in this corpus. All 20,739 middle and outer inverse controls pass; 20,206 also satisfy the finite invertibility conditions and give exact unique middle r by CRT. 103,695 projection identities over five slopes 1/2,1,2,3/2,2/3, 20,739 adjusted-deficit identities. 13 projection incidences with E_total,V_total<=16, |h|<=16 satisfy the small-coefficient test and nonproportional three-form controls, all with minimum pairwise label gap >=T/4; no degenerate ordinary-sample cases in this small-cutoff subset.

Independent necessary candidate census uses clock enumeration and later corrected-clock factors versus middle projection reconstruction of labels and clocks (including degenerate case by two-prime reconstruction and factoring the remaining clock). Both routes check product/horizon CRT, parity, eligibility and source arrival envelope, and the same explicit finite small-coefficient cut. At X4096,16384 use (L,W,A)=(0,4,4),(2,6,8) for slopes 1/2 and 1; at X65536 use only (0,4,4) for both slopes to bound the computation. 432 shift configuration incidences, ten exact set equalities, 142 necessary candidate incidences (105 degenerate, 37 nondegenerate). Exact incoming and deterministic forward MIN validate 12 incidences (8 degenerate, 4 nondegenerate), including 3 with all pairwise label gaps >=T/4 and 4 prime-source-cofactor incidences. Configurations overlap; these are not distinct canonical roots, no asymptotic proportions inferred. No degenerate candidates for slope 1/2. Breakdown necessary/local (degenerate necessary/local in parentheses):
| X | (0,4,4), 1/2 | (0,4,4), 1 | (2,6,8), 1/2 | (2,6,8), 1 |
|---:|---:|---:|---:|---:|
|4096|1/1 (0/0)|4/1 (4/1)|4/2 (0/0)|42/1 (24/1)|
|16384|0/0 (0/0)|5/0 (5/0)|4/0 (0/0)|57/6 (47/5)|
|65536|0/0 (0/0)|25/1 (25/1)|not run|not run|

Actual canonical example of the new deficit strip:
    H_i=10122,10174,10210; p_i=53,37,83;
    q_i=191,275,123; arrivals n_i=5143,5145,5146;
    waits=31,2,1; sides=1,1,0; E_1=E_2=0.
For M=1,N=2: (h_0,h_1,h_2)=(2,2,0), (b_1,b_2)=(5,9). Thus 37*3=53*2+5 and 83*1=37*2+9. The middle actual post-deficit is 80=2*37+6. Both later waits are fast and the minimum prime gap is 16>=T/4 for T=32; the middle and final cofactors are composite. The very same physical triple is recovered in the independent census with an incoming feasible wait of 1 (different source pre-time, same post-state). This is a real MIN local transition as well as an observed canonical trajectory at the original pre-time. No analytic sieve constants or macro hypothesis tested, no Lean verification.

## 7. Remaining world

The exact inverse exposes the necessary two-dimensional outer-label search; the middle-projection sieve removes narrow rational clock strips (in particular small adjusted deficit multipliers under (9)) even when labels are widely separated and cofactors composite. General simultaneous congruences outside these strips remain open, as do short-lifetime localization, arbitrary long nonparallel recovery words, larger relay/elapsed budgets and the full hypothetical integer infinite orbit. Next useful target: exploit projection transport over longer words to restrict repeated visits to the same rational strips, or count nonparallel congruences when all projections are large. No full all-constraint infinite model, general uncapped mixed-run bound, Lean proof or finite-twin contradiction. Main and sibling branches not modified by this work.
