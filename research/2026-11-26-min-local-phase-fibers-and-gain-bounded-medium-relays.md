# Exact phase fibers and gain-bounded medium relay inverse uniqueness

2026-11-26 JST. Continuation of 77cad678571ca3cc9dcbd6723c7ae88cf17571fc.
Purpose: recover the predecessor phase information lost in the previous
high-arrival uniqueness theorem, and remove the restriction to a fixed
small alphabet inside a compressed relay. Paper deductions, inherited
upper sieve, and two executed finite audits. No Lean kernel verification,
novelty claim, or twin-infinitude proof.

## 1. The exact time fiber of a selected clock

At even source x let C(x) be the union of all eligible integer clock
progressions: n=0 mod 2p if p|x-1, n=p+2 mod 2p if p|x+1.
At a clock time n in C(x), the least prime at that tick determines
the selected label. Put n_-=max{t<n:t in C(x)}, ell=n-n_-.
For every admissible pre-time v, the next ordinary event fires
at n if and only if

    n_- <= v < n.                                     (1)

The interval is intersected with the time envelope when applicable.
The clock progression of q(x)=min(lpf(x-1),lpf(x+1))
has period 2q(x), so ell<=2q(x). In particular this is the actual
complete pre-time fiber, not an estimate derived from an assumed
distribution of waits. A current event with label p and arrival
(U,n) has known source x=U-p+1, but in general (1) has many times.

There is also an exact way to identify p from the ARRIVAL state,
without counting candidate factors of the offset. At any ordinary
arrival of p>=5, d=2n-U=2ap+s, s=0 for even n, 6 for odd n.
If p>=T, 1<=a, d<=2KT with K<T, then (d-s)/2 is positive
and <=KT<T^2. It has at most one distinct prime divisor >=T.
Thus the incoming high label is unique among high candidates
at such a positive-stratum arrival, even if the alternative
sources had different offsets. The small-label alternatives
and zero-stratum arrivals are not excluded by this observation.

## 2. Compress ANY tail of bounded physical gain

An initial high arrival state (u,v) is permitted when its label
p>=T, its arrival congruences hold (as in 77cad67),
and 1<=a<=K, d_a=2ap+s<=2KT. Hence p<=KT.
Require the time envelope. We permit such relaxed arrivals even
if they have no actual predecessor; this enlarges the graph safely.

From this state follow ordinary uncut MIN for any finite prefix
of total physical gain <=B, including the empty prefix. There is
NO restriction on the alphabet or the number of events in this
prefix, other than the gain bound. Because each w<=2p<=3(p-1),
any endpoint (x,t) satisfies

    E=x-u in [0,B], W=t-v in [0,3B],
    delta=2t-x-d_a in [-B,5B].                       (2)

If B<T-1, this tail cannot itself contain a label >=T.
For the same high label p, the two possible firing time residue
classes are 0 and p+2 mod 2p. Distinct such times are separated
by at least p-2. If two candidate arrivals of that label lead to
the SAME endpoint and 3B<T-2, their firing times coincide by
(2). Parity then determines their side, and their offsets in
[x-B,x] lie in the same class mod 2p, hence coincide. Since
ordinary MIN is deterministic, the entire tail up to x is
also uniquely determined. This proves same-label inverse
uniqueness through arbitrary medium tails, not only fixed
small-prime runs.

More generally compare two endpoints at the SAME offset x with
times t1,t2 satisfying |t1-t2|<=S. If S+3B<T-2, the same proof
shows that DISTINCT initial high arrivals in this comparison
must have DISTINCT labels. Indeed their arrival times differ
by at most S+3B; for equal arrival state determinism forces
equal endpoint time at x.

For a fixed small alphabet one can replace the bounds in (2)
by the previous exact <=11 relay bounds E<=104, W<=133,
delta in [-16,192]. Then S+135<T suffices, and the constant
in the prime equation below becomes S+107.

## 3. A polynomially thin set of close-phase offsets

Let T tend to infinity, T<=sqrt R, K<T, B,S>=0 integers,
S+3B<T-2. Define C_close to be the offsets x in [R,3R)
at which two DISTINCT allowed high arrival states have tails
of gain <=B with endpoint times differing by <=S.
The arrivals have positive multiplier and d_a<=2KT as in
section 2. These are offsets, not exact phase states.

By (2) the two incoming high primes p,r are distinct and
their multipliers a,b satisfy

    ap-br=c, |c|<=S+3B+3, c!=0.                       (3)

The bound follows by subtracting the two endpoint deficits
2t_i-x, the two delta values and the two side constants.
If c=0, distinct p,r>=T>K would force p|b and r|a,
impossible. For each a,b,c, choosing p in [T,KT]
determines r, so trivially there are O((K+1)T) candidate
pairs. No prime-pair lower bound or even an upper sieve on
the pairs is needed here. For each pair, the two tail gains
E,F in [0,B] and two arrival sides give congruences

    x=E+e_p mod p, x=F+e_r mod r, e_p,e_r in {0,-2}.

CRT fixes one residue mod pr. Since pr>=T^2 and T<=sqrt R,
there are O(R/T^2) possibilities in the slab. Summing yields

    |C_close| << K^2(K+1)(B+1)^2(S+3B+4) R/T.         (4)

This counts all hypothetical arrival states and actual short
tails at once. It does not assume canonical origin or any
bound on the number of medium events. In particular for
K=T^o(1), B=S=floor(T^theta), fixed 0<theta<1/3,

    |C_close| <= R T^(-(1-3theta)+o(1)).

For fixed K, theta=1/4 gives O_K(R/T^1/4).
Even the case S=0 (exact state collision) is included.
For the fixed <=11 alphabet, use E<=104 and |c|<=S+107
in the same count.

The polynomial saving is for offsets of close predecessor
phases, not for all possible mergers at one outgoing event.
It cannot be multiplied by an assumed independent clock
probability.

## 4. All phase fibers: a quantitative branching charge

At any x outside C_close, consider any one actual next
event with firing n, and distinct allowed last high arrival
states that can reach x through the permitted tails and
then fire that SAME event. Their pre-times are distinct
and separated by at least S+1. Sort the associated waits
w_i=n-t_i increasingly. If there are N such candidates,
(1) gives

    N <= 1+floor((ell-1)/(S+1)) <= 1+2q(x)/(S+1),
    sum_i w_i >= N+(S+1)N(N-1)/2.                    (5)

In particular at most one of those candidates can have
wait <=S+1. This is an exact inverse uniqueness result for
short-wait transitions, even when the source has a large
least neighbor factor. Also, if ell<=S+1 the WHOLE fiber
has at most one allowed last high arrival. The previous
arrival determines its exact pre-time by replaying the
tail, so no additional phase choice is required for this
compressed edge.

For a positive-stratum destination of a high event in the
corridor d<=2KT, the high label and hence its source offset
are unique by section 1. Thus outside close offsets the
graph of transitions from positive high arrivals through
gain-bounded tails to the next positive high arrival,
retaining only final waits <=S+1, has indegree at most one.
Its outdegree is at most one by determinism (the next high
event must be the first one after the previous arrival,
since B<T-1). It is a disjoint collection of directed chains,
with no merging between distinct retained high states.
This does not exclude entry from histories with no such
previous high arrival, or mergers via longer tails, higher
deficits, zero strata, or larger waits. In particular it
does not yet bound the mass of origins entering these chains.

There is a useful complementary estimate for fibers with
N>=2 at good offsets. Then ell>=S+2, hence q(x)>S/2, and
at least one prior high label r in [T,KT] divides x-E
or x-E+2 for some E in [0,B]. Take S=floor(T^eta),
0<eta<1 fixed, K=T^o(1). For fixed r,E,side, sieve the
progression x=r m+E+e_r for roughness of x-1,x+1.
The multiplier interval has length O(R/r+1) and can be
padded to length comparable to R/r >= T/K. Every odd
sieve prime l<=T^min(eta/2,1/20), for large T, is <q
and is coprime to r. The two forbidden roots are distinct.
The inherited two-form Selberg sieve with translated-
interval error O(z_sieve^6) yields O(R/(r log^2 T))
offsets uniformly; the error is absorbed by the main
term since R/r>=T/K. By Chebyshev, summing reciprocals of
primes in [T,KT] gives O(log(2K)/log T). Thus

    |C_far| << (B+1) log(2K) R/log^3 T,               (6)

where C_far counts offsets with multiple last-high
candidates in some actual fiber and outside C_close.
The direct roughness sieve also gives O(R/log^2 T),
irrespective of B. Use the minimum of the two bounds.
For B growing polynomially in T, (6) alone does not give
a saving; the latter roughness bound still does.

In particular for B=exp(o(loglog T)), K=(loglog T)^A
(fixed A>0), and S=floor(T^eta), the union C_all of
offsets with any multiple allowed last-high candidates
in a single fiber satisfies

    |C_all| <= R/(log T)^(3-o(1)).                   (7)

Here the close part (4) is polynomially small, and (6)
gives the logarithmic saving on the far part. This controls
ALL outgoing labels and phases at such offsets, not only
fast selected events. The conclusion concerns ambiguity
between different previous high arrival states, not
every possible ordinary phase predecessor.

## 5. Longer initial-prefix exclusion and a simpler degree-tail proof

We can transfer the bounds to actual starting offsets using
the compressed reverse ancestry graph of 10382d8 and b884352.
Use fixed low alphabet {3,5,7,11} with gain cap Q=104.
Every prefix with at most k events of label >11 and any
number of small events, with non-low arrivals of inverse
degree <=L, has at most

    A_k(L)=(k+1)(Q+1)^(k+1) max(1,L)^k

starting offsets per endpoint, by compressing the small
runs. This is an offset-only relaxation; phases not needed.
For close offsets take T>=R^epsilon, B=S=T^theta as above,
K polyloglog. With uniform L=O(log R) and
k=floor((1-3theta-delta)log T/loglog R), fixed delta>0
and 3theta+delta<1, the number of starting offsets
in [R,2R) reaching C_close in any such prefix wholly
in [R,3R) is <=R T^(-delta+o(1)). This allows
arbitrary gain-bounded medium tails at the endpoint
and much longer prefixes than the original first-
significant theorem, but only excludes the close part.

For ALL fiber ambiguity we use a logarithmic degree
cutoff. Suppose all prefix labels are <=P=T^O(1) and
T->infinity, T<=sqrt R. (E.g. a prefix wholly inside a
local crossing of width O(T polyloglog T) has such a
bound, as long as an exiting overshoot is not included.)
Let z=loglog T, j=ceil(C z) for a sufficiently large
fixed C, L=2j-2. Let omega_P(n) count distinct prime
factors <=P, so the restricted inverse degree at U
is <=omega_P(U)+omega_P(U+2). The following simpler
weighted degree tail dispenses with the two cases of
the previous proof. For N0=ceil(3R+2), exactly expand
the binomial and count multiples on the ENTIRE
interval [1,N0]:

    sum_(n<=N0) binom(omega_P(n),j)
       = sum_(p1<...<pj<=P) floor(N0/(p1...pj))
       <= N0 (sum_(p<=P)1/p)^j/j!.

There is no additive P^j error: even products exceeding
N0 have zero count, and floor(N0/d)<=N0/d.
On a bad inverse arrival at least one of the two omega
counts is >=j. Since n<=j binom(n,j) for n>=j, the
sum of bad degrees is at most a constant times j times
the above binomial moment. The prime reciprocal sum
is <=z+O(1). Choosing C large gives

    sum_(bad U) deg_P(U) << R exp(-10z).

Apply first-bad stopping, charging the bad arrival degree
once and all preceding non-low arrivals at degree <=L.
Bad-degree origins are bounded by A_k(L) times this
sum, regardless of subsequent coalescence.

For k=floor((3-delta) z/log z), fixed 0<delta<3,
log A_k(L)<=(3-delta+o(1))z, because Q is fixed and
log L=log z+O(1). Equations (7) and the first-bad
bound show that o(R) starting offsets can reach ANY
C_all offset during these prefixes. Quantitatively
the exceptional density is <=exp(-(delta-o(1))z).
For polynomially growing B the direct roughness bound
instead supports k=floor((2-delta)z/log z), 0<delta<2.

The same improved degree-tail argument applies to
the earlier first-significant rough-source count
O(R/log^2 T), with fixed Q: one may now take
k=floor((2-delta)z/log z) total non-low predecessors
with labels <=P=T^O(1), rather than the sqrt(z)
medium budget and O(sqrt(z)) total prefix budget
of b884352. This assertion is about actual prefixes
satisfying the stated total-count/label bound,
not about first significant events after arbitrary
medium-dense histories. It does not require assuming
a good degree for every path. The first-bad stopping
avoids a multiplicative worst-degree loss.

These deductions provide a restartable local
phase-fiber estimate, and extend the offset-only
ancestry budget for this particular obstruction.
They do NOT give a bound on ancestry with arbitrarily
many non-low events, or bound the aggregate mass
entering a chain via medium events. Even a chain with
no new internal mergers can transport a large cohort
already assembled earlier. Controlling that cohort
and the tails with physical gain >B remains open.

## 6. Executed independent diagnostics

(1) research/min_local_phase_fiber_spacing_audit.mjs,
commit aedb03608837b9aa1bca6eac03dd8b5927351cab,
blob f8a8c960233f1731e50829a18fce92de747a5a59.
Five controls (R,T,K,S):
(100000,251,6,24),(100000,503,6,48),
(1000000,503,6,64),(1000000,997,6,100),
(100000,503,60,64).
Relaxed high arrivals with p in [T,2T], exact arrival
congruences/envelope, 1<=a<=K; restricted <=11
relay endpoints retained for 198<d<=2KT. This permits
some initial d_a slightly larger than 2KT and excludes
others; the tested pair bounds follow from the exact
signed small-relay interval rather than the general
section 2 corridor. This is a finite arithmetic control,
not a test of an asymptotic density constant.

956,517 candidate arrivals; 2,797,402 relay endpoint
incidences; 195,520 close pairs (13,160 equal times,
182,360 different times); 71,924 close offsets summed
over controls. 2,663,069 exact next-event fibers,
57,906 multiple, 13,379 multiple fibers at good
offsets. 1,621,325 short-wait uniqueness controls and
38,718 separation checks. 6,009,273 literal GCD clock
ticks, including a long gap at a relaxed twin source.
The relaxed graph includes twins, so its largest gap
is NOT a claimed non-twin gap. 50,000 canonical
root/parameter incidences, 1,097,837 actual ordinary
events stopped before twins or local exit, 3,354
covered endpoints. No actual same-outgoing-event
collision of distinct prior high states in these
limited canonical controls. This is not a universal
absence claim.

(2) research/min_local_gain_bounded_relay_audit.mjs,
commit 11ee367d17e1267ec8323ab7663660c75194022f,
blob 28fcc148c37960192a2152b4ca27e4a3aecbcb51.
Four controls (R,T,K,B,S):
(100000,251,6,32,24),(100000,503,6,64,48),
(1000000,503,6,64,48),(1000000,997,6,128,100).
Relaxed arrivals p in [T,2T], 1<=a<=K,
d_a<=2KT. Follow the ACTUAL unrestricted MIN from
each arrival as long as total tail gain <=B.
No fixed small alphabet for these tails.

    R       T    B  arrivals  tail events  p>11 in tail  close pairs
    100000  251  32    22765       77197          8241       5963
    100000  503  64    19666       97347         15806       9750
    1000000 503  64   196666      979464        157385     106918
    1000000 997 128   184103     1319961        265158     213522

Total 423,200 arrivals; 2,473,969 tail events,
446,590 with label >11; 2,897,169 endpoint incidences.
336,153 close-pair linear relations checked, 49,948
equal-time pairs, 286,205 distinct-time pairs;
46,303 ambiguous exact endpoints, 137,184 close
offsets summed over controls. 1,477,596 short-fiber
controls, 16,179 far multiple fibers, 13,335 exact
positive high arrival label uniqueness checks.
370 literal unrestricted tail ticks. Maximum observed
tail length 28 events, max count of p>11 in a tail 6.
Example of actual unrestricted tails from RELAXED
high arrival states: (1000330,500764,p=599,a=1)
and (1000334,500777,p=607,a=1) both reach
(1000360,500800); each tail has 5 events, one
with p>11. Both incoming main events need not have
canonical reset-origin ancestry. Example far fiber
at x=1000080, n=502428,p=281,q=281,ell=562:
waits 6,318 from two distinct prior high arrivals,
outside the finite close set for T997,B128,S100.
This demonstrates that a short wait on one history
does NOT imply a short complete fiber or absence of
long-wait alternative histories.

40,000 independent canonical root/parameter
incidences, 900,171 actual ordinary events before
twin/exit, 4,825 retained endpoints covered by the
relaxed enumeration, 1,483 with an intervening
p>11. No distinct-prior actual merge found within
these bounded controls; all assertions passed.
Finite controls narrower than the analytic label
range and not a test of asymptotic exponents.

Both sources executed as ECMAScript in the research
runtime, committed, fetched at exact commit, and
re-executed with identical counts. No Node process
or Lean process invoked. Reproduction:
node research/min_local_phase_fiber_spacing_audit.mjs
node research/min_local_gain_bounded_relay_audit.mjs

## 7. Next concrete obstruction

The pre-time of a high arrival is not generally unique,
but short final waits and gain-bounded prior tails now
have a controlled inverse graph. The full ambiguity
offsets are also rare with a bounded logarithmic
ancestry budget. Unlike a fixed alphabet analysis,
this permits numerous intermediate events in short
physical spans. To obtain a twin-infinitude proof,
one still needs to bound the flow of roots through
longer medium tails and the incoming mass at high
chain entrances (or establish a favorable unbounded
root family by a separate construction). An entropy
argument that only charges new mergers cannot bound
already large stable cohorts. No estimate of total
medium-dense wait o(D), no favorable unbounded reset
supply, and no change to canonical Lean targets or
sibling branches.
