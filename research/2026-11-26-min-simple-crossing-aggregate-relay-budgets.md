# Aggregate relay budgets without lower-label enumeration

2026-11-26 JST. Continuation of 4d195219051f02b9a36f07a971e542a30c94e73e.
The earlier sparse-interruption theorem counts lower occurrences and
equality patterns. Here they are not counted at all: retain only the
total displacement between successive high events. This yields two
unconditional bounds on actual wait, valid for arbitrarily repeated
low labels and independent of their support. The bounds have a
different domain from the earlier sparse-count theorem; neither
contains the other. No full stable-wait bound or twin proof.

## 1. Compressed high prefix and aggregate gain

Use the same common-boundary system, M=R/12+O(1) reset origins,
X in [R,3R/2], 6|X, state (X,X/2+3), stop at first U_exit>=2R.
Only non-twin waits are counted. On any path w<=2min(p,q(u)),
total gain <3R. Let T be dyadic, tending to infinity, and put

    l=log T, m=log log T,
    A=T/l^2, U=T l^2, W0=T/l^2,
    h=ceil(16 l/log(2m)),  2 U^h<=sqrt R.                 (1)

The room condition is eventually satisfied uniformly for
T<=exp((log R)^(1/3)). There is no small-prime cutoff z in
the theorem. An anchor is a non-twin event of label in
[T,2T) and wait >=W0. List successive high events, defined
by label >=A, starting at the anchor. Stop at the first repeated
high label or the h-th distinct high label, whichever occurs
first. Require this stopping event to exist and all retained
high labels to be <=U. If the path ends before either
stopping condition, the prefix is not counted.

Let n be the number of distinct high labels of this prefix.
It has n+1 high events in the repeated case and n=h high
events in the all-distinct case. If x_i is its i-th high
source, let

    E_i=x_(i+1)-x_i-(p_i-1)
       =sum of gains of ALL intervening lower events;
    G=sum_i E_i.

These are nonnegative even integers. Impose G<=n B, where
B>=1 is a function of T and h B+3<A. No assumption on the
number, size distribution, support, clocks, or repeat
patterns of those lower events is made. An individual E_i
may be much larger than B if the other gains are small.
This includes lower-event labels below any earlier cutoff z
and all preempted low runs.

For fixed n the number of candidate gain vectors of length
<=n (length fixed by whether repeat occurs) is at most

    binom(floor(n B)+n,n) <= (e(B+1))^n.                 (2)

Indeed pad by one zero in the distinct case, then apply stars
and bars and n! >= (n/e)^n. Evenness is unnecessary for
this upper count, though it is needed in the exclusion of
consecutive repeated labels. Crucially (2) does not grow
with the number of lower events in the path. We have not
assumed these gain vectors occur in actual MIN; counting
all possible gain vectors is an upper bound.

## 2. Source sieve using one or two long waits

For a fixed high label tuple, orientations e_i in {-1,1},
and gain vector E, all relative source offsets are fixed:
    x_i=x_0+sum_(j<i)(p_j-1+E_j), x_i=e_i mod p_i.
Distinct high labels impose at most one source class modulo
2P, P their product; repeats impose compatibility.
By (1), 2P<=sqrt R. This CRT does NOT include any of the
lower prime labels. Each actual path visits an anchor offset
at most once, so source-offset counts bound actual anchor
occurrences on that path.

The anchor wait implies x_0+-1 have no odd prime factor
less than W0/2. The inherited explicit two-form Selberg
upper sieve (record-displacement-and-supply, section 3)
on the source progression, using primes up to floor(T^(1/40)),
gives
    count per tuple << R/(P l^2).                         (3)
All high prime factors of P exceed the sieve cutoff. The
parameter interval has length comparable to R/P>=sqrt R,
so the O(T^(3/20)) remainder is absorbed.

If the SECOND high event also has wait >=W0, write
D=x_1-x_0=p_0-1+E_0. Its neighboring integers supply two
additional rough forms. The four shifts -1,1,D-1,D+1 are
distinct since D>=A-1>2. Their difference product is
nonzero and O((U+hB)^6), hence <=T^C for fixed C. Omit
the odd primes <=5 and those dividing the difference
product, to retain four distinct roots in each modulus.
The same explicit Selberg upper sieve with g(ell)=4/ell
on remaining primes gives
    count per tuple << R m^4/(P l^4).                    (4)
In detail the squarefree counting error is O(rho(d))
with rho(d)<=d and |lambda_d|<=d for ell>=7. The
sieve remainder is O(T^(3/20)) as before. The complete
Euler product has order l^4, and the omitted factors
cost O(m^4) by the prime-divisor-product estimate
proved in the mixed-window note: for 1<=|N|<=T^C,
prod_(ell|N)(1-1/ell)^(-1)<<log log T. The local
O(ell^-2) corrections give a bounded factor, and the
same mean-log-index truncation of the Euler product
gives the Selberg denominator. No roughness of any
subsequent high event is needed. Bound (4) is uniform
in the high tuple and the gain vector, even when D
depends on an as-yet unspecified high prime. It is
applied after all prime values are fixed.

## 3. First high repeat, now with arbitrary low words

A consecutive high-label repeat p_i=p_(i+1)=p would require
p to divide 1+e_(i+1)-e_i-E_i, a nonzero odd integer
of absolute value <=h B+3<A<=p. Hence it is impossible.
Thus in a repeated prefix n>=2. At the first repeat
p_n=p_i, i<=n-2, the endpoint congruence gives
    p_(n-1)=a p_i+c,
    c=n-i+e_n-e_i-sum_(j=i)^(n-1) E_j
                     -sum_(j=i+1)^(n-2) p_j.
Here p_(n-1) and p_i are distinct, c!=0, and
1<=a<=C h U/A. Positivity follows from the interior
high-prime sum (at least (n-i-1)A) plus the relay
gains minus n-i+e_n-e_i. The upper bound follows
from total high gains <=h U and G<=h B. Fix i,
orientations, the gain vector and all other high primes;
then c is fixed and |c|=O(h(U+B)). The harmonic
coefficient sieve of the first-repeat-prefix note applies
without modification:
    sum_a sum_(p,q in [A,U], q=ap+c, p!=q) 1/(pq)
        << m^4/(A l^2).                                 (5)
When the repeated p is the anchor, its band [T,2T)
improves the denominator A to T: in the proof sum
1/s over dyadic p bins is O(1/T) instead of O(1/A).
For clarity (5) follows from subdividing p~s,q~t;
the two prime forms lie in an interval for p of length
<=min(s,t/a), which is enlarged to comparable length
if shorter. The two-form upper sieve omitting primes
dividing ac gives count O(min(s,t/a)m^2/l^2). Divide
by st and sum 1/a, dyadic t bins, and the geometric
sum 1/s. All lengths are >=T/polylog(T), and the
coefficients are polynomial in T, so the remainder
and singular-product bounds are uniform. This counts
prime pairs on fixed c, then (3) or (4) counts sources
for the resulting tuple. It does not assume
independent probabilities of clock selections.

## 4. Two all-depth wait bounds

Let S_H=sum_(A<=p<=U)1/p<<m/l (Chebyshev on dyadic bins).
Define D_B=C(B+1), absorbing orientations and (2)
with a fixed absolute C. For any B with hB+3<A and
D_B S_H->0, the count of all-distinct prefixes is
    << R/l^2 * (D_B S_H)^h.
This counts high labels only, not intervening low
primes, by applying (3) and summing the reciprocals
of the h distinct high labels. Weight by anchor
wait <=4T. We use this bound even in the two-long-
wait class.

For a first repeat, combine (2), (3), (5), and the
harmonic sum for the n-2 other high labels. The
choice of i costs <=n; allow n^2 for convenience.
After weighting by 4T, repeated-anchor case (i=0)
is bounded at fixed n>=2 by
    << R n^2 D_B^n m^4/l^4 * S_H^(n-2).
Nonanchor repeated p (i>0) requires n>=3, and the
same bound gains a factor T/A=l^2. Summing these
geometric tails, starting at n=2 and 3 respectively,
and adding the distinct case gives
    W_1(T,B) << R T/l^2 * (D_B S_H)^h
         + R (B+1)^2 m^4/l^4
         + R (B+1)^3 m^5/l^3.                           (6)
Constants absolute for sufficiently large T with
D_B S_H small enough. For W_2, which requires the
second high event to have wait >=W0, replace (3)
by (4) in the two repeated-prefix estimates. Thus
    W_2(T,B) << R T/l^2 * (D_B S_H)^h
         + R (B+1)^2 m^8/l^6
         + R (B+1)^3 m^9/l^5.                           (7)
These are actual anchor-wait upper bounds for arbitrary
single trajectories, not hypothesized bounds on a
random word. Because each source is counted once, no
factor h for overlapping return subwords is needed.

Choose
    B_1=floor(l^(2/3)/m^4), B_2=floor(l/m^4).
Both tend to infinity, satisfy hB+3<A, and have
D_B S_H->0. With h as in (1) the distinct term is
O(R/T^2) in both cases: even for B_2 the base is
O(m^-3), and its h-th power is T^(-48+o(1)).
Substituting into (6),(7) yields
    W_1(T,B_1) << R/(l m^7),
    W_2(T,B_2) << R/l^2.                                 (8)

The first series is summable over dyadic T>=T0->infinity:
sum 1/(l m^7)<<1/(log log T0)^6 by the integral test.
The second sums to O(1/log T0). Summing over M origins,
    W_(aggregate budget B_1) << R^2/(log log T0)^6,
    W_(aggregate budget B_2, two long waits)
                             << R^2/log T0.
Both are o(R^2). They include arbitrary masses and all
depths. Compared with the previous sparse-count result,
there is no count of low occurrences at all; for example
a prefix may include nB_1/2 successive gain-2 events
subject to legality and the actual gain condition. This
is an allowance in the theorem, not an assertion that
such a long all-3 sequence is legal. Conversely a prefix
with very few but individually large low gains may satisfy
the earlier theorem and not this one.

## 5. What this leaves

The prior upper-interruption charge applies to the forward
h-high window and also covers a >U interruption before
the new stopping point; terminal prefixes without a
repeat or h distinct high events are covered by the old
missing-window charge. The earlier long-physical-relay
charge G_low>=T l^3 across a full h-high window remains
valid and can be combined with (8). For the other
eligible anchors, the new exclusions cover G<=nB_1,
and when the second high wait >=W0 also G<=nB_2.
They can overlap the previous sparse-occurrence exclusions;
do not add finite populations as if disjoint.

A large count of lower events with modest gain is now
handled whenever its aggregate gain meets the respective
budget. However a relay gain between these logarithmic
budgets and T l^3 can be substantial, and no bound on
its total anchor wait is proved. In particular neither
(2) nor the primorial barrier guarantees such a budget
for actual high-to-high relays. The second-high wait
condition is an additional restriction for the larger
budget, not a consequence of anchor roughness.
The product-room restriction also still excludes
polynomial scales. The count of possible displacements
in (2) deliberately ignores detailed clock constraints;
a stronger estimate for the distribution of these
displacements could be the next avenue. No proof of
W=o(R^2), E=O(R^2), or twin infinitude follows.

## 6. Executed audit

Source research/min_simple_relay_budget_audit.py at
bcac840329e4ce589cdeaa44e835c3faf332c26c, Git blob
8cebd3ece335a6a87f3b7ce5f9bda4819f7b6e35.
Exact remote readback matches locally executed git hash.
Self-contained Python stdlib:
    python research/min_simple_relay_budget_audit.py 1000 10000 100000 1000000

Diagnostic h=4, A=T/4,U=8T,W0=max(7,T//8), budgets
8,16,32,64,128. Require a full h-high window and observed
G+3<A in accepted prefixes (rather than asymptotic
hB+3<A); the proof covers some prefixes without a full
window as well. Count ALL low events in the gain and in
the diagnostic many-lower flag (count>2+floor(n/4)).
This count includes labels <=3 and so is NOT the exact
same flag as the earlier sparse-interruption audit,
which counts only labels >3. No claim of set inclusion
between the two finite diagnostics is made.
Independent SPF and modular clocks, literal tick GCD
checks at R<=10000, actual origin replay all four sizes.
Checked exact gain compression, high-only CRT including
first repeat, endpoint linear relation, stars-and-bars
bound, individual-relay-vs-total budget, and four
distinct source forms with their good-prime roots.

R=10^6: 83334 origins, 294268 states, 2564511 non-twin
visits, total wait 66822800. Diagnostic eligible anchors
233398, anchor wait 49479900; 89414 full no-upper
windows, anchor wait 16673277. 5167 distinct prefix
tuples in the full diagnostic.

    B   accepted   accepted wait   low repeats  many lower  two rough
    8       9247       1439336          6020        3561       6824
    16     10682       1942990          7454        4995       7874
    32     11788       2494993          8558        6101       8727
    64     12069       2581279          8839        6382       9008
    128    12069       2581279          8839        6382       9008

At B=8, 2918 accepted prefixes have some E_i>B; the
aggregate budget is genuinely exercised. A concrete
example X=1000194 has high labels (157,269,53,673),
gains (6,14,8), eight low occurrences using three distinct
low labels, anchor wait 24; G=28<=4*8, despite E_1=14>8.
At B=64, 449 first high repeats, two-rough wait 1835540.
At R=100000, B=8 accepted 372, B=32 accepted 425
(including one first high repeat); at R=10000, 10
accepted. No anchors at R=1000 under the diagnostic
cutoff. All checks passed. Fixed diagnostic parameters
do not test the asymptotic growing h, log-budget
conditions, or analytic sieve constants. No Lean run.
