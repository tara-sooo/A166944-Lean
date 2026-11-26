# Growing short-relay words and arrival-rank capacity

2026-11-26 JST. Continuation of 5aef6a4ed635b40666a045663f4fa439ce74243d.
Goal: control actual long stable transport, not just fixed-order moments
or a prescribed small prime support. New paper deductions and two
executed audits. No proof of residual W=o(R^2), twin infinitude or
Lean verification.

## 1. Uniform growing-word theorem, including repetitions

Use the common-boundary MIN: seeds X in [R,3R/2], 6|X, reset
(X,X/2+3), stop on the first event reaching U>=2R. M=R/12+O(1).
The pre-offsets are strictly increasing. On non-twin sources
q(u)=min(lpf(u-1),lpf(u+1)), and wait w<=2q<=2sqrt(2R+1),
also w<=2p for selected prime label p. The total gain of a path
is <3R. All waits counted below exclude twin events.

Fix a dyadic band [T,2T), T growing, and mark any subset of
non-twin events in this band whose wait is >=T/log T.
Consider consecutive marked events with intervening physical
gain E_i (even nonnegative). A short h-word has h marked events
with every one of its h-1 relays <=B. No condition on distinct
label count is imposed. Let W_word(T) count the waits of the
FIRST events of all short h-words on a single path in the slab.
Use parameters

    B=floor((log T)^(1/4)),
    h=ceil(8 log T/log log T),
    (2T)^h <= sqrt R.

For T sufficiently large, uniformly in the path,

    W_word(T) << R/(log T)^(3/2).                          (1)

The source offset is counted at most once per path even if many
different paths or phases can realize the same candidate word.
Thus (1) has no dependence on seed mass, phase, or total history.

### Proof: common offset progression and roughness

Write labels p_i, orientations e_i in {-1,1}, pre-offsets
x_i=x_0+sum_(k<i)(p_k-1+E_k). Eligibility requires
x_i=e_i mod p_i. For each distinct label the first occurrence
fixes x_0 mod that label; repetitions impose additional
compatibility. If P is the product of the distinct labels,
the consistent source class is one residue modulo 2P (x even).
Here P<=(2T)^h<=sqrt R. The source is rough: all odd factors
of x_0+-1 are >=T/(2log T), because the mark has wait >=T/log T.
Parametrize the class as x_0=a+2P n in an interval of length
O(R/P), enlarging to comparable length if needed. For sieve
primes 3<=ell<=floor(T^(1/10)), ell<T and ell does not divide P;
the two forms a+2P n+-1 have distinct roots modulo ell.
The explicit two-form Selberg sieve of the inherited
record-displacement-and-supply note, section 3, gives

    O(R/(P log^2 T))

source offsets per fixed tuple. The O(T^(3/5)) error is
absorbed, since R/P>=sqrt R>=(2T)^h. Constants are independent
of word length: only TWO forms at the first source are sieved,
and all moduli in P exceed the sieve cutoff. The bound does
not treat clock probabilities as independent.

If all h labels differ, sum this estimate over orientations,
relays and ordered prime tuples. Chebyshev on [T,2T) gives
sum_p 1/p << 1/log T. Hence distinct-word source count is

    << R/log^2 T * (C(B+1)/log T)^h.

Multiplying by 4T bounds first-event wait. With the stated
h and B the power is T^(-6+o(1)), so this contribution
is O(R/T^2), more than sufficient for (1).

### Proof: a shortest repeated subword

If a word contains a repetition, choose a pair of equal
labels at minimum separation j<h. The subword is
p_0,p_1,...,p_(j-1),p_0 with all first j labels distinct.
The congruence at its two ends gives exactly

    p_1+...+p_(j-1) = a p_0 + j + e_j-e_0 - sum_(i<j) E_i,

where a is an integer of absolute value <=3j for large T.
The case j=1 is impossible: the right-hand constant
1+e_1-e_0-E_0 is odd nonzero with absolute value <p_0,
because E_0<=B<T-3 and E_0 is even.

Fix j>=2, orientations, relays and a. The relation determines
the final interior prime p_(j-1) from the other j-1 primes.
There are at most (C T/log T)^(j-1) free prime tuples,
regardless of whether the determined integer is prime.
Every consistent tuple has source progression with P>=T^j,
and the same two-form sieve saves log^2 T. Counting O(j)
choices of a, 2^(j+1) orientations, (B+1)^j relays, we get

    N_j << (R/T) * j (C_1(B+1))^j / log^(j+1) T.

This counts possible source offsets with multiplicity of
compatible tuples, hence upper bounds actual minimal returns
on a single path. Constants C,C_1 are absolute. Sum the
geometric tail for j>=2 (C_1(B+1)/log T -> 0):

    sum_(2<=j<h) N_j << (R/T) (B+1)^2/log^3 T.

Each return occurrence belongs to at most h short h-windows
of the marked sequence. Thus the total first-event wait of
the windows containing repeats is

    << R h (B+1)^2/log^3 T << R/(log T)^(3/2).

Together with the distinct case this proves (1). This uses
the minimal return relation at arbitrary depth up to h,
not just the p,r,p relation of the preceding paper.

### All origins, all eligible scales

For instance the product condition holds uniformly for
T0(R)<=T<=exp((log R)^(1/3)), T0->infinity, and also
T<=exp(0.1 sqrt(log R log log R)) for sufficiently large R.
In the latter range h log(2T) <= (0.16+o(1))log R
at the endpoint; monotonicity for sufficiently large T
gives the inequality throughout. The scale condition itself
is the operative hypothesis, not an assumption about data.

Summing (1) over dyadic T>=T0 satisfying the product condition
and over M origins yields

    W_all_short_long_words << R^2/sqrt(log T0)=o(R^2).      (2)

Counting per origin allows arbitrary prior and subsequent
mergers. It is therefore a bound on actual all-depth stable
traffic as well. No support-size assumption is needed.

For one band let G be total intervening physical gain
between consecutive marked events. Split the marked sequence
at relays E>B. The number of runs is <=1+G/(B+1).
Every mark except the final h-1 in each run starts a short
h-word. Therefore

    W_marked(T) << R/log^(3/2) T + T h (1+G/(B+1)).        (3)

Non-twin events with p in bands T>=T0 but w<T/log T
have total wait O(R/log T0) per path by the gain budget.
Equation (3) is an unconditional support-free estimate at
the indicated scales, but its relay term need not be small.
For example a macroscopic marked wait in one such band
requires G >> R(B+1)/(T h) for large R, since T h=o(R).
No bound making that true relay gain impossible is proved.
The relay gains for different bands may overlap, so they
cannot simply be summed as disjoint physical costs.
The product condition fails at polynomial scales T=R^eps
for growing h; the earlier fixed-length sieves do not fix
this limitation. No assertion that all residual waits are
covered by (2).

## 2. Divisor budget for an entire arrival-rank spectrum

For an actual event (u,v)->(U,V) with label p, even firing
gives p|U and p|V; odd firing gives p|(U+2) and p|(V-2).
For integers A,K define the adjusted arrival rank

    Z_{A,K}(U,V)=A U-K V+2(A+K) 1_(V odd).

Thus p|Z_{A,K} always. For A=1,K=2 this is
-(2V-U-6*1_(V odd)); the adjusted deficit is divisible
by 2p because it is even. Call an arrival rank-singular
if Z=0. For fixed rank, K!=0, at most two singular times
are possible at any fixed U (one for each parity).
Unlike a nonzero rank value, zero imposes no bound on the
incoming prime divisor.

Partition each exact heavy chain into blocks of width
D=ceil(R^(3/4)), as in the local-label-diversity note.
In one chain-block piece choose any integer coefficients
A,K (possibly fitted after inspecting that piece) and any
subset of its non-twin events with p>=T and Z!=0. Let
mathcal D be the set of distinct nonzero Z values of these
events and L_D=log rad(product_(Z in mathcal D) |Z|),
with empty product 1. All their selected labels divide
the product. Consequently

    sum_(distinct selected p) 1/log^2 p
        <= (sum_(distinct selected p) log p)/log^3 T
        <= L_D/log^3 T.

The uniform local single-label capacity (previous paper)
now gives, for the UNWEIGHTED waits on the chosen part
of the piece,

    W_{p>=T,Z!=0} << D L_D/log^3 T.                       (4)

This is a phase/label correlation estimate independent
of the mass. In particular if |A|,|K|<=R^c for fixed c,
then |Z|<<R^(c+1) by the time envelope even at exit.
For fixed eps>0 and T=R^eps, a spectrum of at most O(log R)
distinct nonzero arrival values has L_D=O(log^2 R), and (4)
is O(D/log R). More generally the radical budget alone
suffices; the values can be numerous with shared divisors.
For example an affine rank strip A U-K V in an interval
of width O(log R) has this property, excluding Z=0.

Every origin visits <=ceil(R/D)+1+log_2 M heavy-chain
pieces, by the all-depth light-arrival budget. Sum (4)
over origins for any collection of pieces or subsets
having L_D=O(log^2 R), to obtain actual origin-weighted

    W_{nonzero rank,sparse spectrum,p>=R^eps}
        =O(R^2/log R).

Coefficients may be chosen per piece for this estimate.
On a piece with nonzero high-label wait >=eta D one
necessarily has L_D>>eta log^3 T, and for polynomial
T and polynomially bounded coefficients, Omega(log^2 R)
distinct nonzero rank values. This is a lower bound on
phase diversity, not just selected-prime diversity.
It does not bound the singular rank events or all low labels.

## 3. Dual capacity on arrival phases, arbitrary prior phase width

Define ambient incoming wait supply
    C_R=2 sum_(even R<=u<2R,non-twin) q(u) omega((u-1)(u+1)).
By the earlier three-log H_1 bound, C_R<<R^(3/2)/log^3 R:
for q<=R^(1/3) the contribution is O(R^(4/3)log R);
otherwise each neighbor has at most three distinct prime
factors for large R, so use 12 H_1. This is an ambient
source-offset sum, not a mass estimate.

Choose arbitrary sets J_U of arrival times, at most K0
times for each arrival offset U, including exact exit
states. The choices can depend on the entire graph.
Let m_y be the maximum non-twin incoming wait of each
reachable target y=(U,V), V in J_U. Then

    sum_y m_y <= K0 C_R.

Indeed for every possible source offset u and prime label
p|u+-1 the destination offset is fixed U=u+p-1, allowing
at most K0 selected target times and wait <=2q(u). Taking
a maximum over incoming states for each y is bounded by
summing these candidate contributions. Distinct phases
at one source are NOT counted separately for the same
destination, since the maximum, not total wait, is used.

Let b(s) count exact-state origins, and include the total
mass of all incoming origins at each terminal exit state.
For an edge from b(s)<=H to b(y)>H, every contributing
origin crosses the mass threshold at most once over
its whole path. Such non-twin waits cost <=2M sqrt(2R+1).
For the other selected incoming edges at each y, their
source masses are disjoint and sum to <=b(y)<=H.
Thus total ACTUAL wait on selected arrivals whose SOURCE
mass is <=H satisfies

    W_arrival <= H K0 C_R + 2M sqrt(2R+1).                (5)

If the destination itself has b(y)<=H, the threshold
term is unnecessary. This holds at all generations and
without a narrow source-time band. The previous slot
capacity was source-based; (5) is a destination bound.

For any single rank with K!=0 choose its two singular
arrival phases at each U (K0=2). With H=sqrt R log^2 R,

    W_{Z=0,b(source)<=H}=O(R^2/log R).

In particular arrivals returning to d=0 at even V
or d=6 at odd V are controlled for all modest source
cohorts even if they originated far from a reset phase.
A common per-offset phase-count cap is required in (5);
one cannot take arbitrary per-piece singular ranks and
sum (5) without controlling their union. Large source
mass singular arrivals still need an independent bound.

## 4. Exact singular-return excursion identity

Use the special rank A=1,K=2 and call the arrival
singular when d=2V-U equals 0 (even V) or 6 (odd V).
Both singular types have U divisible by 4.
For a nonsingular even arrival, d is a nonzero multiple
of 2p, hence d>=6. For a nonsingular odd arrival with
d<6, the only possible negative nonzero multiple
d-6 of 2p is -6: necessarily p=3,d=0. The update
d_new=d_pre+2w-(p-1), with d_pre>=0,w>=1, then
forces d_pre=0,w=1. Thus a nonsingular run starting
at d=6 stays at d>=6. A run starting at d=0
trivially stays at d>=0. Include the initial seed
as a starting reset (d=6, either parity).

Split an origin's non-twin path at every singular
arrival. Denote its total nonsingular waits by W_n,
nonsingular physical gains by G_n. Every nonsingular
relay (including the final tail) starts at d_0=0 or 6
and ends with d_pre>=d_0. If its gain E and wait W_e
are the sums of its constituent nonsingular events,

    E=2 W_e+d_0-d_pre <=2 W_e.
    0<=d_pre-d_0=2 W_e-E<=5E,

using W_e<=3E. Therefore, exactly and uniformly,

    G_n<=2 W_n,
    sum_(singular arrivals) (d_pre-6)_+ <=2 W_n.

If the next singular event has label p, wait w and
destination d_new in {0,6},

    |2w-(p-1)|=|d_new-d_pre| <=6+5E.

In particular, for any fixed beta>0 the total waits
of singular events preceded by relay gain E>=beta p
are <=(2/beta) G_n <=(4/beta)W_n (use w<=2p).
The same bound holds for singular events with
(d_pre-6)_+>=beta p. This is a precise reduction
of a singular-dominated path to almost half-time jumps
separated by short relative relays, provided W_n is small.
If W_n is itself macroscopic, these charges are not small.
No upper bound W_n=o(R^2) over all origins is proved.

## 5. Obstruction: arbitrary long exact direct-reset chains

There are arbitrarily large legitimate d=6 seeds on
multiples of 12 with any prescribed finite length m of
consecutive d=6 -> d=6 non-twin events. All selected labels
can be distinct and exceed any prescribed fixed bound.
This is not just a locally legal non-reset ancestry word.

Choose p_i recursively prime, p_i=1 modulo
12 times the product of odd primes <=2m+2 and all earlier
p_j, with p_i>E_(i-1)+3, p_i>2m+3 and above the
prescribed bound; E_i=sum_(j<=i)(p_j-1), E_0=0.
Existence of arbitrarily large primes 1 mod a fixed
integer N is sufficient (e.g. Dirichlet, or the elementary
cyclotomic proof: a prime factor of Phi_N(A) with A
divisible by N and a prescribed finite set of primes
has order N modulo that prime and is outside that set).
Set B0=max p_i+6. Seek X divisible by 12, with
X+E_(i-1)=-1 mod p_i for each i. At an earlier
source the positive gain difference <p_i-3 ensures
the residue is not +/-1. At a later source the residue
is -2 mod p_i by the nested congruences, also safe.
For every unselected odd prime q<=B0 exclude the
at most 2m residues giving X+E_j=+/-1 mod q for j<m.
For q<=2m+2 all E_j=0 mod q, choose X=0 mod q;
for q>2m+2 at least one residue remains. CRT solves
all conditions, consistently with X divisible by 12,
on a positive-density arithmetic progression.

Take X sufficiently large in that progression. At source
u=X+E_(i-1), v=u/2+3 odd, the desired plus p_i clock
fires after w=(p_i-1)/2 (even). Indeed n-2=(u+p_i+1)/2
is divisible by p_i and n is odd. This is its first
eligible tick. All other odd primes <=B0 are excluded
from both neighbors. At relative tick j<=w the raw
defects are 2j+7 (even absolute tick) and 2j+1 (odd),
positive and <=p_i+6, so no larger prime can fire.
Therefore the intended event wins the exact first-clock
and least-label competition, and d remains 6. The
selected plus neighbor u+1 is composite once X>max p_i,
so each event is non-twin. Repeat for m events.

The construction permits arbitrarily long direct
singular histories at actual reset seeds; the labels
are fixed for each m while X varies, and no quantitative
growth with X is asserted. It does not refute (2), which
requires a growing word in one comparable band, or any
proposed asymptotic transport bound. It rules out a
uniform fixed-depth exclusion of singular direct chains.

## 6. Executed audits and persistence

Both sources use stdlib and inherited min_simple_crossing_audit.py.

- research/min_simple_long_word_audit.py, source commit
  071522751327452ac9d4e2d3f12bcf85d65fe7be, blob
  fd195c7b833351a9eb32389b6ec7dedf5d3a50e4.
  Remote exact readback; after aligning one blank line
  the local git hash matched this blob and the exact
  file was rerun at all four scales.
- research/min_simple_rank_spectrum_audit.py, source commit
  a7c05d91bf81e0dfc5055f5359881f4a72c558ae, blob
  6ed1b3841ee6c0d23b8762db072d79292b077026.
  Remote exact readback and executed source hash match.

    python research/min_simple_long_word_audit.py 1000 10000 100000 1000000
    python research/min_simple_rank_spectrum_audit.py 1000 10000 100000 1000000

Long-word audit: independent literal enumeration over two CRT
periods (four primes 11,13,17,19, modulus 92378, residue 30526);
per-origin actual clock replay; congruences for whole words,
shortest-repeat relations, per-tuple source count, at-most-h
window multiplicity, and relay-tail decomposition checked.
Finite diagnostic uses h=3,4,8 and B=min(8,(T-4)//4),
mark ceil(log T)*w>=T. These are NOT the growing asymptotic
parameters; no asymptotic sieve constant is numerically fitted.
At R=10^6, 83,334 origins, 294,268 cached states, 2,564,511
non-twin visits, wait 66,822,800, 688,487 marked visits.
142 distinct word tuples (including minimal returns).
Short 3-windows: 2639, 1490 distinct, 1149 repeated, first
wait 110300. Short 4-windows: 192, 38 distinct, 154 repeated,
one minimal-return distance 3 and 153 distance 2, first wait
3771. No short 8-window in these data. Growing h(T) and
its product-room condition are not exercised by the finite
samples. The checks test arithmetic/charging identities,
not the asymptotic theorem.

Rank audit: at R=10^6, 61,657 heavy-block pieces, H_1=7714010,
ambient C_R=57214968. Singular d=0/6 arrivals at 47,415
distinct target states, total wait 14,715,049, max-incoming
wait capacity sum 1,168,479. At H=8, small-source singular
wait 4,213,426, threshold crossing wait 2,289,068 from
25,715 origins; the positive crossing case is exercised.
At H=(floor(sqrt R)+1)*ceil(log R)^2=196196>M all source
masses qualify; no large-mass case at that cap is tested.
Arbitrary graph-dependent two highest-wait arrival phases
per offset also checked: 179,475 targets, capacity 4,002,008,
total wait 65,222,022; H=8 threshold mass 54,915 and wait
6,137,437. Divisor budgets checked for (A,K)=(1,2),(2,3),
(3,5),(5,9), with p>=31 and spectrum cutoff 14 at R=10^6.
Special rank (1,2) high nonzero wait 40,303,391, high
singular wait 13,853,596, max spectrum size 30; high
nonzero wait on sparse pieces 33,200,148.
All-origin excursion check: singular visits 346406,
nonsingular visits 2218105; W_n=52107751, G_n=50018492,
sum excess d=13007414, max relay 3960, max per-origin
G_n/W_n=2. All integer structural checks passed and
literal GCD event selection independently checked for
R=1000,10000. Non-singular other-rank test populations
are not a claim of density. The direct-reset control uses
literal GCD ticks, p=(13,61,73,109), waits (6,30,36,54),
seed 100977580137097591501605875711440060486178904528,
modulus 63220109280835215576290412583087324986549373980.
All four arrivals return to exact odd d=6 states.

## 7. What is still open

New bound (2) removes a genuinely growing-length family of
short-relay comparable long-wait transport, regardless of
support or cohort size. New (4) bounds high-label transport
with sparse nonzero arrival-rank spectra, and (5) removes
modest-mass singular arrivals without source-phase restrictions.
The excursion identities and exact long reset controls show
what remains of a singular-dominated route. None of these
eliminates large-mass singular transport or broad-spectrum
nonsingular transport with large relay/mixed-scale histories.
Polynomial-size comparable labels lie outside the growing-word
product range. A uniform upper bound on the actual residual
wait, not more fixed-depth counting, is still needed.
No full-history energy O(R^2) bound, twin-infinitude proof,
or Lean kernel verification.
