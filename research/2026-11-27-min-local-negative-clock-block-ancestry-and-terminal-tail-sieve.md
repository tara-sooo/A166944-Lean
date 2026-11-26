# Negative MIN: exact clock-block ancestry and terminal-tail sieve

2026-11-27 JST. Continuation of 83647a1337b68088a5c9f59a788586705ff13d41.
Replace the spatial ancestor supergraph by an exact reverse forest of
stationary clock blocks, with gain/height pruning, then obtain extra
logarithmic savings for non-twin endpoints preceded by a fixed number
of mesoscopic marked primes, even if marked labels repeat. Apply the
previous walk-moment bounds to the remaining prefix. No unrestricted
bad-basin energy bound, low-gain population lower bound, twin proof,
Lean verification, or claim of literature priority.

## 1. Physical domain and clock blocks

As in 83647a1 take H=4 floor(sqrt(R)/(log R)^B),
fixed B>0, L=floor(H/4), canonical A in [R,2R]
divisible by six, initial h=3. Use first POST-tick
height H and full gain <=L for success.
Given a prospective endpoint a0, all ancestors
have a in [a0,Amax], Amax=min(2R,a0+L).
All positions are even; for large R they and their
neighbors are positive, physical absolute times
n=h-a/2 are negative on the height domain [0,H].
The height bound is on the processed state, not
the pre-firing height.

At fixed a let C(a) contain (p,c) for odd prime
p|a+1, c=0, and odd prime p|a-1, c=p+2.
The clock is eligible at absolute ticks n=c mod2p.
For a state at height u define

    d(a,u)=max(0, max_(p,c in C(a))
               [u-((u-a/2-c) mod 2p)]).

This is the last possible clock at that position
on or before u, or zero if all such clocks are
negative in height. The reverse idle ancestry
of (a,u) consists exactly of the interval
[d(a,u),u]. A clock at its left endpoint is
allowed: an incoming jump may arrive after the
tick at which a resident root would have left.
It cannot be crossed backwards by an idle edge.
For all intermediate reverse states u<=H-1.

A canonical birth at A=a contributes one root
precisely when a in [R,2R], 6|a, and
d(a,u)<=3<=u. Birth is after the tick; it is
not erased by a clock at height 3.

To enumerate all nonidentity incoming edges,
choose p|a (minus) or p|a-2 (plus), p odd prime.
The previous position is b=a+p-1, so restrict
b<=Amax. For each arrival height h in
[d(a,u),u], the required absolute time is
n=h-a/2 and the pre-firing height at b is

    t=h+(p-1)/2.

The clock condition at n is n=0 mod2p (minus)
or n=p+2 mod2p (plus). Require t<=H, and test
that p is the least eligible prime at b at tick n
by factoring b+/-1. If accepted, the predecessor
is (b,t-1) at absolute time n-1. Its height is
nonnegative and <=H-1. The outgoing clock at b
is exactly at t, so its preceding block ends
at t-1. This is an exhaustive inverse rule.

Starting from (a0,H), the resulting clock-block
tree has no duplicate blocks: each full block
has exactly one next firing and destination,
and the endpoint block is truncated at H.
Two distinct reverse paths from a block to that
endpoint would contradict deterministic forward
dynamics. Spatial position strictly increases
along nonidentity reverse edges, so the bounded
domain is acyclic. Roots cannot be counted twice.
Conversely each root reaching the endpoint
under the specified budget and without an
earlier processed height H traces this inverse
tree. Thus the enumeration is exact, including
when no canonical birth reaches the endpoint.
If a clock at height H exists at a0, no incoming
jump there can satisfy t<=H, and there is no
idle passage from H-1; the tree correctly has
zero births for H>3.

An exact offset generating polynomial can also
be computed. At block (a,u) include 1 if it
contains a canonical birth, and for each accepted
incoming edge add z^(p-1) times the predecessor
block polynomial. Its exponent records root
distance minus a. Use the global bound Amax
throughout. At (a0,H), evaluation at z=1 gives
the basin mass m_a0; the coefficient of z^g
is zero or one, identifying the unique possible
root a0+g. The energy is the sum of squares of
the values at one across selected endpoints.
This gives an all-depth exact counting rule,
not a bound on its asymptotic values.

## 2. Gain-budget pruning and local temporal indegree

For any actual incoming event into a along a
successful canonical trajectory to a0, gain
already spent is G<=Amax-a. The mod-30 potential
gives the post-arrival height h<=11+7G/4.
The universal event barrier of 676c259 also
gives G >= 18t/35-10, t the pre-firing height.
Thus reject any incoming candidate with

    h > 11+7(Amax-a)/4
    or 18t > 35(Amax-a+10).                      (1)

Both are necessary inequalities on a genuine
ancestor, including if its earlier path has
arbitrarily many events. They remove branches
without requiring bounds on event depth or
assuming anything about the endpoint being twin.
A block with d(a,u)>11+7(Amax-a)/4 is entirely
unproductive: it contains neither an admissible
arrival nor a canonical birth. This is a local
empty-ancestry certificate.

The temporal window also bounds the unpruned
indegree before testing priority. Write
q(a)=min(P^-(a-1),P^-(a+1)). Since the q(a)
clock recurs every 2q(a) ticks,

    u-d(a,u) < 2q(a).

For any fixed incoming label p there are
at most 1+floor((u-d)/(2p)) clock opportunities
in the interval, so the total number of
candidate branches is at most

    sum_(odd p|a or p|a-2)
              (1+floor((u-d)/(2p))).             (2)

The same bound with u replaced by the smaller
of u and floor(11+7(Amax-a)/4) applies after
the arrival-height pruning, or zero if this
is below d. In particular incoming p>=q(a)
has at most one opportunity in the whole block.
At a fixed arrival height h there is only one
clock side, determined by absolute-time parity.
The minus labels divide gcd(a,h), and the plus
labels divide gcd(a-2,h-3), in addition to
the full clock congruence and priority.
Except at heights 0 and 3, candidate factors
are therefore constrained by the small height
itself. At a reset height the corresponding
gcd constraint degenerates. These exact
bounds improve the spatial-only ancestor rule
but do not give a uniform polylogarithmic
bound on total basin mass.

## 3. Terminal marked-prime words and an additional sieve saving

Fix a small-prime alphabet P0, e.g. {3,5},
with complete spatial wall maximum half-gap M
from 0116e3e. A contiguous run using only P0
has full gain in {0,2,...,2(M-1)}. In the
example M=9. Fix k>=1 and theta>0 with

    k theta < 1/2,

and let Y=R^theta. Consider successful roots
whose last k events OUTSIDE P0 have labels in
[Y,2Y); the low-only runs after and between
these marks may be arbitrary, subject to their
wall bound. The earlier prefix has no restriction
on its labels for now. Record the suffix from
the source of the earliest of the k marked
events through the final endpoint a. In reverse
order write p_1,...,p_k, and low-run gains
d_1,...,d_k, each in {0,2,...,2(M-1)}.
Record c_i=0 for a minus arrival, 2 for a plus
arrival. Define

    s_i = sum_(j<=i) d_j + sum_(j<i)(p_j-1).

The raw arrival at the i-th reversed mark is
a+s_i; the spatial congruence is

    a+s_i = c_i mod p_i.                        (3)

Let P be the product of DISTINCT marked labels.
For a fixed compatible word these congruences
pin a to one class modulo P. The suffix start
is b=a+sum_i(d_i+p_i-1). This suffix description
retains only spatial conditions, hence provides
a necessary condition and an upper count of
the actual clock-compatible suffixes.

Suppose a is a non-twin endpoint. As in d9f6049
and 83647a1 both neighbors are K-rough with
K comparable to sqrt(R)/(log R)^B. For large R
one of them equals q r with q<=r primes and
K<q<=sqrt(2R+1). Write a+e=q r, e in {-1,1}.
The other side q r-2e is K-rough. Since
p_i<=2Y=o(K), q is different from every p_i.
Thus (3) pins r to one class modulo P. The
integer parameter on this progression ranges
over an interval of length O(X), where

    X=R/(q P) >> R^epsilon

for some fixed epsilon>0, because k theta<1/2.
The two linear forms r and q r-2e have distinct
zero classes for odd primes not dividing q P.
Sift on primes <=R^eta for sufficiently small
fixed eta>0 depending on theta and epsilon.
All these primes are below q, all p_i, r and K,
so no excluded local degeneracies occur and
each form must survive. The standard
dimension-two upper sieve (same input and
CRT remainder as d9f6049) with level sqrt X,
error O(sqrt X log X), yields uniformly

    # a for fixed q,e,word
                << R/(q P log^2 R).             (4)

The implicit constant can depend on the fixed
parameters. The contribution from r itself
prime is handled by this upper sieve, not by
assuming a lower bound for any prime pair.

If all p_i distinct, summing 1/P over ordered
prime labels in the band is at most

    (sum_(Y<=p<2Y) 1/p)^k << 1/log^k R.

The q reciprocal sum is O_B(loglog R/log R).
The choices of low-run gains and sides number
at most (2M)^k, a fixed constant. Thus there are

    O(R loglog R/log^(3+k) R)                   (5)

pairs (a,terminal word) for non-twin endpoints.
This includes all admissible histories with such
a suffix, not merely histories of total depth k.
At this stage distinctness of the labels was
assumed; the next section removes it.

## 4. Repeated labels also satisfy the saving

For two adjacent reversed marks carrying the
same p, the difference between their raw
arrivals is p-1+d, with d even, 0<=d<=2(M-1).
Both raw arrival residues are in {0,2} mod p.
Consequently -1+d must be congruent to a
difference in {-2,0,2}. For p sufficiently
large compared with M, these bounded numbers
would have to be equal, impossible by parity.
So consecutive equal marked primes cannot occur.

Fix any pattern of equality among k marks that
has ell<k distinct labels. Choose two occurrences
i<j of a repeated p with no p between them.
There is another distinct intervening label r.
Subtract (3) at i and j. After fixing all other
distinct labels, the differences in (3) give

    m r + C = 0 mod p,                           (6)

where 1<=m<=k counts r occurrences between the
two repeated p marks. Since p>k, this determines
one residue of r modulo p. In a common band
[Y,2Y) with p>=Y, at most two integer choices
of r remain. No primality estimate for those
choices is needed. The congruence is necessary,
not sufficient, even if (3) for another repeat
imposes further restrictions.

There are O_k(pi(2Y)^(ell-1)) assignments of
the remaining free prime values and O(1) choices
for r in each. Since P>=Y^ell,

    sum_(compatible repeated words) 1/P
          <<_(k,M) 1/(Y log^(ell-1) R).

This has a polynomial saving in Y and is
o(log^(-k) R) for fixed theta,k. The finite
number of equality patterns and low-run/side
choices are absorbed. Applying (4) proves
(5) WITHOUT distinctness of marked labels.
In fact the repeated-label contribution to
(5) is lower order. The common-band hypothesis
is used for the constant choices in (6).
For all-distinct labels, the same argument
in section 3 allows separate polynomial
constant-ratio bands as long as their product
scale is below R^(1/2-epsilon).
No claim for arbitrary growing k or for
all labels up to the square-root band.

## 5. Transfer to the remaining prefix: longer depth range

Let U be the set of possible suffix starts b
from the pairs counted in (5), so

    |U| << R loglog R/log^(3+k) R.

Every a has at most O_(k,M,theta)(1) such
terminal words: reverse choose each d, then
p>=Y dividing one of two integers of size
O(R), at most O_theta(1) choices. The same
holds at each b in the forward direction:
choose a marked label from the two neighbors'
large factors, then a low-run displacement.
Thus the suffix relation has bounded
multiplicity at both ends (on word pairs,
not on root incidences).

Restrict the remaining prefix to at most d
ordinary events, or at most d macro steps
with a fixed low alphabet as in 83647a1.
Let F_d(b) be the corresponding spatial
walk majorant from that note, which is
independent of absolute time. Each prefix
root starting in the slab and reaching b
injects into such a walk. For j=1,2, the
bounded multiplicities and Holder give

    sum_(bad a) m_a^j << sum_(b in U) F_d(b)^j,

where m_a counts only roots satisfying this
suffix and prefix restriction. For fixed
q>=2 use the previous restricted moment
inequality and the degree bound:

    N_bad,tail(d)
       << |U|^(1-1/q) R^(1/q)
                     [C(loglog R+dq)]^d,

    C_bad,tail(d)
       << |U|^(1-2/q) R^(2/q)
                     [C(loglog R+dq)]^(2d).

Constants may depend on k,M,theta,B,q;
for a fixed macro alphabet its wall gap
is absorbed in C. If

    d <= kappa loglog R/logloglog R,

then the exponents of log R in these
two bounds (apart from R) are respectively

    kappa-(3+k)+(3+k)/q+o(1),
    2 kappa-(3+k)+2(3+k)/q+o(1).

Choosing q large and fixed proves:

* For kappa<3+k, N_bad,tail(d)=o(R).
* For kappa<(5+k)/2,
  C_bad,tail(d)=o(R log^2 R).

Thus every marked terminal event supplies
one further logarithmic saving in the
support count, extending the allowable
PREFIX depth coefficient for the mass
bound by one and for the energy bound
by one half. E.g. k=3, theta=1/10
gives the mass threshold kappa<6
and energy threshold kappa<4, rather
than 3 and 5/2. This example concerns
only roots with the specified three
last non-low marks. Repeated labels
are covered by section 4.
The suffix itself has bounded macro
length, so its addition to the depth
is negligible at this scale.

A gain-based version requires no depth
restriction on the prefix: if its gain
is <=J, each suffix start b has at most
floor(J/6)+1 canonical prefix roots.
The same bounded multiplicity argument
gives

    N_bad,tail << (J+1) R loglog R/log^(3+k) R,
    C_bad,tail << (J+1)^2 R loglog R/log^(3+k) R.

For J<=log^nu R, fixed nu<3+k gives
o(R) bad mass; nu<(5+k)/2 gives
o(R log^2 R) bad energy. This is an
all-event-depth estimate within a
prefix gain restriction, not an
unrestricted prefix bound.

The missing step is a covering or
distribution theorem for successful
roots guaranteeing the required suffix
structure and prefix depth or gain.
The estimates do not apply to all
successful trajectories. The exact
clock-block rule of sections 1-2 may
help study the remainder but does not
itself furnish a global energy estimate.

## 6. Executed finite audit

Source research/min_local_negative_bad_basin_clock_blocks_audit.mjs,
commit f3e8b67e0261e939c3ca75e9b185484357a18851,
blob 7a7b4fba4b6aa58fc5ca3bc1ac72e17b0931110a.
Executed in ECMAScript research runtime,
fetched at exact commit and re-executed
with identical output. Reproduce with node.
No separate Node or Lean invocation.

Six slabs R=3000,12000,48000,192000,480000,
1000000, H=4 floor(sqrt(R)/sqrt(log R)),
L=floor(H/4). All canonical roots, ordinary
forward event enumeration to first passage
or budget stop. Reverse all actually reached
non-twin endpoints, a deterministic sample
of reached twin endpoints, and 374 sampled
rough non-twin endpoints with no successful
root. For each compare the actual root list
with both the plain exact reverse forest and
the gain-pruned reverse forest. All match.

    roots                             289172
    completed events                 2541188
    successes                         100550
    endpoint controls                   1667
    empty endpoint controls              374
    exact root-list comparisons         3334
    plain block nodes                5155850
    plain candidate branches         5495380
    plain priority rejections         336970
    plain preheight rejections          4227
    pruned block nodes               1543204
    pruned candidate branches        1923753
    pruned priority rejections        100879
    pruned preheight rejections         1157
    pruned budget rejections          280180
    no-duplicate block checks        6699054

The overall visited block reduction is about
70.1 percent. All comparisons use full
individual root lists, not merely mass totals.
For R=1000000, 867 reverse controls,
3631578 plain nodes, 1079251 pruned nodes,
largest plain reverse tree 19158 blocks,
largest actual basin among these controls
40 roots. Dead branches are numerous;
the node reduction is an algorithmic
improvement, not a proof of small basin mass.

For suffix controls use P0={3,5}, M=9, several
fixed finite bands [Y,2Y), initially distinct
marks of lengths k=1,2,3. Check low-run caps,
raw-arrival congruences, reverse degree envelope,
and support counts. Independently enumerate
all residues in small CRT products (<=15000)
for selected bad suffixes with composite-side
factor q distinct from marked p. Check the
two forbidden residues in the residual
progression and their finite interval error.

    distinct-label suffix incidences   162535
    distinct suffix keys (incidences
       across slab/band/depth controls) 37667
    raw arrival congruence checks      452217
    suffix multiplicity checks          31259
    independent complete CRT controls    3000
    two-form CRT remainder checks       12070

Repeated-label controls: Y=19,23,31,47,
k=2,3,4,5, all six slabs, now allow repeats.
All repeated-mark congruences, absence of
adjacent repeats, intervening-label residue
and number of integer choices verified.

    repeated-label controls               96
    repeated-label root incidences       156
    of these non-twin incidences            7
    repeated congruence checks           188
    intervening residue checks           188
    constant-choice tests                188

For R=1000000, band [17,34), k=1,2,3
with distinct labels:
bad success root counts 956,202,25;
bad endpoint counts 168,41,5;
bad suffix-start counts 191,44,6.
These are finite overlapping controls
and not an asymptotic test of (5).
The fixed finite bands are not the
polynomial Y=R^theta range used by
the asymptotic proof. The script's
first attempted repeated-control
extension used a mismatched source
replacement and did not produce the
new controls; it was corrected before
the final commit and successful readback.

## 7. Status

The exact reverse clock-block forest works
without a depth cutoff and provides strong
gain-based pruning. The new arithmetic
tail-sieve bound gives an extra log saving
per terminal marked prime, including
repeats, and extends the previous
depth-truncated mass and energy estimates
for a specified subclass. We have not
bounded the full long-path non-twin mass
or C_bad=O(R log^2 R), nor proved a
positive-density low-gain success
population at near-square-root height.
No twin-infinitude proof, Lean verification,
or canonical Lean target/sibling changes.
