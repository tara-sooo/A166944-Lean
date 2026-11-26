# Negative MIN: static frontier equivalence and missed-clock barriers

2026-11-27 JST. Continuation of 676c25981b8da5d374989b8f5e7298d572452fc6.
Investigate whether the generation of distinct low-gain endpoints
below the final height-doubling barrier can provide a substantial
new set beyond static rough centers. The result is a structural
limitation of that route, a sharper small-budget equivalence,
and a quantitative asymptotic for distinct endpoints at subpower
height. It does not provide the missing near-square-root lower
bound or a proof of twin infinitude.

## 1. Exact stationary clock spectrum

Write x=a/2, h=x+n. For an eligible odd prime p,
the minus side means p|a+1 and n=0 mod 2p,
and the plus side means p|a-1 and n=p+2 mod 2p.
Thus for a fixed distance the possible heights of
that clock are one residue class modulo 2p:

    minus: (s p - 1)/2 mod 2p,
    plus:  (s p + 5)/2 mod 2p,

where s=1 if x=(p-1)/2 mod2, otherwise s=3.
Indeed these are the two lifts of the required
height residue modulo p; their parities differ,
and n has the required even or odd parity.
Call s=1 short and s=3 long. For p>=11 these
representatives are the first positive heights
and exceed 3 (also exceed 6 for sufficiently
large p). At small primes choose the first
representative strictly above the starting
height 3 by adding multiples of 2p. For
canonical distances a divisible by 6, p=3 is
ineligible. Denote by d_3(a) the first
stationary clock height strictly after 3
over all eligible primes. Equivalently

    d_3(a)=3+w(a,3-a/2).

This is a spatial function, independent of the
history that brought a root to that position.
For sufficiently large H the set of even a
with both neighbor least factors >2H+1 is
contained in {a : d_3(a)>H}, which is in turn
contained in the rough set with both factors
>(2H-5)/3. For the latter inclusion, any
eligible p with representative above 3 and
p<=(2H-5)/3 has an opportunity at or before H;
the finitely many smaller p whose representative
is <=3 have their next opportunity at bounded
height and cannot occur in a large-H stationary
survivor. Roughness makes a divisible by six
once the cutoff exceeds 3. Statements about
static canonical roots below are on that
progression.

## 2. Dynamic-only endpoint and the missed-clock barrier

Start a physical seed of height h0 in {3,6},
distance A in [R,2R], 6|A. For the first
POST-tick height H passage within gain budget
L, let a be the endpoint, G=A-a<=L,
and h_arr the height of its preceding event
arrival, or h0 if no event. The last interval
is idle. The previous mod-30 potential gives

    h_arr <= h0 + 7G/4 + 8 <= 14 + 7G/4,
    I = H-h_arr >= H-14-7G/4.                   (1)

Assume L<=lambda H for fixed lambda<4/7,
H tending to infinity and H<=C sqrt R.
Then all factors of a+/-1 are >I/2>=c_lambda H
for a fixed c_lambda>0 and large H.
In particular a is divisible by six, and
the short/long representatives above all
exceed both seed heights.

Suppose d_3(a)<=H, so this endpoint could NOT
have reached H by stationary waiting from
its own canonical seed. Call this a dynamic-only
endpoint (not merely an endpoint reached by
a positive-gain path). Some eligible prime q
has a first clock at height d<=H. Because the
final segment (h_arr,H] is idle, necessarily
d<=h_arr; equality is allowed because the
incoming jump arrives AFTER the tick. As
d >= (q-1)/2, we have q<=2h_arr+1.
The next opportunity after h_arr occurs
within 2q ticks, so

    H < h_arr+2q <= 5h_arr+2 <=72+35G/4.

Consequently every dynamic-only endpoint costs

    G > (4/35)(H-72).                            (2)

This is valid uniformly for both seed phases,
including an arbitrary genuine restart seed
of the types in 5b148fe. In particular for
L <= (4/35)(H-72), every successful endpoint
is a zero-gain stationary survivor from its
own canonical seed. It may lie slightly below
the chosen slab, so exact set equality should
either enlarge the static interval by L or
restrict to endpoints within the slab.

There is a further short/long refinement for
lambda<2/7: for large H (1) gives h_arr<H/2,
and 2q>I>h_arr for all eligible q.
Thus at most one clock opportunity of a given
q could have been missed before arrival.
For every missed q,

    d <= h_arr < H < d+2q.

Writing d=(s q+c_e)/2, c_e=-1 or 5,
the eligible missed primes satisfy

    (2H-c_e)/(s+4) < q <= (2h_arr-c_e)/s.        (3)

For short clocks this gives q> (2H-5)/5,
q<=2h_arr+1. For long clocks it gives
q>(2H-5)/7, q<=(2h_arr+1)/3, and

    H < (7h_arr+2)/3,
    G > (12/49)H - 10.                          (4)

The latter constant is deliberately rounded
down. In particular for fixed lambda<12/49
only short clocks may be missed, once H is
large. They have the prescribed mod-four
class in section 1. At the budget H/4,
long-clock misses are arithmetically possible
only in a narrow band, asymptotically
q/H in (2/7,7/24]. This is a necessary
condition, not existence of such misses.
The audit found no long-clock misses.

## 3. Uniform static frontier equivalence

Let J=[R,2R], and let E(H,L) be the set of
distinct endpoints of canonical roots in J
reaching H within budget L. Include all
canonical roots, not merely a selected
subpopulation. Use H<=C sqrt R and
0<=L<=lambda H, fixed lambda<4/7.
Every stationary canonical survivor in J
is included (gain zero). Every endpoint is
in J^-=[R-L,2R] and c_lambda H-rough by (1).
The static survivor set S_H on J consists
of d_3(a)>H, and is sandwiched between
the rough sets at cutoffs 2H+1 and
(2H-5)/3. Therefore, ignoring the O(H)
boundary states, both E and S_H contain
the (2H+1)-rough set and are contained in
a c H-rough set for a common fixed c>0.

For a rough center in the difference of
these two rough sets, some neighbor is
p m with c H<p<=2H+1 a prime. For fixed
p and side, sift m and p m +/-2 at cutoff
H^epsilon with fixed sufficiently small
epsilon. Both avoid primes below that
cutoff, and each odd sifting prime has
two distinct forbidden residues because
p is outside the cutoff. The parameter
interval has length O(R/p), and m is of
scale R/p. The usual dimension-two
upper sieve gives O(R/(p log^2 H)) values.
This is uniform since R/p >> H, with
level sqrt(R/p) and summed remainder
O(sqrt(R/p) log(R/p)); see the identical
CRT and sieve argument in 676c259 and
d9f6049. Chebyshev's bound gives
sum_(cH<p<=2H+1) 1/p << 1/log H.
Consequently the whole difference has size
O(R/log^3 H). The boundary error O(H)
is absorbed in this bound for H<=C sqrt R.

Let Q_H be the ordinary set of even
a in J with both least prime factors
>H. The symmetric-difference statement is

    |E(H,L) symmetric_difference Q_H|
                  <<_(lambda,C) R/log^3 H,      (5)
    |E(H,L) symmetric_difference S_H|
                  <<_(lambda,C) R/log^3 H.      (6)

The lower inclusions use the full canonical
family. For an arbitrary selected subset,
or phase-6-only roots, the upper estimate
on endpoints outside S_H still holds, but
the symmetric-difference lower inclusion
need not hold. If the full canonical family
is included along with phase-6 roots,
(5)-(6) remain valid.

For dynamic-only endpoints one can also
derive (6) directly from (3): each has a
missed prime in a constant-ratio band,
and the same rough-neighbor upper sieve
applies. In particular if lambda=4/35+o(1),
then (4) rules out long misses, and (3)
confines each short missed prime to
q/H=2/5+o(1). The ordinary prime number
theorem implies o(H/log H) primes in
this shrinking relative band (first
bound by any fixed enclosing relative
interval and then let its width tend
to zero). The per-prime bound above
is O(R/(H log^2 H)), uniformly.
Hence in this regime the count of
dynamic-only endpoints is even

    o(R/log^3 H).                             (7)

The statement concerns missed-clock
exceptions; boundary states, if counted
as additional dynamic endpoints outside
the slab, number O(H)=o(R/log^3 H).
No assumption of uniformity of the
adaptive trajectories is used. The
standard sieve input is the one used
in 74a6796 and later notes; no new
lower sieve at polynomial near-square-root
cutoffs is invoked.

## 4. Actual asymptotic at subpower height

As a consequence of (5), there is a precise
asymptotic for distinct first-height endpoints
on the actual physical slab, in the range
H->infinity and log H=o(log R). For the
ordinary rough set Q_H, write a=6j and sieve
the two prohibited residues per prime p>=5
up to H. N=R/6+O(1). The standard fundamental
lemma used in 74a6796, with level sqrt N,
gives

    |Q_H|=(1+o(1)) (R/6) V(H),
    V(H)=prod_(5<=p<=H)(1-2/p).

Indeed s=log(sqrt N)/log H tends to infinity,
and the summed remainder O(sqrt N log N)
is o(N/log^2 H). By Mertens,

    V(H) ~ C*/log^2 H,
    C*=9 exp(-2 gamma) prod_(p>=5)
                    (1-1/(p-1)^2)>0.

The factor 9 removes primes 2 and 3 from
the squared Mertens product. Inserting
(5) gives uniformly for 0<=L<=lambda H

    |E(H,L)| ~ (C*/6) R/log^2 H.               (8)

This counts actual distinct endpoints, not
formal CRT-period representatives and not
root incidences. It shows that in this
range any fixed low-gain budget changes
the leading endpoint count by zero.
It gives no similar asymptotic for the
multiplicity of each endpoint or the
total number of successful roots.
For fixed sufficiently small polynomial
exponents the lower sieve gives a
constant-factor two-sided estimate,
rather than the relative asymptotic (8).
No extension to larger polynomial
exponents is claimed.

## 5. Square-root witness with a shorter height

Let S=sqrt(2R+1) and H=ceil(3S/2+3).
A non-twin a in J^- has some least
neighbor factor q<=S. Its short or long
stationary representative is at most
(3q+5)/2, hence <=H. For small q
whose representative is <=3, the next
opportunity is still at bounded height.
Thus S_H consists exactly of twin centers
at this H for large R: a twin center's
eligible labels are a-1,a+1, whose first
clock heights are of order R and exceed H.

By (2), every successful first passage with

    G <= (4/35)(H-72)

at this reduced height is a twin endpoint,
even without the full 4S height of 5b148fe.
In particular any unbounded family with
G/H bounded strictly below 4/35 at
H=ceil(3S/2+3) suffices. Conversely
infinitely many twins give zero-gain
canonical witnesses here, so the criterion
is equivalent to twin infinitude.
For general H=cS, fixed c>3/2, combine
(2) with the usual non-twin bound
I<2S and (1). The strict asymptotic
sufficient ratio is

    G/H < max(4/35,(4/7)(1-2/c)),

with fixed margin. This complements the
previous 2/7 ratio at c=4. It is a tradeoff,
not an improvement of every parameter.
No actual asymptotic small-gain sequence
at any of these heights is obtained.

## 6. Consequence at the near-square-root frontier

Set H comparable to sqrt R/(log R)^B,
fixed B>0, still with a fixed lambda<4/7.
Every actual twin center in J is a
zero-gain survivor for sufficiently large R.
Every non-twin endpoint is c_lambda H-rough
by (1). By the half-prime exception argument
of d9f6049, K=c_lambda H, the count of these
non-twin centers is O(R loglog R/log^3 R).
Writing pi_2(J) for the number of twin
centers in J,

    |E(H,L)| = pi_2(J)
                 + O_(lambda,B)(R loglog R/log^3 R). (9)

Here the possible boundary twins in
[R-L,R) contribute O(H) and are absorbed.
At H=c sqrt R for any fixed c>0, the
same argument with a constant-ratio
least-factor band gives the smaller
error O(R/log^3 R), or an empty
non-twin exception if the cutoff
already exceeds S.

In particular the previously proposed
distinct-state target
|E(H,L)|=omega(R loglog R/log^3 R)
requires a twin count of that order
already. This statement is stronger
than mere twin infinitude. The lower
bound on E is not obtained from (9).
The near-square-root dynamic-only
endpoint count O(R/log^3 R) in (6)
is even smaller than the full
non-twin rough exception scale.

This establishes a limitation of the
attempt to create many NEW distinct
rough states by low-gain evolution:
the full canonical seed family already
contains almost the same stationary
frontier. Repeated state generation
cannot supply an additional leading-order
endpoint population in the subpower
range, and at the near-square-root
scale its extra contribution is below
the sufficient target. This does not
rule out a dynamical proof via
successful root MASS, multiplicity,
or a single low-gain witness. For
example, a large successful root
population together with sufficiently
small conditional collision energy
would force many stationary survivors
by (6) and Cauchy-Schwarz. It would
derive the necessary static lower
bound indirectly, not assume it.
Such a mass/energy estimate remains
unproved.

There is a useful mass form of the
dynamic-only bound. If successful
root multiplicities are m_a and
C_s=sum m_a^2, then at most

    O(sqrt(C_s R/log^3 H))

successful roots lie on dynamic-only
endpoints, by (6) and Cauchy-Schwarz.
For a near-square-root cohort with
N_s>>R and C_s=O(R log^2 R), this
is o(R). The non-twin exception mass
has the previously derived upper
bound O(sqrt(C_s R loglog R/log^3 R)).
These estimates refer to the selected
successful cohort, not all roots.
They are conditional transfer bounds,
not an energy upper bound.

## 7. Executed audit

Source research/min_local_negative_static_frontier_equivalence_audit.mjs
commit c9a1a3f870adb51c6ab78a874f9204d2ca2d994a,
blob 5ccc7d876e4f7cd4f0fe9b5cf8c50db45651db3b.
Executed in ECMAScript research runtime,
fetched at the exact commit and independently
re-executed with identical output.
Reproduce with node on this source.
No separate Node or Lean process invoked.

Four slabs R=12000,48000,192000,480000;
multiple heights including 64,128,256,
4 floor(sqrt R/sqrt(log R)),
ceil(3S/2+3), ceil(2S), ceil(4S).
All canonical distances in each slab,
both initial heights 3 and 6 (the
phase-6 sample is the full extended
seed family, not only actual reset
descendants). Stop at gain budget
floor(H/4) if the next event would
exceed it. Compare independent
factorization-based next-event rule
and explicit stationary clock heights,
enumerate distinct first-passage
endpoints, static survivors, and
missed-clock types. All assertions
passed.

    root/height/phase controls        1708056
    completed events                 13637420
    explicit clock congruence checks  3639452
    static next-clock comparisons      854828
    first passages                     661758
    gain-budget stops                 1046298
    small-budget static checks         416040
    missed-clock incidence checks         878
    single-missed-clock band checks       878
    short misses                         878
    long misses                            0
    static rough sandwich checks        854028
    reduced-height twin witness checks 251777
    4S twin witness checks              157929

All counts are incidences across
controls, not distinct roots or
distinct twins. The long-miss branch
of (4) had no observed examples in
these controls; its proof is the
explicit clock inequality, not an
empirical bound. For example at
R=480000, using the standard phase-3
family only:

    H       static in J    all distinct E(H,H/4)   dynamic-only
    64          10497             10613                116
    128          7912              7954                 42
    256          5916              5927                 11
    764          3747              3749                  1
    1473         3473              3474                  0
    1960         3473              3474                  0
    3920         3473              3476                  0

The discrepancies in the last three
rows are static-eligible boundary
states below R, not missed clocks.
At H=764 there is one boundary
state in addition to the one
dynamic-only endpoint. For the
small budget floor((4/35)(H-72))
(with zero used for negative
finite budgets), all endpoints
were static eligible, allowing
boundary states. The displayed
H=64 small budget is zero.
No inference of asymptotic
near-square-root lower bounds
from these finite data.

## 8. Remaining research direction

The new finding (5)-(6) closes the
gap between distinct low-gain
first-passage endpoints and a
static rough frontier at leading
order in the controlled lower-sieve
range. At near-square-root height
(9) shows the main distinct-state
goal effectively requires a lower
bound on twin abundance. The
dynamical advantage, if any, must
come from proving gain/mass
estimates or a single witness,
not from an extra leading-order
set of low-gain states absent
from the static family. The
reduced-height criterion gives
a second tradeoff for such a
witness. No square-root asymptotic
gain saving, near-square-root
lower-sieve breakthrough, twin
infinitude proof, Lean verification,
or canonical Lean target/sibling
branch changes.
