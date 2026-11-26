# Negative MIN: record-return forests, old-prime deletion dilution and first-use supply

2026-11-27 JST. Continuation of e40e4c5d6130fb77947021a8bb0911b6d52f89d9.
We resolve the exact old-label record-level transfer into a decreasing
return forest, including repeated visits and traffic rather than just
first-cut mass. The forest gives exact gain, energy and weighted-position
identities. Same-label return spacing strengthens the repeat threshold
from the preceding note. We obtain a CRT deletion inequality for the
FIRST USE of a large label at a record level even if the prime has been
available at earlier levels. This yields an unconditional formal
first-use record-gain bound across a band of large primes. The finite
tests show that most cut-energy increments are base/return cross
terms, and most of their top-label traffic is first-use rather than
repeated use. The main remaining problem is a cross-correlation bound,
below-record gain, and large-height actual-slab transfer. Paper-level
deductions, not Lean verification or a claim of literature priority.

## 1. Universal one-level return map

Use first PREheight L_b as in ddd9474 and e40e4c5d.
At position a and preheight b the absolute tick is
n=b-a/2. If a label p fires, write sigma=-1 for the
even-tick minus clock, +1 for the odd-tick plus clock.
Then p divides a-sigma, and divides 2b+1 (minus) or
2b-5 (plus). Position becomes a-p+1, postheight
h'=b-(p-1)/2>=0. The next preheight is h'+1.

For each b>=1 define F_b on all even pre-tick
positions at level b, taking the first future
preheight b+1. Include the finite congruence
extension with all primes <=2b+1. The odd
height factor can be negative at very low
heights; use its absolute prime factors.
The finite-alphabet wall guarantees that
F_b is defined, as every jump decreases the
position and the process must eventually
idle up to b+1. Preheight can increase by
at most one.

If the tick at b is idle, F_b(a)=a. Otherwise
its next return to b has source

    R_b(a) = (F_(b-1) o ... o F_(h'+1))(a-p+1),   (1)

with the composition empty if h'+1=b.
All intermediate firings have preheight <b.
This follows by successive first passage to
each of the intermediate levels, with the
correct absolute tick determined by position
and preheight. It gives a recursive
construction of the record-level return
map using only lower-level maps.

At a moving vertex a draw one directed
edge a->R_b(a), labelled (p,sigma).
Write D_e=a-R_b(a)>=p-1 for its total
gain, including all lower-height events.
Its elapsed time from pre-tick to
pre-tick is exactly D_e/2, because
both endpoints have the same preheight.
In the physical line all edges strictly
decrease position. On the period modulo
4 product_(odd q<=2b+1) q there are no
directed cycles: a cycle would imply
a positive period's displacement below
the height cap, exceeding the wall bound.
Thus every vertex reaches an idle
vertex, and the resulting terminal map
is exactly F_b. This construction
includes all old labels and repeated
visits at b; it is not a first-visit-only
or independent-resampling model.

## 2. Exact traffic, energy and spatial moment

For an actual slab use a FIXED set S of
canonical roots that all reach first
preheight H+1 within their elapsed
T=ceil(8 sqrt(2R+1)). For large R all
these paths stay in the positive
distance, negative-time physical region.
Use levels b=4,...,H. The same one-level
identities hold on the formal period,
except that the spatial moment below
uses actual lifted positions.

Let u_b(a) be the initial mass at L_b,
and v_b(a) the total visiting mass of
the record return forest, including
both first and later visits to b before
L_(b+1). Each root visits any particular
vertex at most once because return
edges decrease a. Thus

    I_b(a)=sum_(e:x->a) v_b(x),
    v_b(a)=u_b(a)+I_b(a).                         (2)

For an idle vertex, v_b(a)=u_(b+1)(a);
for a moving vertex, u_(b+1)(a)=0.
Let E_b=sum u_b^2 and define the local
nonnegative energy creation

    delta_b(a)=2 u_b(a) I_b(a)
                 + I_b(a)^2 - sum_(e:x->a) v_b(x)^2.

The first term is the base cohort
crossed with incoming cohorts. The
remaining term is the cross-product
of different incoming branches.
Each ordered distinct pair first
joins the same record-return vertex
exactly once in the transition, even
if it originally merged below that
height within an excursion.

By expanding (2) and cancelling the
squared traffic of internal edges,

    E_(b+1)-E_b = sum_a delta_b(a).                (3)

In particular no estimate of the
number of repeat visits is required
for this exact energy identity.
The squared traffic on the right
is NOT the initial moving mass
u_b(x)^2 used in a one-step exit map.

A second, gain-weighted identity on
the physical line is

    sum_(e:x->y) D_e v_b(x)^2
      = sum_a a delta_b(a)
        + sum_a a u_b(a)^2
        - sum_a a u_(b+1)(a)^2.                 (4)

Multiply the definition of delta
by a, sum over vertices, and
cancel each internal squared flow
at its two endpoints. The remaining
edge term is (x-y) v_b(x)^2.
The two boundary terms are exactly
the first-cut position moments.
Equation (4) can equally use a
common shifted coordinate a-a0.

## 3. Gain and shared suffix ledger across ALL record levels

For each root, the intervals of
return edges at successive record
levels are disjoint and partition
all completed jumps before L_(H+1).
Indeed a jump at the current record
starts an excursion below it, which
must return before the next higher
record. All lower-height jumps
during that excursion belong to
this one edge. Consequently

    sum_(b,e:x->y) D_e v_b(x)
                         = sum_(A in S) G_H(A).  (5)

Here G_H(A) is gain just BEFORE
first preheight H+1. This counts
recycled below-record gain and
does not omit any small-label
excursion.

For squared traffic expand into
ordered pairs of participating
roots. If a pair shares an edge
at level b, it shares its whole
remaining record-edge suffix
through L_(H+1). The roots must
have the same final cut. For
each ordered pair with a shared
edge let z be the source of its
FIRST shared record-return edge,
and a_final its common final
cut. Its summed shared edge
gain is z-a_final. If it shares
no edge the contribution is zero.
Thus the exact pair expansion is

    sum_(b,e:x->y) D_e v_b(x)^2
       = sum_(ordered pairs) shared_suffix_gain
       <= (2T+6) E_(H+1).                       (6)

The first common record-return
edge can precede the first
shared FIRST-PREHEIGHT cut:
a pair can merge below b and
then revisit b together.
For example the first-cut
suffix alone undercounts shared
gain for roots 3012 and 3042
in the R=3000, H=64 control:
the shared edge gain is 210,
whereas the first common
first-cut position is 2880
and the final position 2802,
giving only 78. The initial
scratch pair assertion used
this false equality; it was
corrected before committing.
All diagonal pairs obey (5).

For the high-label edge set
p>=cT, c>0 fixed, D_e>=p-1,
so (6) also gives

    sum_(b,e:p>=cT) v_b(x)^2 <<_c E_(H+1).

This is an aggregate top-band
traffic bound conditional on
the final cut energy, with
no count of return depth.

## 4. Same-label repeat and shell injection

At a fixed preheight b and
fixed sign sigma, the sources
of a label p satisfy
a=sigma mod p and a/2 parity
fixed by n=b-a/2.
They therefore form a SINGLE
class modulo 4p (within the
even positions). For p>=5
the sign itself is unique
at b, since the two height
factors differ by 6.
For p=3 keep the two signs
as distinct classes.

If a return edge starting
with p reaches another moving
vertex with the SAME p and
sign at this level, its
displacement satisfies

    D_e == 0 mod 4p, D_e>=4p,
    d_e=D_e-(p-1) >=3p+1,
    d_e == 1-p mod 4p.                          (7)

This sharpens the earlier
necessary d>=p+1 for repeated
fresh p (e40e4c5 section 2).
The stronger congruence also
holds for repeated old labels
at the same b. No assumption
on intermediate labels.

Two distinct sources in one
(p,sign) class with D_e in an
interval of width <4p cannot
return to the same vertex.
In particular all edges with

    d_e<=3p                                     (8)

are injective within their
label/sign class and cannot
immediately repeat that class.
This extends the previous
d<=p short range. More generally
every displacement shell of
width 4p (half-open) is injective
within a fixed class.

For an arbitrary return forest,
let w(t)>0 be nondecreasing
on t>=0 with C_w=sum_(j>=0)1/w(j)
finite. Let I_(p,sigma)(y) be
the total traffic arriving at
y from that label/sign class.
By source spacing, the values
D_e/(4p) among its incoming
edges are at least one apart.
Weighted Cauchy yields

    I_(p,sigma)(y)^2
       <= C_w sum_(e->y,p,sigma)
                         v_b(x)^2 w(D_e/(4p)).  (9)

Let d_b be the number of
eligible label/sign classes
in the height factor lists
(at most omega(2b+1)+
omega(abs(2b-5)), with
omega(1)=0). Summing over
destinations and using
Cauchy over the classes,

    Q_b=sum_y I_b(y)^2
       <= C_w d_b sum_e v_b(x)^2 w(D_e/(4p)).

Thus (3) implies

    Delta E_b <= 2 sqrt(E_b Q_b)+Q_b
                         - sum_(moving x) v_b(x)^2.          (10)

This extends the weighted
fresh-excursion inequality
to all old labels and returns.
It controls collision terms
without maximum fan-in, but
uses the full traffic and
does not close the recurrence
in E_b alone. For a bounded
physical horizon one may
instead take w(t)=1+t and
truncate the reciprocal sum
at floor((2T+6)/(4p))+1,
giving a factor O(log(2+T/p))
per label/sign. For top labels
this is O_c(1).

A sparse-key consequence for
short HIGH/HIGH branch collisions:
let H<=C T, p,r>=c T, p!=r,
and restrict d_e,d_f to [0,J].
For all sufficiently large R,
at any b<=H each side has
at most one such prime since
pr>2b+1. If both incoming
branches exist at b they have
opposite signs. For each b,
p,r (at most a constant number)
and each pair of even tails d,d',
their common target y satisfies

    y == sigma_p+1-d mod p,
    y == sigma_r+1-d' mod r.

The interval of possible y
has length O(R); pr comparable
to R gives O(1) possibilities.
Thus at most O_(c,C)(T(J+1)^2)
different (b,y,p,r,d,d') keys
can collide. This uses no
sieve, no mass cap, and includes
the case of tails of bounded
small-label wall gain. With
J polylog R and each incoming
branch mass polylog R their
pair contribution is o(R).
It is a count of branch keys,
not a bound on inherited mass.
The base/return term in (3)
does not require a second
incoming label and is NOT
controlled by this collision count.

## 5. Deletion dilution for FIRST use of an OLD prime

The main new observation is
that the 1/p dilution is not
restricted to the first height
at which p is available.

Fix b>=4, p>=5 with p^2>2b+1
and p dividing one of the
height factors at b. Its
sign sigma is unique at b.
Let P be all odd primes
<=2b+1 and use the old
alphabet P without p.
Let U^-(a) be the old-only
canonical mass at first
preheight b+1. Its period
L^-=4 product_(q in P,q!=p) q
is coprime to p, with
M^-=L^-/6 canonical roots.
Lift to L^- p.

Consider the FULL trajectories
whose FIRST EVER firing of
p is a record-level firing at
preheight b, meaning before
first b+1 (possibly at a
return visit to b). Up to
that tick the full and deleted
paths agree. If p wins at b,
every other prime divisor of
that tick's height factor
is smaller than p: otherwise
the factor would be >=p^2.
No smaller prime is eligible,
or p would not win.
The deleted rule therefore
idles at b and exits to b+1
at the SAME source a.

Hence the full first-use
traffic at this source,
call it v_0(a;b,p), is
bounded by U^-(a) at the
unique activated lift of
each old exit class with
correct parity and a=sigma
mod p. This is a pointwise
old-deletion certificate.
For every real r>=1,

    (1/(p M^-)) sum_a v_0(a;b,p)^r
       <= (1/p) K_r^-(b+1;sigma),              (11)

where K_r^-(b+1;sigma) is the
old-exit moment per M^- on
the appropriate clock parity.
No assumption of no earlier
negative tests for p. All
earlier p preemption conditions
can only delete some of the
roots of the activated lift.

More precisely, for each old
root trajectory to its old
exit choose the unique lift
giving the required final p
pin (provided the parity is
correct). Accept the root iff
p could NOT have beaten any
old event or fired on any
earlier idle tick. At an old
firing tick use the smaller
prime tie rule. At the target
b tick p is automatically the
winner under p^2>2b+1 and old
idle. This is an exact
characterization of the
first-use cohort by its
p-deleted prefix. It works
even if old p was introduced
long before b and even if
b is composite or is the
third clock level. Unlike a
fresh insertion, it does not
imply that the whole full
partition refines the old
partition, since earlier
p firings can change paths.

For the base-return energy
term, further restrict the
base roots at the return
target y to those that have
not used p before their
first b cut. These roots'
first b states also coincide
with their p-deleted states.
Let u_b^-(y) be that deleted
first-b mass. Write A_x for
the uniquely pinned lift of
old exit class x with the
right parity. Even if p
fires again in the following
return excursion, the full
return map R_b(A_x) is a
deterministic function of
that pinned source. Therefore
the two-sided p-unused
base cross term is bounded
by the normalized old-period
correlation

    (2/(p M^-)) sum_x U^-(x)
                         u_b^-(R_b(A_x) mod L^-).            (12)

Here the sum is over the
clock-compatible old exit
classes. This is the same
1/p factor for an old prime,
but with a correlation
between two deleted profiles,
not two independent means.
It does not cover previously
p-used base roots or
incoming traffic which has
already used p. No estimate
of the correlation sufficient
to close (10) is obtained.

## 6. Low-gain retention at early PLUS levels

There is also a lower bound
for (11) at selected old
levels. Suppose the final
sign is plus and

    b=(k p+5)/2, k=1 or 3,

with the hypotheses of
section 5. For a p-deleted
root with old exit at a and
correctly pinned lift,
assume old total gain

    G^- < 2p-2.                                (13)

Any earlier possible p
firing would be at a+d,
0<=d<=G^- even.
If its sign is minus,
a+d==-1 mod p and a==1
mod p imply d==-2 mod p;
the smallest nonnegative
even solution is 2p-2,
contradicting (13).
If its sign is plus and
d>0, the least possible
even multiple of p is
2p, again impossible.
If d=0, the same-position
plus clock repeats only
after 2p ticks, hence
after a preheight
difference of 2p. The
first possible plus
height is (p+5)/2 for
p>=5. Neither k=1 nor
k=3 leaves room for a
previous same-position
plus clock, even on
a path with repeated
height visits. At a fixed
position absolute time
and height increase
together, and previous
times are strictly earlier.

Thus all such low-gain
old roots survive the
activation certificate.
Let U^-_short be the
old-exit mass with
(13). On each activated
lift

    U^-_short(a)<=v_0(a;b,p)<=U^-(a),

so the moment (11) is
sandwiched between 1/p
times the restricted
short old moment and
1/p times the full
old moment. At the
first minus level
b=(p-1)/2 the original
fresh exact equality
holds without any gain
restriction. For k>=5
the same-position clock
exception is real; a
small old displacement
alone no longer guarantees
retention. This is why
one must not replace
(11) by unconditional
equality at all old
levels.

For comparison, if a
root has fired p>=5
before a later p
event, the two source
positions differ by
at least 2p-2. Their
difference is even,
>=p-1 (the earlier
jump), and congruent
to 0 or +/-2 mod p.
The smallest admissible
positive differences are
2p, 2p-2, 2p+2
respectively (p>=5).
Thus the pre-gain
before a repeated p
is at least 2p-2.
For p=3 this statement
fails and is not used.
At the SAME record b
and sign, (7) is
stronger. The finite
audit checks both
bounds separately.

## 7. Unconditional first-use record gain supply (formal)

Let H grow, and take
sqrt(2H+1)<Y<=2H+1.
On the formal canonical
period through cutoff
2H+1, define S_(H,Y)
to be the sum of
p-1 over record-level
firings of p>=Y that
are each the first ever
use of their own label
on that root, strictly
before first preheight
H+1. Count the triggering
jump, NOT the full
gain D_e of its return
excursion.

For each p the number
of possible preheights
b<=H is O(1+H/p),
because the minus and
plus height expressions
are 2b+1 and 2b-5.
For each such b use
(11) with r=1:
K_1^-(b+1;sigma)<=1.
The old profile
may vary with b,p but
this bound is exact
mass conservation.
The larger common
period lifts each
local calculation
without changing
normalized averages.
Therefore

    E_formal S_(H,Y)
       << sum_(Y<=p<=2H+1) (1+H/p).             (14)

In particular for fixed c>0,

    E_formal S_(H,cH) <<_c H/log H = o(H).

More generally for any
fixed B>0 and
Y=H/(log H)^B,

    E_formal S_(H,Y)
       <<_B H loglog H/log H = o(H).

The last bounds use
Chebyshev's prime-count
estimate and dyadic
reciprocal sums across
O(loglog H) bands
in the latter case.
No independence of
old-label histories,
energy conjecture or
fresh-only assumption
is required. It includes
first-use old labels at
multiple record heights,
where the earlier
fresh-only recursion
did not apply.

For actual slabs this
formal estimate transfers
by exact period counting
when H<=c0 log R with
c0 sufficiently small:
the period is O(R^u),
u<1/2, all cuts fit
the horizon by the wall,
and nonnegative root
weights give a relative
O(period/R) counting
error. It does NOT
transfer at H comparable
to sqrt R via this
argument. Nor does (14)
count p first used
BELOW an already attained
record, repeated p
firings, or the lower
excursion gain d_e.
Those contributions can
still be large.

## 8. Connection to the twin witness without post-cut recycled histories

Set S0=sqrt(2R+1),
H=ceil(4S0), and use the
common physical survivors
to L_(H+1) by T.
Let G_H be gain before
that cut. Its elapsed
time is H-2+G_H/2.
If W is the elapsed
time of the last
completed event (zero
if none), the universal
mod-30 potential gives
W<=9G_H/4+8. Hence
the time from that
arrival to the pre-cut
tick obeys

    I >= H-10-7G_H/4.

At a non-twin center
a in the physical slab
a<=2R and a positive
even, there is an odd
neighbor factor <=S0.
The next event is
within 2S0 ticks.
The cut is taken
before its own tick,
so I<=2S0. Consequently

    G_H >= (4/7)(H-2S0-10)
                      = (2/7)H-O(1)            (15)

for every surviving
root with non-twin
cut endpoint. This is
the preheight version
of the previous
terminal-excursion
criterion. In particular
one root with
G_H<=H/4 at arbitrarily
large R certifies
twin infinitude.

By (5) an alternative
sufficient condition,
requiring no post-cut
merger analysis, is
a nonempty common
surviving root set S
on unbounded slabs
with

    sum_(b,e) D_e v_b(x)
              <= (2/7-delta) H |S|              (16)

for a fixed delta>0.
This is a direct
first-height gain
criterion rather
than the older
elapsed-time mean
gain criterion.
It counts the entire
below-record recycled
history through its
return edges. In this
ledger one can separate
the first-use triggering
gain (14) from
all the d_e and
repeated-trigger gains.
The latter terms, and
actual large-height
estimates for the
former, remain open.
Neither (10) nor (14)
implies (16).

## 9. Executed audits

All three final scripts were executed in the
ECMAScript research runtime, fetched from the
exact remote commits and re-executed with
matching output. Reproduce with node.
No separate Node or Lean invocation.
An initial scratch pair identity incorrectly
used the first common first cut instead
of the first shared return edge (section 3).
An extension also initially applied the
p>=5 repeat-use spatial bound to p=3.
Both scratch assertions were corrected;
the final scripts use the stated conditions.

A. research/min_local_negative_record_return_forest_audit.mjs
   commit bbb871b7afed07106c1c9901aa505e289e01f4c4
   blob 12b05f8777481e32333d913b1ec3b4d5fb40adaf

Actual slabs R=3000,12000,48000,192000
with maximum record H=64,128,256,512.
Every canonical root reaches its final
cut by T. Store cut intervals and record
return edges, independently compute
first-cut masses by interval sweeps,
check (2)-(6), same-label repeats,
short injection and classify base
cross terms by quotient and first use.
At R=3000 independently scan all
unordered pairs including diagonals.

    roots                                  42504
    completed events                      866073
    record intervals                      229441
    return-edge incidences                207803
    distinct return edges                  68339
    traffic checks                        126893
    short-injection controls               66559
    same-class repeated-return keys           28
    branch-pair controls                     813
    energy/spatial moment controls           948
    gain partition controls                42504
    pair checks                           125751
    pairs sharing earlier return edges      177
    first-use record controls             152789
    repeated-use p>=5 distance controls     36156

All final assertions passed. Energy increments
are ordered-pair quantities (factor two for
distinct pairs). In the four slabs:

    R        total increase  base cross     short-base cross
      3000          5692          5670            5380
     12000         51992         51786           43574
     48000        300426        299484          255330
    192000       1951032       1946010         1675458

In the largest control base-cross accounts
for .99742598 of the increase; short-base
.85875475. Branch-only contribution is 5022,
including 4318 short/short and 704 short/long.
All short/short collisions have different
labels in this finite control. No general
absence of long/long collision is asserted.

At R=192000 and H=512:
  total base cross                   1946010
  first-use incoming                 1809162
  previously-used incoming            136848
  top (p>=b/4) incoming              1726028
  top first-use incoming             1691900
  top previously-used incoming         34128
  top slow incoming                  1541888
  base cross with recycled traffic      45324

Thus 98.0% of the top base cross
has first-use incoming label, and
92.97% of all base cross has first-use
incoming label. Base cross with
recycled traffic (v-u at source)
is only 2.33% in this control.
The quotient-one plus reset alone
accounts for 584304 of base cross,
fresh minus quotient-one 415522,
minus quotient-three 246330, and
plus quotient-three 232774.
These are classifications by
incoming root label history;
the base partner's p-use history
was NOT measured. In particular
they cannot be used as a numerical
estimate of the two-sided term (12).

The final mean gain for this slab
through first preheight 513 is
529.1098, normalized final energy
61.96784. The chosen H is far below
4 sqrt(2R+1); this is not a twin
witness test. The weighted traffic
527580226 is .02681386 of the
deterministic bound (2T+6) E_final.

B. research/min_local_negative_old_prime_deletion_dilution_audit.mjs
   commit f7a1a33b494f2c53e50cd50c00bf950527cf36db
   blob 46b7a78d6e6cda5dca606bcc0fefb4ff61a631d1

Exact old/full periods for (b,p)=
(5,5),(5,11),(6,7),(6,13),(7,5),
(8,11),(8,17). Enumerate old roots,
select the unique activating lift,
check every earlier event interval
for p preemption and final idle
interval for earlier p clock.
Compare the complete accepting
root lists with independent full
period simulation and moments
r=1,2,3. Controls:

    old root classes                     29906
    full root classes                   371910
    activation/certificate checks        15245 each
    first-use root checks                15245
    exact moment comparisons                21

All assertions passed. All
activated roots retain their
first-use event in these
small periods, including
old p=5 at b=7. This
is not true in general;
audit C supplies concrete
loss examples. The script
has an unused zero
baseVirginPairChecks
counter; (12) is a
paper-level inequality
and was not separately
numerically audited.

C. research/min_local_negative_old_prime_retention_audit.mjs
   commit 35d315e7652b5afd9e41631c34a40c7d9d361b9d
   blob 1934f5cee1b4d533534658decbfd23cf34dd7762

Actual slabs R=48000 (all roots),
192000 (step 7 in canonical root
index), p=11,23,47,97, k=1,3,5
and both signs. Independently
simulate p-deleted and full
paths to b+1. Compare every
first-use record source,
retention and activation
moments; check (13) at
early plus levels. Counts:

    root/prime/height controls           301752
    activated roots                       6707
    retained first-use roots              5225
    activation losses                     1482
    early plus low-gain controls          1845
    earlier same-position clock checks    1277
    pointwise moment checks               3554

All final assertions passed.
For R=48000, p=11, plus k=3
there are 386 activated and
364 retained roots, all 279
low-gain roots retained.
Example loss A=50106:
deleted exit at a=50040,
old gain 66, full first p
at a=50106, plus preheight 8
instead of b=19. At plus
k=5, p=47, only 20 of 163
activated roots retain the
designated first use, with
143 earlier same-position
clock losses. This confirms
that unconditional old
equality would be false.
First-minus controls always
retain. These finite slab
comparisons do not assert
uniform p residue distribution
or validate (14) at polynomial
actual heights.

## 10. Remaining proof

The old-label transfer is now
an exact return forest, with
traffic, spatial moment and
gain ledger. Same-label return
injection removes much of the
branch-collision complexity.
The numerical dominant term
is the base/return cross
correlation, typically with
a first-use incoming label;
(11)-(12) give an arithmetic
way of separating that term
even for old labels. The
unconditional first-use
record triggering supply
bound (14) is a formal
result and exact-period
actual result at logarithmic
heights. The necessary
control of deleted-profile
cross correlations, below-record
excursion gains, previously-used
partners, and actual square-root
height transfer remains missing.
The direct witness inequality
(16) provides a route that
does not require controlling
post-cut histories, but is
not established. No twin
infinitude proof, Lean
verification, changes to
canonical Lean targets,
sibling branches or Context
files.
