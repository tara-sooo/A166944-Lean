# Negative MIN: stopped-prefix criterion and laminar weighted relay budget

2026-11-26 JST. Continuation of 567028a5f9cd17db3c53a340cee2d935f5eb749d.
Adopt the stopped forward-prefix target proposed in the other
research discussion, as approved by the user. Establish its exact
finite twin-witness implication and a multiband packing certificate
that never charges the same lower-label gain twice. Paper arguments
and executed finite controls; not an asymptotic extinction or
twin-infinitude proof.

## 1. Stopped-prefix target and finite witness

For 6|A, A>=12, initialize remaining distance a=A,
clock v=-A/2+3. Follow the ordinary negative MIN, including
only completed events at times <=-1, and stop at the
first arrival with a<=A/2 or when the next event would
fire after -1, whichever comes first. Denote the
completed elapsed wait by W(A), cumulative gain by G.
The standard nonnegative height invariant is

    h=3+W-G/2 >=0.

If the half-distance boundary is reached, G>=A/2,
hence W>=A/4-3.

Otherwise the final source a is >A/2. If it is not
a twin center, q(a)<=sqrt(A+1), and its actual next
wait w<=2q(a)<=2sqrt(A+1). Since the gap from the last
completed clock v to -1 is strictly smaller than w,

    W >= A/2-4-2sqrt(A+1).

Thus if no twin source occurs in the prefix, including
the final unfinished source if there is one,

    W(A)>=min(A/4-3,A/2-4-2sqrt(A+1)).              (1)

In particular a strict violation of (1) certifies
a twin center in (A/2,A], not necessarily the initial
source or the final one. In fact in the non-crossing
case the final unfinished source alone is enough.
Under finite twins all sources in this range are
non-twin for large A, so liminf W(A)/A>=1/4.
Conversely a sufficiently large twin center A
has its first firing at zero (376c97e), hence W=0.
The following statements are equivalent:

    infinitely many twin primes;
    liminf_(6|A,A->infty) W(A)/A < 1/4;
    liminf_(6|A,A->infty) W(A)/A = 0.

No assertion about eventual terminal phase or the
entire inverse fiber is needed. The fixed numerical
threshold in (1) is a sufficient finite witness,
not a new prime distribution theorem.

For budgets on actual completed-event gains,
exclude the last crossing event if the prefix
stopped at the half boundary. Under the non-twin
assumption it costs at most 2sqrt(A+1) wait.
The remaining block has total gain G'<A/2 and

    W' >= A/4-3-2sqrt(A+1)

in the crossing case. In the time-stop case retain
all completed events and use (1), giving
W'>=A/4-O(sqrt A) in both cases. This removes
possible large final-gain overshoot from the
multiband resource budget. All complete-event
sources are in (A/2,A].

For comparison the latest single-threshold estimate
of 567028a (T comparable to sqrt A) is

    W << G_low + J sqrt A + sqrt(J A G_low)+sqrt A

on a non-twin prefix, where J is the number of
distinct ordered unequal-label/sign keys. Therefore
J=o(sqrt A) and (J+1)G_low=o(A) on the same unbounded
sequence suffice by (1). It is sufficient to replace
J by 4L^2. These are not yet established on any
unbounded sequence.

## 2. Multiband relay intervals form a laminar family

Fix a base threshold t>=5, and partition selected
labels >=t into dyadic bands B_j=[2^j t,2^(j+1)t).
Index a finite completed-event sequence by i.
At level j, break it at all events in higher
bands. Between successive level-j marks in a
component define the relay I as the set of indices
STRICTLY between the two marks. All labels within
I belong to lower bands (or are below t). Empty
relays are allowed in the arithmetic packing,
but need not be included as nonempty intervals.

For two nonempty relay intervals at the same level,
their interiors are disjoint. For levels j<k,
a level-j relay cannot contain a level-k mark:
such a mark is a separator at level j. Thus if
a level-j relay meets the interior of a level-k
relay, it is contained in the latter. In particular
all nonempty relays form a laminar family (disjoint
or nested). This is a deterministic fact about the
band word, independent of clock phases.

Let E_I=sum_(i in I)(p_i-1), and split

    E_I=H_I+g_I,
    H_I=sum_(i in I:p_i>=t)(p_i-1),
    g_I=sum_(i in I:p_i<t)(p_i-1).

The marked part H_I is known from the band word and
the actual >=t labels. The lower gain is a single
shared budget G_<t=sum_(p_i<t)(p_i-1).
We want a lower bound on G_<t that can combine all
levels without counting a lower event repeatedly.

## 3. Weighted CRT packing, including unequal weights

Group the relays at all levels by
g=(level,p,r,e,f), with p!=r the endpoint labels
and e,f their source sides. The positions of first
sources of this group are distinct; write d_g
for their spatial span (or use a valid containing
interval length minus one). For each fixed relay
gain E>=0, the CRT modulus is 2pr, so its number
of occurrences in group g is <=c_g, where

    c_g=floor(d_g/(2pr))+1.

Suppose there are n_g relays. Assign arbitrary
nonnegative weights lambda_I to them and sort
them into decreasing order lambda_(1)>=...>=lambda_(n_g).
Then

    sum_(I in g) lambda_I E_I
        >= sum_(i=1..n_g) 2 floor((i-1)/c_g) lambda_(i)
        =: P_g(lambda).                             (2)

Proof: the increasing rearrangement of the even
nonnegative gains has ith entry >=2 floor((i-1)/c_g).
The rearrangement inequality puts the smallest gains
against the largest weights in the minimum scalar
product. Both facts hold even if some weights
are zero, some gains are arbitrarily large, or
weights were chosen from the observed word.
This weighted inequality does NOT require equal
lambda within a group. It reduces to the exact
unweighted packing lower bound of 567028a when
all lambda=1. A same-label relay has E_I>=p-1,
and needs no group packing.

Subtract the known marked gain:

    sum_(I in g) lambda_I g_I
       >= (P_g(lambda)-sum_(I in g)lambda_I H_I)_+.  (3)

For same-label relays replace P_g by lambda_I(p-1)
and take the positive part after subtraction of
lambda_I H_I. The positive part is valid because
the actual remaining gain is nonnegative.

## 4. Non-double-counted budget certificate

Choose any nonnegative weights satisfying the
pointwise capacity constraint on EACH lower event:

    sum_(I containing i) lambda_I <=1,  p_i<t.       (4)

Then sum_I lambda_I g_I <= G_<t by interchanging
the two finite sums. Combining with (3) gives

    C(lambda) =
      sum_(unequal groups g)
        (P_g(lambda)-sum_(I in g)lambda_I H_I)_+
      +sum_(same-label I) lambda_I(p-1-H_I)_+
      <= G_<t.                                      (5)

This is a single global inequality incorporating
every selected band. It charges only the part
of the packing cost not already explained by
known >=t events. It is valid for any feasible
weights, and one may take the supremum over them.
One may also restrict all weights to [0,1] for
bounded optimization; the examples below do so.
Groups are disjoint as sets of relay incidences,
not as spatial intervals. Their residual charges
sum correctly only because of (4).

For example, let D(i) be the number of nonempty
relays containing lower event i. Give a relay
containing a lower event the weight

    lambda_I=1/max_(i in I,p_i<t) D(i).

Give weight zero to relays containing no lower event.
At every lower i, each of its D(i) weights is <=1/D(i),
so (4) holds. The uniform weight 1/max_i D(i)
is another feasible choice (when a lower event
exists). Alternatively take weights one on a
disjoint collection of relay intervals, zero
elsewhere. The laminar structure makes these
choices especially easy to compute.

Equation (5) is a lower-bound certificate, not an
upper bound on lower gain. For the stopped,
overshoot-trimmed non-twin prefix in section 1,
write G_hi=sum_(p_i>=t)(p_i-1). Then necessarily

    G_hi + C(lambda) <= G'<A/2.                    (6)

One can also use G_hi+max(C(lambda),W_low/3)<A/2,
since W_low<=3G_<t. The maximum avoids counting
the same lower-label gain twice even within a
single level. Thus a hypothetical macroscopic
time prefix whose band data force the left
side of (6) above the available budget is
impossible.

The certificate uses actual label/sign keys,
source spans and marked gains; it does not
need the unknown exact small-relay gains as
input for its lower bound once these data and
the interval incidence structure are supplied.
The difficult next step is a lower bound for
C(lambda) (or another global obstruction)
from the assumption W'>=A/4-O(sqrt A) on
canonical non-twin prefixes. It is NOT shown
that (6) fails for such prefixes. With many
distinct transition keys or no repeated key
at its local CRT capacity, (2) can give zero.
The marked gain H_I can also absorb the entire
packing demand. Laminarity resolves accounting,
not the prime-pair existence problem.

## 5. Executed audit

Source research/min_local_negative_laminar_relay_budget_audit.mjs,
commit fc075350f947389a6e4bb20f6f12812bcc7a2e69,
blob df37b350deb16ab7e51c4e88f9d427ea66694ef7.
Executed in the ECMAScript research runtime,
fetched at the exact commit and re-executed
with identical output. Reproduce:
node research/min_local_negative_laminar_relay_budget_audit.mjs
No separate Node or Lean invocation.

All canonical A=12,18,...,120000: 19999 seeds,
355317 completed events, 3 half stops, 19996
time stops. 19993 visited a twin source including
the final unfinished source, 6 did not. All six
non-twin lower-bound checks of (1) passed. All
19982 strict small-wait witnesses had visited
a twin source. Non-twin controls are therefore
very sparse in this canonical sample; it does
not test asymptotic finite-twin behavior.

The multiband controls use 376 contiguous
non-twin blocks from sparse canonical negative
and noncanonical clock phases 0,17,floor(A/5),
in slabs R=10000,40000,100000,180000. Five base
thresholds 5,7,11,17,23 per block. Noncanonical
positive-time controls are used to exercise
overlaps, not to infer canonical asymptotics.

    block/threshold controls           1880
    relay incidences                   3983
    empty relays                       1301
    same-label relays                   443
    unequal key groups                 3374
    laminar pair checks                3412
    lower-event incidences with
      multiple enclosing relays         761
    maximum observed nesting depth        4
    cases unweighted lower gain sum
      exceeds total lower gain           31

Three feasible weight allocations per control:
uniform inverse maximum depth, local inverse
maximum depth, and deepest-relay-only unit
weights. 71238 pointwise weight checks,
10122 weighted group packing checks,
5640 full residual-budget checks. All passed.
1014 allocations give a positive total
certificate (including same-label terms);
only 6 unequal group incidences yield
positive residual packing costs. The largest
certificate is 42, and the largest ratio
certificate/actual lower gain is 0.75.
The unequal packing bounds are often zero
in these finite samples. No numerical
contradiction to the canonical gain budget.

Additionally 63 synthetic packing controls
with c=1..3, n=1..7 and nonuniform weights,
53217 enumerated permutations of the cheapest
multiset. Every minimum matches (2).
These are arithmetic packing checks, not
assertions of realizable MIN trajectories.

## 6. Status

The stopped forward-prefix criterion is now
recorded and the multiband relay charge has
an explicit no-double-counting inequality.
The remaining core is to prove an unbounded
sequence with W(A)/A bounded below 1/4,
e.g. via a gain-budget contradiction for
hypothetical long non-twin prefixes or the
joint single-threshold sufficient condition.
No asymptotic bound of this kind, twin-
infinitude proof, or Lean verification.
No changes to canonical Lean targets or
sibling branches.
