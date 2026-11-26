# Negative-query Laplace certificates and terminal-scan obstruction

2026-11-26 JST. Continuation of e5a92bbc8ca2fe4c469a24ae261803cb2aa2e182.
Correct the low-cost quantile target if terminal verification queries
are counted, and replace it by a negative-query Laplace criterion
that excludes virtual terminal scans. Paper deductions and executed
finite diagnostics. No Lean verification or twin-infinitude proof.

## 1. Obstruction in the previous cost target

Keep A all odd primes below T, T just above sqrt(3R+1),
y=sqrt R, canonical X in [R,2R), D=ceil(y^alpha),
0<alpha<1. Base A0 containing 3 with P0=4 prod A0<2D.
Stop at the first new support product M>=M0=2D/P0,
or actual restricted terminal. Reaching D without
product crossing is impossible by the primorial wall
in e5a92bb.

The previous count of budgeted PRODUCT CROSSINGS is valid.
But a cost criterion for ALL stopped roots must specify
whether the virtual terminal scan is counted. If the
terminal scan is included, the low-cost target from
section 4 of e5a92bb cannot hold at large R.

Indeed suppose a path terminates before the support-product
threshold. Put S=A0 union discovered primes. Then
prod_(p in S)p=P0 M/4<D/2. At the terminal u, for every
unused prime p in A minus S the two residue classes
X=+1-(u-X) and -1-(u-X) mod p both give negative tests.
A full scan of 2 max(A) ticks includes the two clock
opportunities of p, whether or not their residues were
already rejected in earlier scans. Thus at least two
distinct negative residues have been counted for each
unused prime by the end of the terminal scan.

For any s>=0 the previous all-query weight p^(s-1)
is >=1/p. The new negative-only weight below is also
>=1/p. Use p>log y: the number of such primes in S
is <=log(D/2)/loglog y, and their reciprocal sum is
O(1/loglog y). Hence every genuine terminal before
the product crossing has full-scan cost at least

    2 sum_(log y<p<T) 1/p - O(1/loglog y)
      = 2(loglog y-logloglog y)+O(1) -> infinity.   (1)

The Mertens estimate is for the two prime cutoffs,
not a distribution assumption about the actual path.
The bound holds for any base satisfying the stated
product cap.

In particular for fixed budget B=1, eventually
NO such terminal belongs to the low-cost population
if its full verification scan is included. Therefore
the previous proposed 35% low-cost target, with
alpha=.9,kappa=.1,lambda=2, is already ruled out by
the crossing count UNCONDITIONALLY with full-scan
accounting. It cannot prove infinitude that way.
This corrects the interpretation of that target;
the positive certificate count itself is unchanged.
If costs only include actual event scans, the same
count applies to product-crossing leaves and the
terminal obstruction (1) does not apply. A virtual
terminal scan may still be run in the algorithm to
identify termination; it simply must not be included
in the score assigned to terminal leaves.

## 2. Exact conservative weights on the relaxed query tree

Fix 0<=s<1. At an unknown distinct residue query
of p in H=A minus A0, charge only the NEGATIVE
answer the cost

    f_s(p)=-log(1-p^(s-1)).

A positive answer has cost zero. Cache rejected
residues and positive discoveries as previously.
Let F_s(X) be the sum up to the first support-product
crossing or actual terminal, EXCLUDING all virtual
terminal scans. Include failed queries preceding
the winning clock of the crossing event, including
least-prime tie candidates. No charges after a
prime is known positive. We use full actual event
scans, not the trimmed coarea bound without its
domain restrictions.

For each fixed canonical base residue, build the
finite relaxed query tree as in e5a92bb without a
cost budget. Stop at threshold M>=M0, terminal,
or physical displacement D (unreachable before
threshold). The finite gain cutoff and finite scan
at each source give finite depth. Negative branches
may be impossible, which merely enlarges the tree.
Every selected label is consistent with the positive
constraints, so the primorial-wall reasoning still
applies on relaxed branches.

Give each negative edge weight exp(-f_s(p)) and
each positive edge weight p^(s-1). These are not
the actual conditional probabilities of a query.
They nevertheless sum EXACTLY to one:

    exp(-f_s(p))+p^(s-1)=1.

Total tilted mass of all success leaves is at most
one, by finite tree mass conservation. On a success
leaf with discovered product M and accumulated
negative cost F, the mass is

    exp(-F) M^(s-1).

All success leaves precede any virtual terminal
scan; negative charges on branches ending at a
terminal do not enter the success-leaf weight.
Retain only positive congruences as in f48cdef.
Each certificate has modulus m=P0 M with
2D<=m<2Dz, z=max(A). Therefore for each base residue

    sum_(success leaves) exp(-F)/M <= M0^(-s).      (2)

Unlike the previous exp(B)-1 bound, this is a
weighted sum over ALL success leaves, without
fixing a cost quantile or integrating a budget tail.
The same leaf can cover multiple real roots;
overlaps of certificates are counted with
multiplicity and only enlarge the upper bound.

## 3. Weighted local crossing and terminal score

Let I be any positive interval of length L,
N its number of canonical roots. Since a certificate
of modulus m contains at most L/m+1 integers,
summing (2) over P0/6 base residues yields

    sum_(X in I, crossing) exp(-F_s(X))
        <= L/6 (1+2Dz/L) M0^(-s).                 (3)

Every actual root's crossing leaf retains its exact
physical-prefix cost; the weighted covering is
valid even if multiple leaves cover one root.

Let E_I be the actual finite-slab average, and let
tau_I denote the fraction of roots reaching an actual
terminal before product threshold. Each terminal
score exp(-F_s) is <=1. Thus unconditionally

    tau_I >= E_I exp(-F_s)
        - (L/(6N))(1+2Dz/L) M0^(-s).              (4)

This is a direct sufficient criterion for a short
terminal, using only the physical prefix cost.
It makes no claim that the RHS is positive.
If a terminal occurs before threshold, G<D;
at T>sqrt(3R+1), L=R, D<R and R sufficiently
large, its two neighbors are prime.

A refinement valid on finite small trees: retain the
actual tilted success mass A_r<=1 separately for
each base residue r. In (3) one may multiply the
right side by (6/P0) sum_r A_r, and/or sum each
individual weighted certificate count exactly.
A loss in tilted mass corresponds to terminal
leaves of the relaxed query tree, not necessarily
real feasible terminal roots in the physical slab.
No uniform asymptotic improvement of this mass
factor is claimed.

## 4. Consequences under finite twins and a moment target

Take L=R, y=sqrt R, z<2y, D=ceil(y^alpha) with
fixed 0<alpha<1, P0=y^(kappa+o(1)),
0<=kappa<alpha, s=lambda/log y for fixed lambda>0.
Then 2Dz/R=o(1), M0^s -> exp(lambda(alpha-kappa)).
If twin centers are finite, all sufficiently
large roots cross before termination. By (3)

    limsup E_I exp(-F_s)
        <= exp(-lambda(alpha-kappa)).             (5)

Jensen also gives under that hypothesis

    liminf E_I F_s >= lambda(alpha-kappa).         (6)

This is stronger than the integrated mean bound
in e5a92bb for its own (different) all-query cost;
the two costs must not be identified.
Without the finite-twins hypothesis (4) implies
infinitude if

    limsup E_I exp(-F_s) > exp(-lambda(alpha-kappa)).

A sufficient stronger condition, by Jensen, is
liminf E_I F_s < lambda(alpha-kappa).
The moment criterion needs no fixed positive
fraction bound at a particular cost and counts
only actual-event negative queries. The physical
cutoff and base/product stop keep the certificate
modulus o(R).

For alpha=.9,kappa=.1,lambda=2, the target
Laplace average is strictly greater than e^(-1.6)
(about .20190) along unbounded R. Equivalently
a mean physical negative cost uniformly below
1.6 on such a subsequence suffices. Neither has
been obtained. Choice of these constants is an
illustration, not a fitted favorable asymptotic
regime. One should not infer success from the
fact that terminal verification costs are now
excluded. The physical cost itself can remain
large and the large-scale samples below do not
establish the target.

## 5. Executed diagnostic

Source research/min_local_restricted_negative_laplace_audit.mjs,
commit 2a56f82ae9ba97490c3ab07315773464437808d9,
blob 627ad832135c0cfcba11730d345e268845be2a10.
Reproduce: node research/min_local_restricted_negative_laplace_audit.mjs.
Executed in ECMAScript research runtime, fetched at exact commit,
and re-executed with identical results. No separate Node or Lean.

Four exact relaxed-tree controls with maximum admitted
label z=7,13,17,31, including all base residues.
Independently enumerate actual seeds, literal candidate
queries and first support-product crossing. Verify
conservation of binary edge weights, per-base success
mass <=1, weighted certificate coverage, local inequality
(3), and (4). At actual terminal verify both terminal
residues negative for every unused prime, count only
additional distinct failures and compare full-scan cost
to the explicit finite lower bound 2 sum unused f_s(p).

    z    D    roots   actual crossings   physical score    bound (3)/N
    7   18       70            40           .76014             .92376
    13  65    10010          5561           .68610             .75463
    17 300   170170         68810           .52897             .31234
    31 300     1667           934           .37158             .59799

The physical score includes terminals; the bound
column is for CROSSING scores only. E.g. z=17
gives a positive finite lower bound on the terminal
fraction, about .2166; actual fraction 101360/170170
about .596. This control has fixed small z, and
terminal offsets are not necessarily twin centers.
All four weighted crossing and terminal inequalities
passed.

Three additional actual local samples with base {3}
(fixed P0=12), z=ceil sqrt(3R+1), D=ceil(y^.9),
s=2/log y. The last sample is shorter than R;
its bound uses its actual length, not length R.
These samples independently check actual clock and
terminal-scan identities and measure scores; they
do NOT enumerate the dense certificate tree.

    R        length    roots   physical score   mean physical cost
    10000      10000    1667      .282965          2.73229
    100000    100000   16667      .221212          2.99870
    1000000   120000   20000      .162802          3.38216

Conditional on actual terminal before product threshold,
mean physical cost vs mean cost including verification:
R=10000: .44448 vs 9.70026;
R=100000: .60109 vs 10.06565;
R=1000000: .85648 vs 10.48743.
Full-scan terminal scores are accordingly negligible
in those samples. These finite data show the importance
of distinguishing the two costs; they do not show a
favorable asymptotic physical score. Also the fixed-base
controls are not the growing-base kappa=.1 regime.

Totals 220251 root/control incidences, 1224 relaxed
tree states, 1208 new binary query nodes, 1120 success
leaves (1044 multi-discovery), 75345 exact weighted
actual coverage checks, 109365 actual product crossings,
110886 terminals before crossing, 454108 events,
4553833 actual ticks, 1943624 distinct negative queries,
2456960 additional terminal negatives, 110886 terminal
scan lower checks, 344839 wall checks, 16 per-base
tilted mass checks. All assertions passed. Floating
weights checked with tolerances; residue arithmetic
and counts exact within the tested integer range.

## 6. Remaining research

The previous full-scan low-cost quantile target was
intrinsically obstructed, including on short actual
trajectories. The new physical negative-only score
removes that obstruction and gives a direct local
moment criterion. The remaining substantive question
is whether the actual physical score exceeds the
threshold in (5) along unbounded slabs. It is not
enough to bound the cost of virtual terminal scans
or to apply full-period expectation inequalities.
The dense-base/local-cost estimate remains open,
and no twin-infinitude proof or Lean verification
has been obtained. No canonical Lean target or
sibling branch changed.
