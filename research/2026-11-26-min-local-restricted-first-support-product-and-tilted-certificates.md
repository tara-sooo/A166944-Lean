# First support-product crossing and tilted local certificates

2026-11-26 JST. Continuation of f48cdef9a92d54fc592bdb8cbf753385f47bbf19.
Use the primorial wall to stop the positive CRT certificate tree
at the first sufficiently large product of discovered primes.
This gives a variable-discovery-count local transfer and a
necessary quantitative query-cost condition under finite twins.
Paper deductions and executed finite diagnostics; no Lean
verification, external novelty claim, or twin-infinitude proof.

## 1. Stop at the first support-product threshold

Let A be all admitted odd primes, with maximum z. Fix a known
base A0 containing 3, and track every prime in H=A minus A0.
The base period P0=4 product_(p in A0)p fixes canonical roots
modulo 4 and at every base prime. Let M be the product of
distinct discovered primes of H, initially 1.

After any actual prefix, all selected labels divide

    Q=2 product_(p in A0)p M = P0 M/2.

The primorial wall is valid even if some base labels were never
selected. For even u below the next multiple J of Q, any admitted
selected p satisfies u=+1 or -1 mod p, so the even positive
distance J-u is at least p-1. The step u->u+p-1 cannot strictly
cross J; no selected label is possible at J. If X is itself
a multiple of Q, no event using this support can start there.
Consequently the entire prefix has physical gain G<Q.
This argument only needs the positive source congruences,
not the first-clock choice.

Fix physical displacement D with P0<2D, and set

    M0=2D/P0>1.

Every trajectory reaching gain >=D must hit M>=M0 by then.
Stop the query tree at the FIRST discovery with M>=M0,
at a terminal, or at the displacement cutoff. Count the
successful query causing the threshold crossing itself,
even if its event also causes physical cutoff.
At each successful leaf

    M0<=M<z M0,
    m=P0 M<2Dz.                                      (1)

There is no fixed count of discoveries in this tree.
If a real path terminates without reaching M0, its gain
is <D. This is independent of all later trajectory behavior.
The bound also holds on hypothetical negative branches of
the relaxed tree, because its distinct positive congruences
are compatible by CRT, and the wall holds for the selected
support of any representative. No negative-branch feasibility
test is needed for the upper bound.

## 2. Tilted positive certificates

Fix s>=0. Charge a previously untested query to an unknown
prime p in H the cost

    a_s(p)=p^(s-1),

on either outcome. Cache negative residues and positive
discoveries as in f48cdef. All queries in H prior to stopping
are charged, not just queries in a selected dyadic band.
Introduce an auxiliary stop BEFORE the next query would
exceed total cost B>=0.

Retain only positive residue equalities at success leaves,
together with the fixed base residue, giving a multiset of
CRT certificates with modulus m as in (1). Assign each such
leaf ordinary weight w=1/M and tilted weight M^s w.
A negative edge has tilted weight 1 and a positive edge has
tilted weight a_s(p). These are certificate weights, not
conditional branch probabilities.

For any subtree with remaining budget b, total tilted weight
of success leaves is <=exp(b). Indeed at a binary query of
cost a, the induction step uses (1+a) exp(b-a)<=exp(b).
The finite displacement stop and finite scan per source
make deterministic segments finite, and the query budget
bounds the number of charged queries. Terminal/failure
leaves contribute zero; an immediate success contributes one.

A refinement: if at least one MORE positive discovery is
required on every successful continuation, the bound is
exp(b)-1. The negative branch still requires at least one
positive; the positive branch may succeed immediately.
Thus its step is

    [exp(b-a)-1]+a exp(b-a)<=exp(b)-1.

Since M0>1, every successful path from the initial base
requires at least one positive discovery. Consequently,
for EACH canonical base residue,

    sum_(success leaves) M^(s-1) <= exp(B)-1,
    sum_(success leaves) 1/M <= (exp(B)-1)/M0^s.       (2)

No fixed k, independent event assumption, or full-period
probability approximation is involved. This is different
from the factorial bound with a prescribed discovery count
in f48cdef. That bound is sharper for fixed small counts;
the present tilt handles the product threshold with arbitrary
discovery counts and weights larger primes differently.

## 3. Local count without a fixed number of discoveries

For an arbitrary positive seed slab I of length L, one
certificate contains at most L/m+1 roots. By (1),

    L/m+1 <= (1+2Dz/L) L/(P0 M).

Sum over all successful leaves and the P0/6 canonical
base classes using (2). The number of actual roots
whose first support-product crossing occurs within budget B
is at most

    L/6 (1+2Dz/L) (exp(B)-1) (P0/(2D))^s.          (3)

In particular the same bound applies to the roots whose
trajectory reaches physical distance D and whose cost up
to the first product crossing is <=B. No requirement
is imposed on the cost after that crossing. This last
feature avoids the need to estimate the complete long
trajectory or all subsequent bands.

The result applies directly to any physical interval,
even when the full admitted period is exponentially
larger than L. The base product must fit P0<2D,
and the certificate error factor is now controlled
by D*z rather than P0*z^k for a fixed k.
It is still a conditional small-cost bound, not an
unconditional displacement estimate.

## 4. Necessary query-cost distribution under finite twins

Let R tend to infinity, y=sqrt R, and admit every odd prime
p<T, where T=ceil(sqrt(3R+1))+1. Then z<=2y for all
large R. Take canonical roots in [R,2R), so L=R and
N=R/6+O(1). Fix 0<alpha<1 and put D=ceil(y^alpha).
Choose a base of all odd primes <=kappa log y, containing
3, for fixed 0<kappa<alpha. By the prime number theorem
P0=y^(kappa+o(1)). Alternatively use a fixed base and
interpret kappa=0. All estimates below are in the physical
slab, not over the full prime period.

Assume finitely many twin prime centers. For all sufficiently
large R no canonical restricted trajectory terminates before
D: a terminal u<2R+D<3R has both neighbors free of odd
prime factors <T, so both neighbors must be prime.
Thus EVERY root reaches D, and in particular hits M0.

For fixed lambda>0 choose s=lambda/log y.
Let C_lambda(X) be the actual accumulated tilted query
cost up to and including the first M>=M0 discovery.
Under the finite-twins assumption it is defined for every
root in the slab. We have

    2Dz/R=o(1),
    M0^s -> exp(lambda(alpha-kappa)).

For every fixed b>=0, (3) gives the necessary upper
bound on the LOW-cost population:

    limsup_R (1/N) # {X: C_lambda(X)<=b}
         <= min(1, (exp(b)-1) exp(-lambda(alpha-kappa))).  (4)

In particular if b<log(1+exp(lambda(alpha-kappa))),
a positive fraction of roots must exceed b under
finite twins. This is a quantile obstruction, not
a bound on actual query cost without that hypothesis.

Integrating the corresponding tail lower bound over
0<=b<=log(1+exp(A)), A=lambda(alpha-kappa), gives

    liminf_R (1/N) sum_X C_lambda(X)
      >= (1+exp(-A)) log(1+exp(A))-1.               (5)

Indeed int_0^log(1+e^A) [1-e^(-A)(e^b-1)] db is
the displayed expression; Fatou's lemma on this fixed
bounded interval suffices. No uniform integrability
assumption is needed. Equations (4)-(5) are
consequences of the necessary product crossing,
not claims that the actual mean tends to this bound.

An explicit sufficient target: alpha=0.9, kappa=0.1,
lambda=2, b=1. Then the limiting upper fraction
under finite twins is (e-1)e^(-1.6), approximately
0.347. Thus a bound showing that, along unbounded R,
more than 0.35 of the roots either terminate before
D or hit the first support-product threshold within
cost 1 would contradict finite twins. Terminations
before D themselves directly give twin centers.
The numeric constants are merely one choice of
parameters, not empirical estimates.

One can define the cost on every path up to the
first of product threshold, physical cutoff, or
terminal. If a positive fraction of paths stop
with small cost, (3) bounds the fraction that are
product crossings; the remainder are genuine
terminals. More precisely the fraction of terminals
before the product threshold is at least

    fraction with stopped cost <=B
      - (1+2Dz/R)(exp(B)-1)/M0^s * (R/(6N)).

Whenever this difference is positive, at least
one root has G<D and hence supplies a twin center.
This is an unconditional finite inequality; its
use at unbounded R requires the actual cost
distribution estimate, which is not established.

## 5. Connection to occupation and the remaining obstacle

The weighted query charge on an actual prefix
can be bounded by the earlier quiet-coarea
construction with weights p^(s-1) instead of 1/p,
plus successful query costs and any virtual
terminal queries. For the first support-product
stop the final query is included. For an arbitrary
range of tracked primes one must account for
possible multiple candidates at a firing tick,
or simply use all upward ticks. The stronger
unique-band-divisor cancellation in 2d4882e4 does
not automatically hold for the entire tracked range.

The major gain here is that no estimate on all
band gains, the full terminal displacement,
or the occupation after the product threshold is
required. The remaining problem is an upper
bound on an actual early-query-cost quantile in
a dense cutoff, with the growing base small
enough to leave M0>1. Small and intermediate
primes still cause substantial query costs.
Neither the previous high-height occupation
bounds nor full-period conditional averages
establish the required local quantile.
The theorem does not establish short termination
or twin infinitude.

## 6. Executed diagnostic and persistence

Source research/min_local_restricted_product_barrier_audit.mjs,
final commit 26638442a42e4490bb4e760a888c763301da785d,
blob 3538a40787382031cd127ff45e6f11e1b12a33aa.
Executed as ECMAScript in the research runtime,
fetched at the exact commit, and re-executed.
Reproduction:
node research/min_local_restricted_product_barrier_audit.mjs
No separate Node or Lean process invoked.

Nine controls with all admitted odd primes <=z,
known base, displacement cutoff D, tilt s and budget B.
Enumerate relaxed binary certificate trees for every
base residue; check the positive-product wall on
relaxed paths, every certificate's modulus bound,
tilted per-base leaf weight, and local counts.
Independently compute ordinary next event from
source divisibility and clock times for every
actual seed, then scan literal defect queries
to identify its first product crossing.
The three extra controls require multiple discoveries
to cross the product threshold.

    P0   z     D    roots    leaves   multi-leaves  actual within budget
    12    7    18       70         4          0              22
    60   13    65    10010        35          0            3480
   420   17   300   170170       272          0           47438
    12   31    45     1667         4          1             177
    60   61   120     5000        39          0            1648
   420  127   300     5000       622          0            2159
    12   17   300   170170        77         77           37493
    60   31  1000     5000       491        491            1075
    12  127  1000     5000        86         86             262

Totals 372087 root/control incidences, 178 base
classes, 1995 branch states, 1817 binary queries,
1630 success certificates of which 655 have at
least two positive primes, 116082 certificate/root
incidences, 170434 actual product crossings
(75425 with multiple discoveries), 93754 budgeted
actual crossings covered, 16159 duplicate covers,
2173 actual physical exits, 751 of those with
budgeted product crossings, 518865 wall checks,
688919 independent clock checks. All assertions passed.
Real roots with product threshold not reached
terminated before physical cutoff. Many parameter
choices give a theoretical fraction bound >1
and so are only finite arithmetic controls.
The z=31,D=45 control has bound .80248 and
177/1667 actual budgeted crossings. No asymptotic
cost quantile or finite-twins hypothesis is
inferred from these tests.
No changes to canonical Lean targets or sibling
branches.
