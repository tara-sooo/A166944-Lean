# Rough known-support frontiers and the constant-gap obstruction

2026-11-26 JST. Continuation of 91b55926f586127b037a529e8c36b16dca5ee219.
A weighted upper sieve on known-support terminal frontiers bounds the
physical negative-query score of very large final discoveries, without
charging their final scan. More importantly, the same sieve bounds the
score of actual terminals before support-product crossing. This rules out
the proposed positive constant Laplace gap in 91b5592, unconditionally.
Paper deductions and executed finite diagnostics, not Lean verification
or a twin-infinitude proof.

## 1. Known-support frontiers before product crossing

Use the canonical restricted clock system of 91b5592. Admit all odd
primes up to z (or all p<T). Known base A0 contains 3, with
P0=4 product_(p in A0)p<2D. Track all other admitted primes, and let
M be the product of distinct positive discoveries. Stop on first
M>=M0=2D/P0, or at a genuine restricted terminal. Before this
threshold the physical displacement G satisfies G<P0 M/2<D
by the primorial wall. All positive prime residues and all base
residues are known in the relative transcript.

Define a known-support frontier to be a source BEFORE its scan,
where no base prime and no already discovered prime divides either
neighbor. This may be a genuine restricted terminal, or a source
whose next event uses an undiscovered prime. At fixed discovery
depth k (number of distinct positives) there is at most one such
frontier on any branch: at a frontier no known label can advance
the offset, so a further event necessarily increases k.

Let p_* be the smallest tracked prime, and assume the tracked set
is nonempty. The number of possible frontier depths before crossing
is at most J=ceil(log M0/log p_*), since M>=p_*^k and M<M0.
This bound includes the initial depth k=0. If the tracked set is
empty, the wall already forces terminal gain <D.

For 0<=s<1 use the negative-query cost f_s(p)=-log(1-p^(s-1))
and physical prefix cost F of 91b5592. Give negative edges
weight exp(-f_s(p)) and positive edges weight p^(s-1).
The weights sum to one at every binary node, including relaxed
impossible negative branches. The tree is finite by the physical
cutoff and the finite clock scan. At any frontier node, retain
positive equalities and base residue only, producing a congruence
class modulo m=P0 M<2D. Its relative tree mass is

    a=exp(-F) M^(s-1).

Here F ends BEFORE the frontier scan, and no virtual terminal
scan is charged. The frontier nodes at each fixed depth k are
an antichain in this tree. The sum of their masses, conditional
on each canonical base residue, is <=1 by conservation of
tree mass. Summing all frontier depths gives <=J. In particular

    sum_(frontiers at r) exp(-F)/M <= J,             (1)

because M^(-s)<=1. For fixed s>0 the right side can be
replaced by sum_(0<=k<J) p_*^(-sk), by the per-depth estimate.
These are weighted certificates; overlapping congruences
are allowed and do not invalidate upper counts.

## 2. A large new label forces a rough frontier

For an actual event with selected prime p, let q be the least
eligible admitted prime at its source. It exists whenever there
is an event. The wait w<=2q because every eligible clock
fires within its period. Nonnegative half-deficit h=v-u/2
starts at 3, and total elapsed waits <=3G imply h<=3+3G.
The two firing defect forms are 2(h+w)+1 and 2(h+w)-5.
They are odd and nonzero, so

    p <= 7+6G+4q.                                   (2)

If G<D and the final crossing label p>16D+16, then q>D.
Every base and previously discovered prime is <D:
their product is P0 M/4<D/2. Consequently the source
is a known-support frontier. It has no odd prime divisor
of either neighbor below D (provided all such primes
are admitted, as assumed in section 3).
A genuine restricted terminal before threshold is also
a frontier with no such divisors. Both use the score
exp(-F) BEFORE the last scan; for a terminal this is
exactly its physical score in 91b5592.

## 3. Uniform upper sieve on frontier certificates

Take y=sqrt R, D=ceil(y^alpha) for fixed 0<alpha<1,
z comparable to y and admitting every odd prime <D.
Use the canonical roots in [R,2R), N=R/6+O(1).
For a fixed frontier certificate X=b mod m, m<2D,
the offset u=X+G is fixed relative to X. To have no
odd prime divisor <D of u-1 or u+1, the progression
parameter must avoid two distinct residues modulo
each odd prime ell<D with ell not dividing m.
For ell dividing m, the known-support frontier
already certifies nondivisibility.

The standard dimension-two upper-bound sieve, in this
case two linear forms on a progression parameter
interval of length R/m, gives uniformly for such m

    # rough roots in this certificate
        <<_alpha (R/m) (loglog R)^2/(log R)^2.      (3)

Details of the sieve input: choose a fixed sufficiently
small delta>0 depending on alpha, so the sieving primes
ell<=R^delta lie below D and the Selberg upper sieve
level is a fixed small power of R/m. For squarefree
d built from those primes with gcd(d,m)=1, the count
of excluded residue classes has main density
2^omega(d)/d and remainder O(2^omega(d)), uniformly
in b,G,m. The elementary dimension-two upper sieve
bound (or Selberg upper-bound sieve for two linear
forms) at a sufficiently small fixed power level gives
O((R/m) prod_(3<=ell<=R^delta,ell not|m)(1-2/ell)).
The remainder can be absorbed uniformly since
R/m >> R^(1-alpha/2). The finite-prime product over
all odd ell<=R^delta is O_alpha((log R)^(-2)) by
Mertens. Removing prime divisors of m costs at most
O((loglog R)^2): for primes <=log R this follows by
Mertens, and the larger divisors of m have reciprocal
sum O(1/loglog R) from log m=O(log R). No lower
bound sieve or prime-pair distribution is used.
This is the standard upper sieve input in the paper
argument, not an independently kernel-checked theorem.

Multiplying (3) by exp(-F) and summing over all
frontiers and P0/6 base classes using (1),

    sum_(actual rough frontier incidences) exp(-F)
       <<_alpha R J (loglog R)^2/(log R)^2.         (4)

The inequality counts actual visits with multiplicity
across depths. For each actual visit the corresponding
certificate has the exact prefix cost and shift;
all false positive-only certificates only increase
the bound. Since J=O(log R), the right side is o(R).
If the base includes every prime <=kappa log y with
fixed kappa>0 and P0<2D, then J=O(log R/loglog R)
and the right side is O_alpha,kappa(R loglog R/log R).
For a fixed positive tilt s, the geometric depth
factor of section 1 improves J to O_s(1), although
the associated costs are larger. No equidistribution
over the full admitted period is involved.

## 4. Consequences for the earlier sufficient criterion

Let F_s(X) be the physical prefix score cost of
91b5592, ending at first product crossing or terminal.
Define T_score as the sum of exp(-F_s(X)) over real
terminal roots before crossing. Every such terminal is
a rough frontier, with its physical score measured
before the virtual terminal scan. Therefore

    T_score/N <<_alpha J (loglog R)^2/(log R)^2=o(1). (5)

This holds UNCONDITIONALLY, not under finite twins.
It does not imply that the unweighted terminal
fraction is o(1), because costs may be large.
For terminals of cost <=b, it does bound the
unweighted fraction by exp(b) times the RHS.
Likewise, for crossings whose final new prime is
>16D+16, the sum of exp(-F_pre) is bounded by
the RHS in (4), where F_pre excludes the WHOLE
final event scan, not just its positive query.
For fixed base, even b=(1-epsilon)loglog R
with fixed epsilon>0 gives o(1) of roots
having such a low-cost rough frontier, by (4).

For crossings with final p<=16D+16, the positive
certificate modulus is <2D(16D+16). The weighted
crossing count from 91b5592 therefore applies with
this improved overshoot bound. Define a modified
physical score using F_pre on the very large-final
crossings and the old F_s elsewhere. For this score,

    E_R modified_score
       <= (R/(6N))(1+2D(16D+16)/R) M0^(-s)
          + O_alpha(J (loglog R)^2/(log R)^2).     (6)

This bounds the modified score even if all final
large-prime scans are free. The original score is
no larger, so (6) also applies to it.

In particular take the previous suggested regime
P0=y^(kappa+o(1)), 0<=kappa<alpha<1,
s=lambda/log y with fixed lambda>0. Then (6) yields

    limsup E_R exp(-F_s) <= exp(-lambda(alpha-kappa))

WITHOUT assuming twin primes finite. The proposed
strict constant-gap criterion in 91b5592 is thus
impossible in that regime, not merely unproved.
The analogous strict mean-cost criterion is also
impossible by Jensen. This is a substantive
correction to the previous research target.
The weighted crossing inequality itself remains
valid. It could still imply a genuine terminal if
one showed a POSITIVE finite-scale excess above
its crossing-only bound along unbounded R, but
such an excess must tend to zero. One would need
much more precise crossing bounds and actual score
estimates on the vanishing scale of terminal score.
The present argument supplies only an upper bound
on that scale, not a positive lower bound.

For fixed 0<alpha<1 the extra rough-frontier sieve
factor also shows that extremely large final-label
crossings cannot be the source of a constant
weighted gap, even after removing their scan costs.
It does not establish a bound on total displacement
or rule out all long paths. No terminal existence
in an unbounded sequence of slabs is obtained.

## 5. Executed finite audit

Source research/min_local_restricted_rough_frontier_audit.mjs,
commit 9040c7694a456c624e15d250897e9b62cb30bcc8,
blob a18a2b0c43cbf4bf3590e936a9107d7635b981fd.
Reproduce: node research/min_local_restricted_rough_frontier_audit.mjs.
Executed as ECMAScript in research runtime, fetched at
exact commit, re-executed identically. No Node or Lean
process invoked separately.

Six finite controls, full admitted primes <=z, various
base supports, D,t and s. Here t is a finite roughness
cutoff <=z; it need not equal D. Enumerate relaxed
frontier nodes at every base residue and depth,
verify per-depth antichain mass <=1, then count
actual roots of each positive certificate with
no eligible prime <t by direct arithmetic.
Also check an elementary finite CRT sieve bound
using a subset of the sieving primes whose product
fits the progression length; this is not the
asymptotic Selberg sieve estimate (3).
Independently trace every actual root, compare
physical clocks and prefix costs to the frontier
certificates, check unique frontier per depth,
(2), and large-final condition p>16D+16.

    z    D    t    roots   frontier certs  actual rough visits  large crossings
    17   40   7    1000           6                 885                0
    31   80   11   2000          18                1580                0
    127 240   17   2000          33                1137                0
    251  80   31   2000          18                 751                0
    997  60   53   2000          10                 432                5
    997  20   53   2000           2                 300               55

All 60 large crossings in the finite controls
satisfy the rough-frontier property, including
the stricter test t=53 in the last control.
Totals: 11000 actual roots, 28 base residues
across controls, 8102 tree states, 8074 new
binary query nodes, 87 frontier certificates,
6294 rough certificate/root incidences,
13631 actual frontier visits, 5085 actual
rough visits, 9053 product crossings, 1947
terminals, 17125 clock and large-label inequality
checks, 8144 wall checks, 44 per-depth mass
checks, 87 elementary CRT sieve checks,
13631 exact weighted frontier coverage checks.
All assertions passed. The finite roughness
cutoffs and moduli do not test the asymptotic
constant or rate in (3)-(6).

## 6. Remaining target

The fixed positive-gap physical-score route is
now excluded, just as full virtual terminal
costs excluded the earlier constant budget
quantile. It remains possible to investigate
vanishing-scale lower bounds for actual
terminal scores or a different direct
deterministic crossing obstruction. The
sieve only gives upper bounds and does not
break the parity barrier. No Lean verification,
twin-infinitude proof, or changes to canonical
Lean targets or sibling branches.
