# Positive CRT certificates and local query transfer

2026-11-26 JST. Continuation of 834863160ef0540d9d7872fa68bc494cacbae995.
A positive-only certificate tree for actual restricted-clock discovery
paths gives a stronger single-budget factorial bound and a deterministic
short-interval counting inequality. This is a local transfer of the
query method, not a bound on intermediate-label high-height occupation.
Paper deductions and executed finite diagnostics. No Lean verification
or twin-infinitude proof.

## 1. Conditional base and adaptive tree

Let A=A0 disjoint union H be a finite set of admitted odd primes,
3 in A0. Fix a canonical base residue r=0 mod6 modulo

    P0=4 product_(p in A0) p.

This fixes X mod4 and all A0 residues. Run the actual restricted
clock algorithm of 562b8890 in relative coordinates G=u-X,
W=v-(X/2+3). At the next tick j the half-height is
3+W+j-G/2 and the tick parity is fixed by the base residue.
For each admitted prime divisor p of the appropriate defect
2h+1 (even) or 2h-5 (odd), test X=e-G mod p, with e=+1
or -1 respectively. Check the candidates in increasing order.
A positive answer selects this clock; the next source is
u+p-1. A finite scan of 2 max(A) ticks with no winner
certifies a terminal, without advancing the actual time.

All A0 tests are known. For H keep the positive residue of each
discovered prime and the sets of rejected residues for undiscovered
primes. Only a previously untested residue of an undiscovered
prime is a new binary query. Charge a=1/p for either answer.
Fix a total charge budget B>=0 and a target k>=1.
Stop before the first query that would exceed B, at the kth
distinct discovery (success), at a restricted terminal, or
at first arrival with gain >=D for a fixed displacement cutoff.
In case the kth discovery is the event crossing D, count it:
stop immediately at the successful query. This agrees with the
ordinary inclusion of the crossing event.

The binary tree may include impossible all-negative branches
(e.g. every residue rejected at one prime); that only enlarges
the certificate collection. The depth of new queries is at
most floor(B max(H)), and the deterministic segments between
queries have finite length under the displacement stop and
the finite clock scan. No factorization oracle revealing
unknown root residues is used in this definition.

## 2. Positive-only certificate weight

At each successful leaf retain only the k positive equalities

    X=c_i mod p_i,   i=1,...,k,

where all p_i are distinct, together with the base residue
X=r mod P0. Discard every negative restriction. By CRT the
certificate is one residue class modulo m=P0 prod_i p_i.
Use a MULTISET of certificates (different leaves may give
overlapping or identical classes). Every real root with the
budgeted discovery property belongs to its corresponding
certificate. The converse need not hold.

Define weight of a success leaf relative to the base by

    w=prod_i (1/p_i).

For a subtree with remaining budget b and j remaining
discoveries, the sum of future relative weights is <=b^j/j!.
Proof by finite backward induction. A deterministic segment
has no cost or branching. A success leaf j=0 has weight 1.
A failure leaf has weight 0. At a new query costing a<=b,
the negative edge has weight 1, the positive edge weight a.
Each branch has remaining budget b-a; the positive branch
needs one fewer discovery. Thus

    (b-a)^j/j! + a (b-a)^(j-1)/(j-1)! <= b^j/j!

by the binomial theorem. No conditional independence or
success probability approximation is involved.
Consequently for EACH fixed base residue r,

    sum_(successful leaves at r) 1/prod_i p_i <= B^k/k!.  (1)

Over the full seed period of A, conditional on r, each
certificate has probability exactly its weight. By the
union bound (1) gives

    Pr(k discoveries before exhausting B | r) <= B^k/k!.

Average over base residues for the unconditional bound.
This improves [-log(1-B)]^k/k! from 8348631 in the single
budget, kth-discovery stop setting, even allowing B>=1
(use min(1,RHS)). The old joint-budget inequality allows
each band's counter to freeze while other bands continue;
(1) does not automatically yield a stronger product for
that setting because subsequent uncharged unknown queries
can branch. It is important that ALL unknown queries in
the tracked set H consume the single budget before success.

A useful extension (paper only): if disjoint tracked sets
H_i have separate budgets beta_i, all counters continue
until a common transcript stop, and leaves are required
to have EXACT discovery vector (k_i), then the product
potential prod b_i^j_i/j_i! gives sum of positive-only
weights <=prod beta_i^k_i/k_i!. At a query of an already
filled band discard its positive branch; this is valid
for the exact-vector event. If only lower bounds on final
counts are wanted with all budgets enforced throughout,
sum over the allowed exact vectors. This is not the
frozen-budget joint event in 8348631. No numerical test
of the multivariate extension is included here.

## 3. Direct local interval counting

Let I=[R,R+L) be any physical interval of length L>0
with positive canonical roots, and z=max(H).
A certificate of modulus m covers at most L/m+1
integers in I. Its positive product M=prod p_i<=z^k.
For a fixed base class the number of leaves is therefore
<=z^k times the sum of weights in (1).
There are P0/6 canonical base residues. Summing ALL
certificates, including overlaps, gives the deterministic
bound

    # {X in I, 6|X: budgeted k discoveries}
      <= (L+P0 z^k) B^k/(6 k!).                    (2)

No assumption of equidistribution in I, or use of the
full enlarged period as a sampling interval, is needed.
The interval error arises solely from the positive
certificates. Negative restrictions can be arbitrarily
numerous without increasing the modulus.

More precisely, for paths whose actual first k positive
labels have product M<=L/P0, count only those success
leaves with m<=L. For each such leaf L/m+1<=2L/m.
This yields

    # {X in I, 6|X: budgeted k discoveries,
                     prod_(first k labels)p<=L/P0}
      <= 2L B^k/(6 k!).                             (3)

This is a positive-product-sensitive transfer even if
z^k is much larger than L/P0. With any fixed lambda>0,
the cutoff m<=lambda L changes the factor 2 to
1+lambda. If no modulus meets the cutoff the restricted
event is empty. The full-period estimate applies to all
successful paths; the local estimate (3) only to the
stated product subset. Formula (2) covers the rest but
may be much weaker.

For I of length L comparable to y^2, H subset [y,2y]
and a fixed base A0, (2) gives an O(B^2) fraction for
two distinct high discoveries under their total query
budget B. In contrast the sparse-base relay-cap pair
estimate of 43c8442 needs a bound on each low relay
length to sum all candidate displacements. Here the
certificate bound does not need that relay cap.
For a growing base, the two-label error is O(P0 B^2)
on this scale; hence it is o(1) if P0 B^2=o(1).
For one discovery the relative error factor is
1+O(P0/y); thus P0=O(y) and B=o(1) suffices.
These are conditional local bounds for actual paths
having small charged budgets, not unconditional bounds
on discovery counts.

One can choose A0 as the primes below a small cutoff
and track ALL remaining admitted primes. Formula (2)
and the sharper (3) then apply without conditioning
on the huge product of intermediate primes. However
the cost includes all their unknown queries, not just
the top band's. For dense A the available coarea
estimates do not show that total cost is small.
Conditioning instead on all intermediate primes makes
P0 too large for (2). This is the concrete remaining
tradeoff, not an assertion that the transfer solves
the dense-cutoff problem.

## 4. Relation to the prior high-height charge

The quiet-coarea estimate of 2d4882e4 supplies a
pointwise failed-query budget for a band H in [y,2y]
on a height-limited trajectory. Before the kth hit,
adding k/y to this failed budget covers the successful
query costs. Thus whenever the coarea bound itself
is <=c, the k-discovery event is included in (2)-(3)
with B=c+k/y. For an arbitrary physical interval
this bounds discoveries on paths satisfying the
cost condition; it does not bound the population
where the coarea charge is large.

In particular this method separates the two original
obstacles: controlling occupation of the critical
heights and transferring small-charge bounds from
full periods to local slabs. A transfer is now
available for base/product ranges as in (2)-(3).
The high-height small/intermediate relay occupation
condition from 8348631 remains unresolved.
No claim of E S_z^o=o(y), an unrestricted local
termination bound, or twin infinitude.

## 5. Executed diagnostic

Source research/min_local_restricted_positive_certificate_audit.mjs,
commit 015ee46b2622aa32961be1d9e363797e1b9e4fa6,
blob 5bdb0a9b222274da9e78cdd833b11b322e36050a.
Reproduction:
node research/min_local_restricted_positive_certificate_audit.mjs
Executed as ECMAScript in research runtime, fetched at exact
commit, re-executed with identical output. Initial recursive
prototype hit a call-stack limit while scanning deterministic
ticks; replaced by explicit stack of binary branches and
iterative deterministic scan before the successful audit.
No separate Node or Lean process invoked.

For every canonical base residue independently enumerate
the budgeted query tree (including impossible branches),
record every successful positive-only CRT certificate,
and sum their reciprocal product weights. Check (1) for
each base class, count the certificate congruences in
the physical interval, and compare (2)-(3). Independently
enumerate every actual root in each interval using the
true neighbor clock rule and literal relative defect
queries. Test that every actual success is covered by
a certificate with its actual positive product.

Three full enlarged periods, then three shorter local
controls. In the last three H consists of all primes
in [31,62], [103,206], [127,254], respectively.

    P0   B     k   D    length    roots    leaves  actual  CRT count
    12   .55   2   20       420        70       6       6       6
    60   .48   2   40     60060     10010      69     717     769
   420   .38   3   60   1021020    170170     429     429     429
    12   .13   2  124     10000      1667      15       5       5
    60   .12   2  412     30000      5000    1006      54      56
   420   .15   2  508     30000      5000   18711      47      50

CRT count includes certificate multiplicity and may exceed
actual successes. In the three local controls every successful
certificate modulus exceeds the interval length, so (3)
does not cover those successes; (2) and the exact CRT counts
do. The last control's coarse (2) is very loose: the actual
certificate count is 50 but the bound from length plus
P0 z^k is much larger. The numerical result is not evidence
that the coarse error vanishes for growing dense bases.

Totals 191917 actual root/control incidences, 164 base
classes, 23240 enumerated branch states, 23076 new binary
queries, 20236 success leaves, 1258 actual successes,
1315 certificate/root incidences, 43 duplicate covers of
actual successes, 402686 independent clock-oracle checks.
All 1258 actual success coverage checks passed; 1152 actual
successes satisfy the small-modulus cutoff, all in the three
full-period controls. All per-base weight inequalities and
local counting inequalities passed. Reciprocal weights
checked with floating tolerances; congruences and counts
integer. No asymptotic claims inferred from finite controls.

No changes to canonical Lean targets or sibling branches.
