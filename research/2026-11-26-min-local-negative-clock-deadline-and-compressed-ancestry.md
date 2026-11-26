# Negative-time clock deadlines and compressed ancestry

2026-11-26 JST. Continuation of 165150bb04653e7d7c40b63f3ffec21e252d621a.
Replace literal inverse tick scans by exact jump-to-jump transitions.
The deadline of a stationary inverse state is determined by its two
neighbors, while its possible inverse jumps are determined by two
different integers. Derive a least-prime-factor-weighted time budget
for surviving paths and an exact canonical-line pruning rule.
Paper deductions and independently cross-checked finite diagnostics.
No general extinction theorem or twin-infinitude proof.

## 1. Exact deadlines

Use the even remaining distance b=-u>0, and the reverse tick
index k>=1 (actual tick n=-k). A node (b,j) is a state after
tick -j, immediately before undoing that tick. The candidate
prime set C_k consists of odd prime divisors of k for even k,
and of k+2 for odd k. The source residue for a forward event
is e_k=-1 for even k and +1 for odd k.

Write q(b) for the least odd prime factor of either b-1 or b+1,
ignoring 1. It always exists, since b is positive and even.
For a residue r modulo 2p define

    next(j,r,p)=j+((r-j) mod 2p),

where the remainder is in [0,2p-1]. The first reverse tick at
which identity at b is impossible is exactly

    d(b,j)=min(
       min_(p|b+1, p odd prime) next(j,0,p),
       min_(p|b-1, p odd prime) next(j,p-2,p)
    ).

For all j<=k<d(b,j), F_k(b)=b. At d(b,j), F_d(b)!=b.
The two clock periods give the deterministic bound

    j <= d(b,j) < j+2q(b).                           (1)

This deadline does NOT say that the whole inverse fiber
vanishes there. A nonidentity predecessor may still exist
at the deadline or any earlier tick. It is only the end
of the stationary inverse branch.

## 2. Exact jump-to-jump graph

At a tick k a possible nonidentity predecessor of b is
a=b+p-1. The forward source residue must be e_k mod p,
so the target residue is e_k+1 mod p. Thus the candidate
labels and tick classes are

    p|b,    k=0 mod 2p       (even tick)
    p|b-2,  k=p-2 mod 2p     (odd tick).

All primes here are odd. When b=2 the second divisibility
condition is vacuous; enumerate the odd prime factors of
k+2 in the finite window below instead. In particular the
singular target b=2 causes no infinite branching.

The first nonidentity predecessor after node (b,j) must
occur at one of these ticks k in [j,d(b,j)] inclusive.
For each candidate check that F_k(b+p-1)=b, using the
exact least-prime rule. If the check passes, the next node
is (b+p-1,k+1). All intervening reverse ticks are identities.
No nontrivial predecessor is omitted and no new one is
introduced. A surviving stationary branch through any
finite horizon K exists exactly when K<d(b,j).

For b>2 the number of candidate edges from one node is
bounded by

    sum_(p odd prime dividing b(b-2)) ceil(q(b)/p).   (2)

The two odd-prime factor sets are disjoint, and each relevant
class modulo 2p occurs at most ceil(q(b)/p) times in a window
of length <=2q(b). The same bound applies for b=2 if the sum
uses its finite window candidate set. It bounds candidates,
not necessarily accepted edges. The branch candidates are
thus computed using factorization of b and b-2 rather
than scanning all intervening ticks. The deadline itself
uses b-1 and b+1. These four integers play different roles.

Also, immediately after a reverse jump of label p, the new
state a=b+p-1 satisfies a=e mod p, so q(a)<=p. For p>=5
neither +1 nor -1 mod p is an arrival residue 0 or 2.
Thus the same p cannot be the next nonidentity reverse
jump (irrespective of the number of intervening idle ticks).
This does not forbid reuse after other jumps.

With finite horizon K, the graph exactly enumerates all
possible terminal inverse states and the extinction depth.
It is not an asymptotic bound on the size of the full
inverse graph. A graph state (b,j) determines a unique
forward continuation to the fixed terminal tick; recording
equal nodes would be sufficient if any arise. No equal
jump nodes occurred in the tested controls.

## 3. Weighted time budget

Consider any exact surviving inverse branch from target
b_0 at time -1 through K reverse ticks. Let its nonidentity
jumps be p_i at reverse ticks k_i, and let

    b_i=b_(i-1)+p_i-1,  i=1,...,m.

Then q(b_i)<=p_i. By (1), first jump k_1<=2q(b_0),
successive jump gaps k_(i+1)-k_i<=2q(b_i), and the last
idle tail K-k_m<=2q(b_m)-1. If there is no jump,
K<=2q(b_0)-1 directly. Summing gives

    K <= 2q(b_0)+2 sum_(i=1..m) q(b_i)-1.           (3)

For a given path this can be much sharper than the earlier
K<=3G+2q(b_0)-1, where G=sum(p_i-1). The latter follows
immediately since q(b_i)<=p_i<=3(p_i-1)/2. Formula (3)
retains the least eligible factor at EVERY predecessor,
even when the selected reverse prime is much larger.

Application to a zero-phase canonical termination:
let P>=5 be its last label, b_0=P-1, and initial
canonical distance A>=12. The path before tick 0
is precisely an inverse branch through K=A/2-4,
with b_m=A and G=A-P+1 (the last jump at zero is
not in this inverse branch). Thus (3) requires

    sum_i q(b_i) >= A/4-q(P-1)-3/2.                 (4)

If P-2 is composite, q(P-1)<=sqrt(P-2). As P<=A+1,
the right side is A/4-O(sqrt A).
In particular define

    G_eff=sum_(i: q(b_i) >= (p_i-1)/8) (p_i-1).

Since G<=A and q(b_i)<=3(p_i-1)/2, (4) implies

    A/4-q(P-1)-3/2 <= G/8+(11/8)G_eff
                           <= A/8+(11/8)G_eff,

and hence

    G_eff >= A/11 - (8/11)(q(P-1)+3/2).             (5)

Thus a hypothetical long canonical non-twin zero-phase
ending requires a macroscopic amount of gain at reverse
jumps whose predecessor least eligible factor is comparable
to the label. It cannot be sustained only by large jumps
that have a very small eligible competing prime.

If twins are finite and all predecessor distances are large,
the non-twin condition also gives q(b_i)<=sqrt(b_i+1).
Every event counted in G_eff then has p_i<=8sqrt(A+1)+1.
For such events with p_i>=T, both b_i+-1 have no odd
prime factor below (T-1)/8. This identifies rough states
that would need to carry the long inverse time budget.
The previous upper-sieve/local label capacity methods can
bound individual label contributions but do not bound
all such branches together. Equations (4)-(5) do not
establish that the required macroscopic gain is impossible.
Small labels themselves can be efficient.

## 4. Canonical-line pruning and ancestor extraction

At time -j the half-deficit is h=b/2-j. The nonnegative
height invariant for canonical forward paths allows us
to delete any inverse node with b<2j. For a node (b,j)
the stationary branch visits the states (b,l) with
j<=l<=d(b,j) until the deadline is undone. We may also
truncate this interval at l=b/2. The state at l=d
exists AFTER that tick; only undoing the tick as an
identity is forbidden. This inclusive endpoint matters.

A canonical seed is exactly a state with h=3 and
b=0 mod6, i.e. l=b/2-3. Consequently one can test
whether a whole stationary segment contains a
canonical birth by a single integer comparison:

    b=0 mod6 and j<=b/2-3<=d(b,j),

with the horizon bound l<=K+1 if one is imposed.
Each accepted jump at k must have k<=b/2; its
predecessor b+p-1 at k+1 then also has nonnegative
height, since p>=3. These prunings preserve all
possible canonical origins, because their complete
forward trajectories satisfy the height invariant.
Conversely, if an inverse branch contains such a
canonical state, its exact forward suffix reaches
the target at time -1. If the target is P-1 for a
prime P, it then jumps to zero at tick 0. Positive
distances on the reverse path exclude any earlier
hit of zero. Thus every extracted seed is genuine.

This gives a finite exact ancestry algorithm for
a specified P and a specified upper bound on A.
Even if no ancestors exist within that bound,
unbounded A has not been excluded unless an
extinction proof beyond the bound is available.

## 5. Executed diagnostic

Source research/min_local_negative_deadline_graph_audit.mjs,
commit b1d4042f96ea05a5ad82ae534610d99ac2b69288,
blob b188b3376244941a183570b67337f189d51b1692.
Executed in ECMAScript research runtime, fetched at exact
commit and re-executed with identical output.
Reproduce using
node research/min_local_negative_deadline_graph_audit.mjs
No separate Node or Lean process invoked.

Compare the compressed graph with independent literal
tick-by-tick inverse sets for all 22870 non-twin prime
targets P in [1009,300000], with horizon
min(8192,(P-1)/2-4). Compare exact extinction depth and
final inverse fiber, not just an extinction flag.
All 22870 agree and all are extinct, longest 4315,
as in 91e7cfe and 165150b.

Further compare canonical origins for every prime
P<=601 with the pruned tick method and independently
simulate all 99 canonical seeds A=12,18,...,600.
There are 93 zero-phase seeds and 6 positive-phase
seeds. All 93 zero-phase seeds are recovered exactly
and no spurious origins are reported; all 109 prime
targets agree. A=6 is excluded here because its
canonical birth is at time zero rather than before
the negative suffix. The small controls also exercise
target b=2 and its singular plus-side divisor set.

    literal reverse ticks (all controls)       698484
    accepted literal inverse edges           13560383
    compressed jump nodes                     2586404
    candidate compressed edges                2729146
    accepted compressed edges                 2563425
    deadline checks                           2586404
    branching-bound checks                    2586403
    weighted-time checks                      5172808
    canonical small graph nodes                  8725
    independent canonical forward events          571

All assertions passed. The compression reduces
the number of individual inverse edge visits in
these controls, but not the number of global tick
indices (which are a different unit). No general
runtime complexity claim or speed benchmark.
The largest number of accepted children of a
single node in the controls is 360, illustrating
why bounded branching cannot simply be assumed.
No canonical node was rejected at entry by
negative height in the pruned controls; the
restriction is enforced on stationary segments
and jump windows before creating such a node.
The asymptotic corollaries (4)-(5) are mathematical
deductions; the non-twin canonical terminal
case was not observed in these controls.

## 6. Remaining analytic target

The reverse graph now exposes exactly how long
a state can remain stationary and which labels
can restore it. A proof of full extinction
must rule out branches meeting the time budget
(3) all the way to the canonical birth line.
The derived large required efficient gain (5)
suggests studying the minimum-factor distribution
along such reverse branches, rather than only
their widths or their total support product.
The necessary unboundedness of zero-phase
last labels also remains separate. No uniform
extinction depth, no twin-infinitude proof,
no Lean verification or modifications to
canonical Lean targets or sibling branches.
