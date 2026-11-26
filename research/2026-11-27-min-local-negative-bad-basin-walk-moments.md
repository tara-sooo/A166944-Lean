# Negative MIN: bad-basin ancestor graphs and uniform walk-moment bounds

2026-11-27 JST. Continuation of 15daec28e699dffffcf3212ec08d52e2737cf320.
Develop a depth-truncated non-twin basin mass and energy estimate,
using an undirected spatial supergraph and its degree moments.
Allow the compression of complete low-label runs into macro edges.
This gives an unconditional bound on the short-depth part of the
bad-basin energy target, and a weaker sufficient mass target that
allows a larger depth. The unrestricted-depth target is not solved.
Paper deductions and finite audit, not Lean verification or a
claim of literature priority.

## 1. Set-up and spatial ancestor graph

Fix B>0 and H=4 floor(sqrt(R)/(log R)^B).
Use canonical roots A divisible by six in [R,2R],
starting h=3. A success reaches first POST-tick
height H with full gain G<=L=floor(H/4).
Since positions decrease, every position of
such a successful path lies in J=[R-L,2R].
All distances are even. Let V be the even
integers in J. For R large these distances
are positive, at scale R, and the physical
time is negative throughout a successful path.

By the mod-30 potential (2021e5a) and the
last-arrival bound (15daec2), a successful
endpoint has a final idle interval of length
at least 9H/16-14. Thus both neighbors have
least prime factor >9H/32-7. Let B_R be the
non-twin centers in V satisfying this latter
roughness constraint. The half-prime upper
sieve of d9f6049, also used in 15daec2, gives

    b_R=|B_R| <<_B R loglog R/log^3 R.           (1)

The factor bound, and hence this set, is
independent of the adaptive event histories.

Form a simple undirected graph on V, including
one self-neighbor per vertex. Add an edge
between a and a-p+1 if the latter lies in V
and odd prime p divides a-1 or a+1. Optionally
drop edges of gain greater than L, since a
successful path never uses such an edge.
The graph ignores the clock and least-prime
priority, so it is a supergraph of all actual
spatial event paths within the slab. Its
degree D(a), counting a self-neighbor once,
satisfies

    D(a) <= 1 + omega(a-1)+omega(a+1)
                +omega(a)+omega(a-2).           (2)

Here omega counts distinct prime factors.
Indeed an incoming event of label p from
a+p-1 requires p|a (minus) or p|a-2 (plus).
Every label determines its possible
predecessor uniquely. Outgoing labels are
factors of the two neighbors.
Repeated/overlapping edges only reduce D.

Let F_d(a) be the number of graph walks
of length exactly d starting at a, allowing
self-neighbors. Then F_0=1 and
F_(d+1)(a)=sum_(b adjacent a) F_d(b).
By symmetry the count also equals the number
ending at a. The successful roots arriving
at a via at most d events inject into these
walks: pad their actual spatial path with
self-neighbors at its end. Distinct roots
have distinct starting vertices even when
they later coalesce. Therefore the mass
m_a^(d) of such roots satisfies

    m_a^(d) <= F_d(a).                          (3)

This is an upper bound, not an approximation
to the actual reverse tree. In particular
the walk graph permits upward moves, repeated
vertices, and time-inconsistent histories,
none of which are required to be physical.

## 2. General graph walk-moment inequality

For any finite undirected graph with symmetric
0/1 adjacency and positive D(v) (self-loops
may be used), let S=sum_v D(v). Take the
random walk with uniform choice among each
vertex's D(v) neighbors, with initial law

    pi(v)=D(v)/S.

This is stationary by reversibility, including
self-neighbors counted once. For d>=1,

    F_d(v)=D(v) E_v[prod_(i=1..d-1) D(X_i)],

where the empty product is one. This follows
by summing all length-d transition paths, whose
probability from v is prod_(i=0..d-1) D(X_i)^(-1).

For q>=1 Jensen followed by generalized Holder
gives

    sum_v F_d(v)^q
      <= S E_pi[D(X_0)^(q-1)
                    prod_(i=1..d-1) D(X_i)^q]
      <= S E_pi[D(X_0)^(dq-1)]
       = sum_v D(v)^(dq).                       (4)

In the second inequality use Holder weights
(q-1)/(dq-1) for i=0 and q/(dq-1) for each
i>=1; they sum to one, and all X_i have
the same stationary marginal. Zero weights
are omitted. The case d=q=1 is an identity.
No independence of successive X_i is used.
This graph inequality works for all real q>=1,
though integer q suffices below.

For any subset U of size b, and 1<=r<=q,
another Holder inequality and (4) give

    sum_(v in U) F_d(v)^r
       <= b^(1-r/q) (sum_v D(v)^(dq))^(r/q).      (5)

The dependence on q and d in (4) is important:
one degree moment of order dq suffices. Iterating
a crude operator norm with increasing exponents
would give a much weaker dependence on d.
The same inequality with d=0 holds trivially.

## 3. Uniform degree-moment bound

We give an elementary bound valid at growing
moment orders, without invoking a distribution
limit for omega. For any shifted integer
argument n occurring in (2), sum over a in V.
Since the arguments range in positive integers
up to O(R), without repetition,

    sum_a 2^omega(n) <= sum_(n<=O(R)) tau(n)
                     << R log R.

Here tau is the divisor count, and the last
bound follows from sum_(uv<=X) 1 <= X sum_(u<=X)1/u.
Thus under the uniform distribution on V,
whose size is comparable to R, the tail of
omega(n) satisfies

    Pr(omega(n)>c loglog R+u) << exp(-c' u)

for absolute positive c,c', uniformly in
the displayed shifts. For any real s>=1,
integrating this exponential tail, or
bounding its s-norm by the next integer
factorial, gives

    (E omega(n)^s)^(1/s) << loglog R+s.

Minkowski and (2) prove, uniformly in s>=1,

    (|V|^(-1) sum_a D(a)^s)^(1/s)
                         <= C(loglog R+s).      (6)

Combining (4) with (6),

    (R^(-1) sum_a F_d(a)^q)^(1/q)
                   <= [C'(loglog R+dq)]^d       (7)

for d>=1, q>=1, R sufficiently large. Constants
are absolute; the normalization change from
|V| to R is absorbed in C'. For d=0 use F_0=1.
There is no uniformity assumption about the
set of endpoints in (5).

## 4. Non-twin mass and energy at growing event depth

Define N_bad(d)=sum_(a in B_R) m_a^(d) and
C_bad(d)=sum_(a in B_R) (m_a^(d))^2.
They count only successful canonical roots
with at most d completed events before H.
By (1), (3), (5), (7), for fixed q>=2,

    N_bad(d) <= b_R^(1-1/q) R^(1/q)
                      [C'(loglog R+dq)]^d,       (8)
    C_bad(d) <= b_R^(1-2/q) R^(2/q)
                      [C'(loglog R+dq)]^(2d).    (9)

These inequalities are unconditional and
hold for every depth parameter. They also
apply to arbitrary subsets of such successful
roots. They bound bad-basin mass and energy
directly, not merely the number of endpoints.

Write l2=loglog R and l3=logloglog R. If

    d <= kappa l2/l3

for fixed kappa>=0 and fixed q, then the
bracket to power d in (8) is
(log R)^(kappa+o(1)), uniformly in that
depth range. Hence

    N_bad(d) <= R (log R)^(kappa-3+3/q+o(1)),
    C_bad(d) <= R (log R)^(2kappa-3+6/q+o(1)).     (10)

The loglog factor in (1) is absorbed in
the o(1) exponent. Choose fixed q large
enough after fixing a margin in kappa.

* For every fixed epsilon>0, at depths
  d <= (3-epsilon) l2/l3 (when nonnegative),
  N_bad(d)=o(R).
* For every fixed epsilon>0, at depths
  d <= (5/2-epsilon) l2/l3 (when nonnegative),
  C_bad(d)=o(R log^2 R).

The second result meets the proposed
bad-energy target for the truncated cohort.
It does not bound the energy of the roots
having larger depth. The first result is
sufficient for the twin witness without
requiring the full quadratic energy target.

More generally (10) shows that for any
fixed beta>=0 and kappa<3-beta,
N_bad(d)=o(R/log^beta R).
Consequently a lower bound
N_success(d)>>R/log^beta R at that depth,
along unbounded R, would imply twin
infinitude. The permitted beta,kappa
must be chosen so the hypothesis is not
already impossible from upper bounds;
see section 6.

There is no bound of the required form
on N_success(d) in this note. In particular
the total gain cap O(H) does not imply
d=O(l2/l3).

## 5. Compress arbitrary low-prime runs

Use the complete spatial walls of 0116e3e:
in half-distance x=a/2, a wall J for an
odd-prime alphabet P satisfies
(-J mod p)<=(p-3)/2 for all p in P.
A decreasing jump with label in P cannot
cross this wall. If M is the maximum gap
between consecutive walls, any contiguous
run of P-labeled events has full gain at
most 2(M-1), regardless of the clocks
and number of events in the run.

Fix a low alphabet P (e.g. primes <=5,
with exact half-gap M=9). For a successful
path, call all other labels high. Compress
each low run and the immediately following
high event into one edge, and allow one
last low-only edge after the final high
event. A path with at most k high events
has compressed length at most k+1, even
if its ordinary depth is much larger.

Build a symmetric macro supergraph on V.
Include self-neighbors and edges between
a and a-d, d even, 0<=d<=2(M-1).
Also include a -> a-d-p+1 for every such d
and prime p outside P dividing a-d-1 or
a-d+1, whenever both endpoints are in V.
Use the undirected versions of all edges.
The spatial edge does not assert that the
low run of gain d is actually possible.
Every compressed actual successful path
is contained in this graph.

The new degree D_M(a) has the bound

    D_M(a) <= 1+2(M-1)
         + M[omega(a)+omega(a-2)]
         + sum_(i=0..M-1)
                 [omega(a-2i-1)+omega(a-2i+1)].

The incoming high label divides a or a-2,
independently of the preceding low-run gain.
There are at most M choices for that gain.
For M<=R/8, all shifted arguments here
remain positive and O(R), so (6)'s same
elementary argument and Minkowski yield

    ||D_M||_s <= C M(loglog R+s).               (11)

The walk-moment inequality is unchanged.
For roots with k high events, replace d
by k+1 and C' by C'M in (8)-(9).
For a fixed P this leaves both thresholds
in (10) unchanged asymptotically:
the factor M^(k+1)=(log R)^o(1) at the
indicated depth. Thus the mass and energy
bounds apply to the number of non-low
events, not necessarily total events.

One can also let P grow with R. For
M=(loglog R)^o(1) the same exponents hold.
For instance include primes <=z where
z=o(logloglog R); M<=prod_(3<=p<=z)p
<=exp(O(z)) by the elementary Chebyshev
bound, so this condition is met. More
generally if M<=(loglog R)^eta for fixed
eta>=0, the exponent kappa in (10)
is replaced by (1+eta)kappa.
All these conclusions require a bound
on the remaining high-event count.
The method does not yet supply it
for every successful root.

## 6. Necessary depth range and conditional endpoint excess

The same Holder estimate applies to the
entire successful cohort. Its endpoints
are either non-twin rough centers (1)
or actual twins in J. The dimension-two
upper sieve used in 4649be4 bounds all
twins in J by O(R/log^2 R), so their
union has size O(R/log^2 R).
Consequently the total mass of successes
with depth d<=kappa l2/l3 satisfies

    N_success(d) <= R (log R)^(kappa-2+2/q+o(1)).

In particular if kappa<2, choosing fixed
q large gives N_success(d)=o(R), even
without any finite-twins hypothesis.
Thus the proposed positive-density
short-depth success target cannot be
achieved at arbitrarily small depth.
The same holds for macro depth with
fixed low alphabet (or M=l2^o(1)).

There is a potentially useful window
2<=kappa<3: if a positive fraction
of all roots succeeds within that
ordinary or macro depth along unbounded
slabs, the bad part is o(R) by (10).
The twin part then has positive root
mass. In fact by (5) with r=1 and
q>1, for every fixed delta>0 its
distinct endpoint count is at least

    >> R/(log R)^(kappa+delta)

for sufficiently large R on the
sequence (choose q large enough that
kappa q/(q-1)<kappa+delta, absorb the
o(1) factors). This stronger twin
abundance conclusion is conditional
on the stated mass lower bound, and
does not follow from the degree moment
bounds alone.

If the next objective is just infinitude,
one need not bound the entire C_bad.
Decompose the successful population into
short and long compressed paths. By (10),
for kappa<3, it is enough to show positive
density of the short successes, or to
bound the long-path bad mass by o(R)
and obtain a positive-density total
success lower bound. This differs from
proving C_bad=O(R log^2 R) over all
paths: with the geometric bound on an
endpoint multiplicity <=floor(L/6)+1,
a long-path mass bound o(R) need not
give the full quadratic energy bound.

## 7. Executed finite audit

Source research/min_local_negative_bad_basin_walk_moments_audit.mjs,
commit bcedbe8a0aef632d62d81c4c441d825ece07024e,
blob 7f56820aeca6347ea88f33c3306188954743359f.
Executed in ECMAScript research runtime, fetched at
the exact remote commit and independently re-executed
with identical output. Reproduce using node.
No separate Node or Lean run.

Use H=4 floor(sqrt(R)/sqrt(log R)), gain
budget floor(H/4), all canonical roots
in six slabs R=3000,12000,48000,192000,
480000,1000000. Stop at the gain cap.
Enumerate actual paths and successes,
classify terminal non-twin rough centers,
and retain separate ordinary and
macro depth-truncated masses and energies.
For the first three slabs independently
build the ordinary and P={3,5} macro
supergraphs on all even positions in J,
with actual low-run wall gap M=9.
Check path coverage, degree bounds,
walk-moment inequalities for lengths
1..6 and q=1,2,3,4,8, and restricted
moments r=1,2 whenever q>=r. Each macro
depth threshold k in the audit counts
roots with high-event count+1<=k,
including an allowance for the terminal
low-only edge even if it is unnecessary.

    canonical roots                    289172
    completed events                  2541188
    successful roots                   100550
    successful non-twin roots            7593
    independent graph controls               6
    adjacency entries incl. self      1123504
    degree checks                       63124
    graph walk moment checks              180
    restricted moment checks              324
    ordinary path edge checks            9186
    macro path edge checks               5211
    low-run gain checks               1515353
    basin upper bound checks             9522

All assertions passed. Example data:

    R       successes  bad mass  bad centers  C_bad  max depth(success)
    3000        149         9         4          23        5
    12000       535        26        10          78        7
    48000      2432       203        43        1423       14
    192000     9878       790       134        8284       23
    480000    26965      2140       275       29644       34
    1000000   60591      4425       519       72195       38

For R=1000000 the 6-event depth
truncation gives 32702 successes,
2348 bad roots, bad energy 15634.
With 6 macro steps (at most 5
non-{3,5} events plus terminal low
run), these numbers are respectively
47904,3501,39405. Full bad energy
is 72195; the largest bad basin
has mass 40, versus largest twin
basin mass 43.
The truncated graph envelope counts
many nonphysical walks; it is not
claimed numerically sharp. The
asymptotic depth thresholds are very
small at these finite R, so the
6-event controls are not empirical
verification of the asymptotic regime.
The full finite bad-energy values
do not imply an unrestricted
asymptotic bound.

## 8. Remaining objective

The conditional-on-depth part of the
desired C_bad estimate is obtained
as a uniform unconditional inequality
on that truncated population. The
macro version removes all dependence
on the number of events from a fixed
small-prime alphabet, and even allows
very slowly growing alphabets.
Neither the depth distribution of
successful roots nor their required
mass lower bound is established.
The two key open directions are
controlling the long-path portion
of the non-twin basins using the
actual clocks rather than the
spatial supergraph, and proving
a substantial low-gain success
population at near-square-root
height. No twin-infinitude proof,
Lean verification, or canonical
Lean target/sibling branch changes.
