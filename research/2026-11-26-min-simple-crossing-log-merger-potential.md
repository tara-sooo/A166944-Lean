# Logarithmic merger potential and long-window stable transport

2026-11-26 JST. Continuation of 5c2fc05b7c935b232dc3895b55a90df14996a86d.
User requested focusing on a full-history invariant. The new invariant
controls actual merger growth over ALL generations, including windows
whose physical span grows with R. It does not close stable transport,
prove E=O(R^2), or prove twin infinitude. Paper deductions, executed
finite audit, no Lean verification or external novelty claim.

## 1. Exact coalescence forest and heavy/light budget

Keep the common-boundary MIN with M=R/12+O(1) seeds X multiples of 6
in [R,3R/2], state (X,X/2+3), stop at first U>=2R.
All occupied internal pre-event states s=(u,v) have one successor
(or an exit), u strictly increases. b(s) counts seed origins.
Partition incoming origins by predecessor state and, if s is a seed,
a singleton injection. These groups are disjoint. Exact state groups
never split once coalesced; choosing a heavy incoming group of maximum
mass (ties fixed arbitrarily), define a(s)=b(s)-max incoming mass.
A light arrival is any origin in a nonchosen group; it includes a
nonchosen singleton injection. Each light arrival at least doubles
that origin's group mass, so it occurs at most floor(log_2 M) times.
Consequently

    sum_s a(s) <= M log_2 M.

Alternatively, the entropy gain
    H(s)=b(s) log b(s)-sum_i m_i log m_i
is nonnegative and at least (log 2) a(s), because each nonmax group
m_i<=b(s)/2. Summing over the acyclic graph cancels internal edge terms;
seed entropy is zero and the remaining sum is the entropy of the
partition by exiting edges (not necessarily distinct exit states).
Thus sum H(s)<=M log M. In particular if an incoming maximum is at
most b(s)/2, b(s)<=2a(s). On non-twin sources q(u)<=sqrt(2R+1), so

    sum_(such balanced non-twin s) b(s)q(u)
        <=2sqrt(2R+1) M log_2 M=o(R^2).

The actual wait contribution is at most twice this bound. More generally
if a(s)>=eta b(s), the bound is O(R^(3/2) log R/eta), for any eta>0.
This is an all-depth bound on actual traffic at substantial mergers,
not a degree estimate for possible edges. Pure contraction of mass
at exact states is impossible without exits: merging preserves total
mass and increases its square sum. The useful budget is cumulative
relative growth, not a putative one-step L2 contraction.

## 2. Geometric short windows and all-depth young-origin traffic

Along any path, for every starting offset x on the path, the non-twin
pre-event offsets in [x,x+D) form a consecutive segment (a twin at
u>=R doubles and exits). Since q(u)<=p and p<=3(p-1)/2, summing over
all but the final event telescopes physical gains to less than D.
At the final non-twin pre-event offset q<=sqrt(2R+1). Hence

    sum_(non-twin visits in [x,x+D)) q(u)
        <= W(D):=3D/2+sqrt(2R+1).

Similarly actual waits sum to at most 2W(D). This bound does not
require all edges to be efficient, nor bound the number of events.

Retain only heavy internal predecessor edges. They form disjoint
directed chains: there is at most one heavy parent and at most one
successor for each state. For each origin, its age is physical offset
increase since injection or the most recent light arrival, whichever
is later. The q-weighted contribution of visits of age <L, over all
origins and all generations, is at most

    (M+sum_s a(s)) W(L) <= M(1+log_2 M) W(L).

For L=floor(R/log^2 R), this is O(R^2/log R)=o(R^2)
(the R^(3/2)log R term is lower order). This charges fresh cohorts
regardless of when they merge, unlike a fixed initial-generation bound.
It does not bound the q-weighted traffic of old cohorts.

## 3. Stronger rolling logarithmic potential

For an individual origin, index its internal states s_i=(u_i,v_i)
and masses b_i=b(s_i), with b_-1=1. Set
    lambda_i=log(b_i/b_(i-1))>=0.
Exactly sum_i lambda_i=log b_last<=log M.

For D>=1 define the recent logarithmic growth at an origin visit i by
    Gamma_D(i)=sum_(j<=i, u_j>u_i-D) lambda_j.
If the origin has a previous state t with u(t)<=u_i-D, let t be the
latest such state; then Gamma_D(i)=log(b_i/b(t)). If none exists,
it equals log b_i. The latter origin is recent, of physical age
u_i-X<D. The sum of q over its recent visits is <=W(D).

By exchanging the order of the two finite sums, each lambda_j can
contribute to Gamma_D(i) only for u_i in [u_j,u_j+D). Section 2 yields

    sum_(non-twin i) q(u_i) Gamma_D(i) <= W(D) log M.

Summing over ALL M origins proves the central invariant

    sum_(origins, non-twin visits) q(u) Gamma_D <= M W(D) log M.

It is uniform in the number of events, and in the choice of D.
For delta>0, define an origin visit to be stable-old if its latest
ancestor at or before u-D exists and Gamma_D<=delta. The q-weighted
mass of all other visits is bounded by

    T_bad(D,delta) <= M W(D)(1+log M/delta).

The first term is the recent-origin charge and the second follows
from the logarithmic invariant by Markov's inequality. Thus choose

    D=floor(R/log^3 R),   kappa=ceil(log R),
    delta=log(1+1/kappa).

Then uniformly over all trajectories

    T_bad(D,delta)=O(R^2/log R+R^(3/2)log^2 R)
                 =O(R^2/log R)=o(R^2).

The wait contribution of these visits is at most 2 T_bad. In
particular this actually eliminates one entire portion of the
full-history weighted traffic target. A recent merge of comparable
groups, or even a relative mass growth exceeding 1+1/kappa across
a mesoscopic window, cannot by itself carry the twin-free time demand.
Under the finite-twin hypothesis, sufficiently large R has no twin
offsets in its slab, so all origins have elapsed wait >=R/4-3.
The stable-old visits alone must then have q-weighted traffic >>R^2.
No short-crossing assumption is used in any of these bounds.

## 4. Exact single-ancestor representation of stable mass

Take delta<log 2. A stable-old origin cannot traverse any light
arrival after its latest ancestor at or before u-D: such a light
arrival doubles mass, contradicting Gamma_D<=delta. Therefore all
stable-old origins of a given state s belong to a SINGLE earlier
state t(s): follow the unique heavy-parent chain backward, stopping
at the first state at or before offset u(s)-D. If it does not exist,
or b(s)>exp(delta)b(t(s)), there is no stable-old origin at s.
Conversely if it exists and the mass ratio meets the bound, all
origins through t(s) reach s on that chain with that same ancestor
and growth ratio. Hence the exact stable mass is

    b_st(s) = b(t(s)) if t(s) exists and b(s)<=exp(delta)b(t(s)),
              0 otherwise.

For fixed u, the nonzero ancestors t(s) of distinct states at u
are distinct by forward determinism. The whole cohort at each
stable state is known to relative error <=exp(delta)-1=1/kappa.
An offset-space window may contain a long jump, so no lower bound
on the number of steps in that window is implied.

Write B_st(u)=sum_v b_st(u,v). The previous reduction is now

    sum_(non-twin u) q(u) B(u)
      = sum_(non-twin u) q(u) B_st(u) + O(R^2/log R).

The new error estimate is proved, not hypothesized. Thus it suffices
to bound the stable mass term. Using the earlier H_1 bound
<<R^(3/2)/log^3 R, even stable-old mass at offsets with
B_st(u)<=sqrt(R) log^2 R has weighted traffic O(R^2/log R).
If twins are finite, the remaining demand MUST be carried by offsets
with greater stable-old traffic; each such state inherits nearly
all its mass from a unique earlier state over span D. This identifies
the difficult contribution as already-concentrated, nearly
mass-preserving transport, not recently accumulated merger growth.
The stable term remains uncontrolled. The logarithmic invariant
alone is not an estimate of E=sum B(u)^2, which includes cross-phase
pairs, and does not imply E=O(R^2).

## 5. Two failed simplifications

Literal tick GCD controls (both from legitimate deficit-6 seeds):
- Seeds 1002 and 1014 reach (1014,510). Intermediate seed 1008
  instead stays at u=1008 until tick 530, then jumps to 1060.
  Thus a basin's seed origins need not form an interval.
- At tick 529, the seeds 1008 and 1014 occupy offsets 1008 and
  1020 respectively. At tick 530 they occupy 1060 and 1020:
  strict overtaking without coalescence. Therefore ordering by
  initial offset is not preserved even while both paths are active.
  A proof using noncrossing paths or interval basins cannot be used
  without a different, proved order.

There is also a generic graph-theoretic obstruction to proving the
stable-term estimate from entropy and degree moments alone. A directed
chain of consecutive vertices with one seed injected at each of the
first M vertices, followed by M further vertices, has bounded
internal degree, entropy gain <=M log M, and one mass-M cohort
carried along the entire final chain. Its cumulative square mass is
Omega(M^3). This is NOT a legal MIN example; it shows why clock and
divisibility information on the long stable part is essential.

## 6. Executed audit

Source research/min_simple_merge_potential_audit.py, commit
3095c4583e17b14104c842b95115a1c1b645b6d7, Git blob
d114b4743dfbc4e9eb270bee9dd5026ebbaa4e1c, matches local executed
source and remote content read back exactly. Stdlib plus the
inherited min_simple_crossing_audit.py. Run:

    python research/min_simple_merge_potential_audit.py 1000 10000 100000 1000000

The graph was built by actual modular clocks, with independent
literal GCD ticks for the two controls. Per-origin replay checked
mass doubling, exact light sum, entropy telescoping (floating
comparison), all young-traffic and logarithmic inequalities,
and equality between stable mass determined by origin histories
and the heavy-chain single-ancestor reconstruction (integer ratios).

    R       M     light visits  max light per origin  heavy chains
    1000    84      54             2                    71
    10000   834     880            4                    646
    100000  8334    9989           4                    6407
    1000000 83334   115858         5                    63884

For the rolling windows D and kappa as defined in section 3:

    R        D    kappa   total non-twin Bq   stable Bq   recent Bq   growing Bq
    1000     3     7       3692               2041        673         978
    10000    12    10      127766             64615       19434       43717
    100000   65    12      2971094            871128      797813      1302153
    1000000  379   14      77952797           14285295    31689799    31977703

At R=1000000, non-twin balanced-merger Bq=2123056, all non-twin
wait=66822800, stable-old wait=11546978. For the longer light-age
window L=5239, q-weighted young/old=77078235/874562. Old maximum
offset mass=214 and maximum observed non-twin heavy age=12018.
Stable states counted including twin terminals: 17763. These are
finite measurements, not evidence of a uniform upper bound on
long stable transport; the asymptotic error bound can be much
larger than actual total traffic at tested scales.

Next: bound high-q stable transport by actual clock/number-theory
constraints on the unique long heavy ancestor. The surviving
difficulty is a large cohort already formed earlier and carried
for a long distance with little new mass. Degree-only, order-only
and recent-merger estimates cannot resolve it by themselves.
No twin-infinitude proof or full-history energy bound yet.
