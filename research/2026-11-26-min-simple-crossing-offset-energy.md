# Common-boundary passage energy and elementary semiprime supply

2026-11-26 JST. Continuation of 6e24c0d7c8009d1e68a57e76597b5f03d0051a3b.
Paper deductions and executed finite graph audit. No Lean verification, external novelty claim, or proof of twin infinitude.

## 1. Common stopping boundary and exact merger ledger

Let R be a large positive integer, seeds X in [R,3R/2] with 6|X,
initial state (X,X/2+3), and stop at the first event with U>=2R.
Use only pre-event states u<2R in the directed graph. The seed count
M=R/12+O(1). The graph is acyclic (u strictly increases), with at most
one outgoing edge per state, and common stopping boundary makes every
suffix shared after coalescence.

Let b(s) count distinct seed origins visiting s, U count occupied states,
S=sum b(s), Q=sum b(s)^2. Exact mean N=S/M, and S^2<=UQ.
If a path visits no twin center then its elapsed time is >=R/4-3
and the square-root potential gives
N>(sqrt(2R+1)-sqrt(3R/2+7))/2.
Thus UQ=o(R^3) along unbounded R suffices for twin infinitude.

For an internal state s, let L(s) be its remaining pre-event path length
including s. Partition all incoming origins by incoming edge, plus a
singleton if s is a seed. These sets are disjoint by acyclicity and
determinism. Let c(s) count unordered pairs of origins belonging to
different incoming groups. Each such pair first coalesces at s.
Therefore exactly

    Q = S + 2 sum_s c(s)L(s).

Partition c into same incoming label, distinct labels, and new-seed
injection. Same label implies same predecessor offset, though predecessor
times may differ. For v1<v2 at that offset, next-state coalescence is
equivalent to no active clock in (v1,v2]. In particular v2-v1<2q(u),
where q(u) is the smallest prime factor of either neighbor. This is
a local constraint, not a bound on the masses of the incoming groups.

## 2. Elementary arithmetic supply

For even R<=u<2R, let q(u)=min(lpf(u-1),lpf(u+1)); lpf denotes least
prime factor, including lpf(p)=p. Exclude twin centers from the following
sums. A composite neighbor n has lpf(n)>=q(u) and n<=Y=2R+1.
Each odd n is a neighbor of at most two offsets, so for fixed a>0

    H_a(R)=sum_(non-twin u) q(u)^a
        <=2 sum_(composite n<=Y) lpf(n)^a
        <<_a R^(1+a/2)/log^2 R.

Proof: n with lpf(n)<=Y^(1/3) contribute O(Y^(1+a/3)).
For p=lpf(n)>Y^(1/3), n=pk with k prime, p<=k<=Y/p, since
three factors >=p would exceed Y. Chebyshev's elementary prime
upper bound gives at most O(Y/(p log Y)) choices of k uniformly
in this range. For a=1 and a=2, the sum over p is bounded by
O(Y/log Y) times sum_(p<=sqrt Y) p^(a-1), giving the stated result
by Chebyshev. For arbitrary fixed a>0 the same estimate of the
prime power sum follows by dyadic decomposition, since the
geometric exponent a is positive. The small-factor contribution
is lower order for every fixed a>0. No twin distribution or
two-dimensional sieve is used.

## 3. New sufficient conditions (no distinct-state estimate required)

Let B_R(u)=sum_v b(u,v), the number of origins passing through u.
An origin visits an offset at most once. Define passage energy

    E_R=sum_u B_R(u)^2,    Bmax_R=max_u B_R(u).

Let K_R be the number of seeds reaching 2R without a twin pre-offset.
The envelope gives final v>=R, initial v<=3R/4+3. Each non-twin event
wait w<=2q(u) since every neighboring factor has its own competing
clock. Sum over the K_R paths, then enlarge to all origins:

    K_R(R/4-3) <= 2 sum_(non-twin u) B_R(u) q(u)
              <= 2 sqrt(E_R H_2(R)),
    K_R(R/4-3) <= 2 Bmax_R H_1(R).

Consequently

    K_R/M << sqrt(E_R)/(R log R),
    K_R/M << Bmax_R/(sqrt R log^2 R).

Either E_R=o(R^2 log^2 R) or Bmax_R=o(sqrt R log^2 R) on any
unbounded R subsequence implies K_R/M->0 and infinitely many twins.
In particular E_R=O(R^2) suffices, as does Bmax_R=O(sqrt R log R).
Equivalently, under finite twins, all sufficiently large R must satisfy

    E_R >> R^2 log^2 R,    Bmax_R >> sqrt R log^2 R.

This is a reduction to offset-only traffic: no need to bound U or
number of time phases separately. It does not prove the required
traffic upper bounds. E_R is larger than Q, not interchangeable with it.
If P_R=max_u #{v:b(u,v)>0}, then Q<=E_R<=P_R Q by Cauchy-Schwarz.
A further variant uses Holder with a>1 and conjugate t=a/(a-1):
    K_R/M << (sum_u B_R(u)^t)^(1/t) /
              (R^(3/2-1/a) log^(2/a) R).
This follows directly from H_a; a=2 and a->1 (the separate max
argument above) yield the displayed energy and max criteria.
The direct weighted condition sum_(non-twin u) B_R(u)q(u)=o(R^2)
also suffices; it can be easier than an unweighted energy bound
if large traffic mainly occurs at small q.

## 4. Exact flux recurrence and next open step

Define F_p(x)=sum of b(x,v) over those states whose chosen next
label is p. For each internal even u, summing incoming edges gives

    B_R(u) = 1_(u is a seed)
          + sum_(p odd prime dividing u or u+2, x=u-p+1>=R) F_p(x).

Each eligible p gives at most one predecessor offset. If p divides u
it is the minus arrival, if p divides u+2 it is the plus arrival
(the two are disjoint for odd p). Also sum_p F_p(x)=B_R(x).
For every integer cut y with 3R/2<=y<2R, every origin has exactly
one edge x<=y<x+p-1 crossing that cut, so the sum of F_p(x) over
those crossing edges is exactly M. This is an unconditional flux
constraint, but dropping the clock-dependent choice of p loses
information. It does not bound repeated short-edge traffic.
To close the proof it would suffice to establish either passage-energy
bound above from the true clock selection. The next concrete direction
is to control high-traffic offsets with large q, using this exact
flow recurrence and the arithmetic supply estimate rather than
global phase cardinalities. No independence assumption.

## 5. Executed audit

Source research/min_simple_graph_audit.py at
c67edce80934ad0aeb63f4513300f84efad06a6f, blob
96001c476e365dfd316aeb8d54b4fe1dc5ac553d, matches local executed file.
Uses stdlib and inherited min_simple_crossing_audit.py.
Run:
    python research/min_simple_graph_audit.py 1000 10000 100000 1000000

Exact graph mass propagation, suffix length and first-merger ledger
identities verified. Independent literal tick-by-tick GCD path counts
checked at R=1000 and R=10000. Wait inequalities and offset-energy
comparisons verified at all four sizes.

    R        M      U       S        Q          E          Bmax P   K
    1000     84     240     614      2966       4110       17   4   0
    10000    834    2649    12026    166544     261482     54   9   0
    100000   8334   27708   173682   5352868    8091842    212  11  0
    1000000  83334  294268  2647845  174125585  251512635  490  12  0

    R        H1       H2          sum non-twin Bq
    1000     2404     25746       3692
    10000    33765    1092255     127766
    100000   485138   52342184    2971094
    1000000  7714010  3009969218  77952797

At R=1000000, Q-S=2*(70066471+7830001+7842398), same-label,
distinct-label and new-seed suffix-weighted pair contributions,
respectively. Shares 81.7208%, 9.1324%, 9.1468%. These reproduce
the previous conversation's graph statistics. E/R^2 decreases
from 0.00411000 to 0.00025151 over the four sizes.
All sampled origins hit a twin, so the K>0 case is not exercised
by these graph data. Arithmetic supply proof is independent of
observations. The flux recurrence in section 4 is a paper deduction,
not separately instrumented in this audit.
