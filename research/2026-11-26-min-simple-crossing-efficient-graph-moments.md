# Efficient-edge degree moments and finite-generation transport

2026-11-26 JST. Continuation of a96ce715dd042568afb744790398f63e5467afd5.
Paper deductions and executed finite audit. No Lean verification or proof of
twin infinitude. Unlike the previous rough-supply estimate, the new bounds
control actual origin traffic with a fixed efficient-history depth, not
just counts of possible source offsets. They do not control unbounded depth.

## 1. Efficient events carry the time demand

Use the common-boundary seeds X in [R,3R/2], 6|X, state (X,X/2+3),
and stop at U>=2R. On even non-twin u let q(u)=min(lpf(u-1),lpf(u+1)).
Fix C>=1. An efficient event means p<=C q(u). For an inefficient event
on a twin-free path, w<=2q<2p/C<=3(p-1)/C. The whole physical gain is
<3R, hence total inefficient wait <9R/C. Since total wait >=R/4-3,
efficient events supply at least (1/4-9/C)R-3. For C=100 this is
0.16R-3. This applies to each twin-free origin, without any assumption
about mergers. The observed C=16 graph below is only a diagnostic;
C=100 is used for the stated positive time-demand margin.

## 2. A phase-free efficient candidate graph

Vertices are even offsets in [R,2R). Draw the edge x -> y=x+p-1 for
each odd prime p dividing x-1 or x+1 with p<=C q(x), x non-twin, and
y<2R. Both sides cannot supply the same odd p. One can also include
exit destinations by extending the vertex set to [R,3R) for sufficiently
large R (C fixed), keeping the same restriction on source x; every
estimate below remains valid. Any actual efficient non-twin internal
edge belongs to this graph, but the converse is not asserted.
Write d_+(x), d_-(y) for the candidate out- and in-degrees, and
d_{+,T},d_{-,T} for the corresponding degrees restricted to p>=T.

For every fixed integer k>=1,

    sum_v d_+(v)^k + sum_v d_-(v)^k <<_{C,k} R.

More quantitatively, for T>=7,

    limsup_(R->infinity) R^(-1) sum_v (d_{+,T}^k+d_{-,T}^k)
      <<_{C,k} (1+log log(3T))^(k-1)/log^2 T.

Here T is fixed for the limsup. These are uniform average bounds, not
uniform pointwise bounds. For any fixed a>0 and T>=a sqrt(R) we also have

    sum_v (d_{+,T}^k+d_{-,T}^k) <<_{C,a,k} R/log^3 R.

### Proof

An efficient non-twin source has p<=C sqrt(2R+1). For sufficiently
large p (with threshold depending only on C), q(x)>=p/C.
If the selected neighbor is n=pm, its other neighbor is pm+/-2.
All odd prime factors of m and pm+/-2 are >=p/C. For R sufficiently
large p<n, although the sieve only needs the roughness. The explicit
two-form upper sieve proved in the inherited record-displacement-and-supply
note, section 3, gives O_C(R/(p log^2 p)) possibilities for m per
p and sign: take cutoff floor(p^(1/10)), omit the prime 2, use the
two distinct roots of m(pm+/-2) modulo sieve primes, and interval
length O(R/p) >= c_C p. Its O(p^(3/5)) error is absorbed by the main
term. Small fixed p can be covered by enlarging the constant and
using the trivial interval bound. This proves the edge-count bound
and the degree-1 moment after summing over primes. For p>=T the
reciprocal-prime sum with log^-2 weight is O(1/log^2 T) by Chebyshev
on dyadic bands.

For higher moments expand d^k into sums over j<=k distinct labels
with fixed orientations (at most 2^j choices). If incoming at y,
each label p_i imposes y=0 or -2 mod p_i; if outgoing at x,
each imposes x=1 or -1 mod p_i. Let P=product p_i and p=max p_i.
For tuples with all p_i<=R^(1/(2k)), P<=sqrt R. CRT fixes one residue
class for the common vertex modulo P. At the source of the largest
label (which for incoming is y-p+1), its selected neighbor divided
by p is an affine form m(h) with leading coefficient P/p when the
common vertex is parametrized by v=v0+Ph. The other neighbor is
p m(h)+/-2. For every odd sieve prime ell not dividing P the leading
coefficients are invertible and the two forbidden residues are
distinct. Omit the at most k odd prime divisors of P. This only
changes the sieve constant by a bounded k-dependent factor: the
finite Euler-product loss at each omitted odd prime is <=3, and
the same squarefree Selberg weights and remainder proof apply.
For completeness the interval in h has length O(R/P), and can
be enlarged to length comparable to R/P>=sqrt R, so the
O(p^(3/5)) error is absorbed uniformly. Thus the number of such
vertices is O_{C,k}(R/(P log^2 p)). No joint independence is used.

Summing the other j-1 reciprocal primes gives
O((1+log log(3p))^(j-1)); summation over the maximal p converges:
    sum_(p prime) (1+log log(3p))^(j-1)/(p log^2 p) < infinity.
With p>=T the tail is O_k((1+log log(3T))^(k-1)/log^2 T),
by grouping primes in dyadic bands and comparing the resulting
series with an integral (enlarge constants for small T).

For tuples containing a label >R^(1/(2k)), the number of vertices
having ANY such edge is O_{C,k}(R/log^2 R) by the degree-1 tail
bound. The unrestricted degrees are bounded by omega((x-1)(x+1))
or omega(y(y+2)), respectively. For fixed m the sum of omega^m
of either pair of shifted integers in an O(R) interval is
O_m(R(1+log log(3R))^m): use (a+b)^m<=2^(m-1)(a^m+b^m),
expand omega(n)^m by distinct prime tuples with product <=O(R),
and count multiples with the endpoint error absorbed by R/P.
Cauchy-Schwarz bounds the contribution of the exceptional vertices
to the kth moment by
O_{C,k}(R(1+log log(3R))^k/log R)=o(R).
This proves both fixed-order assertions, with the tail error uniform
in T before taking the limsup.

Finally, for labels p>=a sqrt R all allowed primes are within
[a sqrt R,C sqrt(2R+1)]. The bounded-ratio reciprocal prime sum
is O_{C,a}(1/log R), so the number of marked edges is
O_{C,a}(R/log^3 R). Each vertex has O_a(1) such incoming or outgoing
labels (their product divides one of two integers of size O(R)).
The marked kth moment is at most a constant times the edge count.

## 3. Unconditional transport bound for fixed generations

Write A f(y)=sum_(x->y) f(x), for nonnegative vertex functions.
Use normalized counting E_R f=(1/R)sum_v f(v). For fixed integer s>=1,
Holder and the degree-moment result give

    E_R (Af)^s
      <= (1/R) sum_(x->y) d_-(y)^(s-1) f(x)^s
      <= (E_R[d_+ f^(2s)])^(1/2) (E_R[d_-^(2s-1)])^(1/2)
      <= (E_R d_+^2)^(1/4) (E_R f^(4s))^(1/4)
                                    (E_R d_-^(2s-1))^(1/2)
      <<_{C,s} (E_R f^(4s))^(1/4).

The transpose has the same property. In particular for each fixed
h and k, the number of candidate paths of length h arriving at a
vertex from unit mass at every vertex, or from any subset of the
reset seeds, has kth moment O_{C,h,k}(R) in unnormalized counting.
The analogous outgoing path counts have the same bound.
No independence or clock-phase approximation is needed for this
upper bound.

Let B_{<=h}(u) count actual distinct seed origins reaching u in
at most h internal events, all of those events being efficient
and all source offsets non-twin. Include the reset state itself.
Stop at a twin or at the first inefficient edge. Each actual
history is a candidate path, so B_{<=h}<=sum_(j=0)^h A^j 1.
For fixed h this proves the unconditional prefix-energy bound

    sum_u B_{<=h}(u)^2 <<_{C,h} R.

Consequently, with H_2 from the preceding rough-flux note,

    sum_(non-twin u) q(u) B_{<=h}(u)
       <<_{C,h} R^(3/2)/log^(3/2) R.

This is a genuine bound on actual origin traffic, but only in
the indicated initial generations. It also applies to an injection
whose all fixed moments are uniformly bounded, replacing unit mass
by its incoming mass function in the displayed operator estimate.
It gives no such bound for arbitrary concentrated reinjections.

### Square-root-label traffic in a fixed window

For fixed h and a>0, the number of candidate paths of length h
from unit seed mass that contain an edge with p>=a sqrt R is

    <<_{C,h,a,epsilon} R/log^(3-epsilon) R

for every epsilon>0. To prove it, mark the position of that edge.
Let f_i(x) count paths up to its source and g_j(y) count paths
after its destination, with i+j=h-1. Count via
sum_(x->y marked) f_i(x)g_j(y). Apply Holder over marked edges
with exponents k,k,1/(1-2/k), k>2. The sums of f_i^k and g_j^k
over marked edges are O_{C,h,a,k}(R) by bounded marked degrees and
the preceding moment bounds. The number of marked edges is
O(R/log^3 R). The result is O(R/log^(3-6/k) R); choose k sufficiently
large and sum the h possible positions. For an actual path the
same bound holds for the number of origins having a marked event
within its first h efficient non-twin internal events (use the
union over lengths <=h; the exit variant follows by extending the
vertex set as above). This is substantially stronger than just
the ambient edge-count bound: it allows mergers in a fixed number
of preceding generations. Constants depend on the fixed window
length, not uniformly on h.

## 4. Why the phase-free bound does not yet close the proof

The moment exponent required on f is multiplied by 4 at every
application of the transport estimate; constants are not uniform
in h. On a twin-free path the positive efficient wait demand in
section 1 forces Omega(sqrt R) efficient events, since each wait
<=2sqrt(2R+1). Inefficient events can also inject already concentrated
origin mass. A bounded initial segment therefore cannot be
substituted for the full trajectory. Local degree moments alone
do not establish the required full traffic energy.

For the exact deterministic MIN one may use mass splitting instead
of counting every candidate path. For a fixed generation, let b(x)
be actual offset mass and F(x,y) the part sent to each efficient
internal destination. Then sum_y F(x,y)<=b(x), and

    sum_y (sum_x F(x,y))^2
        <= sum_(x->y) d_-(y) F(x,y)^2
        <= sum_x b(x)^2 max_(x->y) d_-(y),

with empty max taken as zero. This uses actual choice to avoid
the artificial branching multiplicity, but the right side can still
correlate b(x)^2 with large incoming degrees. Bounding that correlation
over many generations, or proving a suitable uniform contraction,
is a new concrete open target. The local degree theorem does not
make successive generations independent.

## 5. Executed audit

Source research/min_simple_efficient_graph_audit.py at
9a55a6f42354e4cda7889c2b82f894d0e1b779c8, Git blob
0b366b9ee42f40cf7ef7f422cedeecd8425db972. Remote content exactly
read back and matched executed local source hash. Requires stdlib and
the inherited min_simple_crossing_audit.py. Commands:

    python research/min_simple_efficient_graph_audit.py 1000 10000 100000 1000000
    cd research
    python -c 'from min_simple_efficient_graph_audit import audit; audit(1000000,100)'

Default C=16, marked threshold T=max(7,floor(sqrt R)/4).
All candidate edge identities, in/out degree sums, marked path
propagation inequalities, and domination of actual MIN generation
arrivals checked at depths 1..16. The actual histories stop on
a twin, inefficient edge, or exit. Counts below are internal arrivals
at the indicated exact depth, not distinct origins across depths.

    R        edges       max in/out  mean in   mean in^2   mean in^4
    1000     1211        6/6         2.422      7.526       101.942
    10000    12413       7/8         2.4826     7.9654      120.7342
    100000   124931      8/8         2.49862    8.10678     129.9699
    1000000  1253011     10/9        2.506022   8.16085     132.696826

R=1000000, C=16, 83334 reset seeds:

    depth  candidate paths  actual arrivals  candidate max  actual max
    1      183723           79907            6              5
    2      423069           78334            16             6
    4      2211813          72775            75             8
    8      61233695         63452            2072           13
    16     46504304772      47451            1945304        14

At C=100, same R, 1581428 edges, max degrees 10/10, 101818
marked edges. At depth 16 there are 3074913869120 candidate paths
versus 49871 actual arrivals, candidate max 75104234 versus actual
max 14. For comparison the sum of squared actual arrivals at depth
16 is 135475, whereas the candidate-path energy is
56000795566939364422. The gap demonstrates the limitations of
discarding the exact clock selection in long-history bounds; it is
not a counterexample to any asymptotic bound for the true dynamics.
No asymptotic estimate is inferred from these finite counts.

Next: study the actual mass-splitting operator and the correlation
between accumulated origin mass and the incoming degree of its
chosen destination, especially in efficient chains after earlier
mergers. No full-history energy bound, short-crossing upper bound,
or twin-infinitude proof has been obtained.
