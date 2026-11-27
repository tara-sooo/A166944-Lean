# Negative MIN: local return caps, short-interval density, and spatial prefix packing

2026-11-27 JST. Continuation of 891cdb3a3865ee18c01e4a1a01780a6ccd92acfe.
The previous target was a mean fixed-prime arrival-height tail on sparse
high-clock heights. We derive a deterministic alternative using finite
alphabet local return caps and short-interval upper prime density.
We then replace the worst-case local cap by a truncated excess reward,
and bound the total excess using exact spatial packing of restricted
prefixes. This permits large isolated local-time maxima provided their
excess reward cannot be packed densely. Exact finite-alphabet controls
through K=11 and sampled controls through K=127 motivate this new
criterion. No limiting capacity estimate or actual growing-alphabet
discrepancy is proved. Paper-level results, not Lean verification.

## 1. Repeated arrivals of a fixed prime

Use the negative MIN conventions of 326eb62 and 891cdb3.
At a completed p firing with postheight h and target a,
the minus sign gives p|h,p|a and the even absolute
clock; the plus sign gives p|h-3,p|a-2 and the odd
clock. For p>=5 the same postheight on a single
trajectory cannot have both signs. Two such arrivals
at the same h have spatial displacement a-a'>0
divisible by 4p, by the spatial pin and clock parity.
Their elapsed time difference is (a-a')/2.
Thus every consecutive return to that height for p
consumes at least 4p gain and 2p ticks. This remains
true in arbitrary-phase restricted runs, because
adding the initial absolute height to their relative
heights does not change equality of heights.

This congruence does not give independent trials on
a repeated p coordinate. In particular the return
intervals for different heights can overlap, so one
cannot sum their gain charges over all heights as if
they were disjoint. This is the obstruction to a
direct probability argument based on repeat spacing.

## 2. Restricted-run decomposition and local caps

Let z>=5 be fixed, K>=z, Q_K=prod_(3<=p<=K) p,
and p_+(K) the next prime >K. In half-distance x=a/2,
the restricted alphabet through K cannot cross
multiples of Q_K (0116e3e). Its event map is periodic
in x mod Q_K and absolute n mod 2Q_K. From any phase
it reaches a rough absorber after finitely many
events. Let D_z^run(b) count its interior descent
intervals from labels <=z covering relative height b.
Define the arbitrary-phase maxima over full runs

    C_z(K)=max_(phase,b) D_z^run(b),
    A_(z,m)(K)=max_phase sum_b (D_z^run(b)-m)_+,

for integer m>=0. All prefixes obey these same maxima.
For comparison the old total descent capacity of
891cdb3 is A_(z,0)(K). One may define an analogous
C_p^arr(K) for arrivals of a single fixed prime p.
Relative or absolute height yields the same maxima.

On any canonical full or low-only trajectory through
T, partition its completed events at every label >K.
The resulting low runs (including empty runs if
convenient) are prefixes of restricted runs through K.
Let G be total gain and N_run their count. Then

    N_run <=1+G/(p_+(K)-1) <=1+(2T+6)/(K-1).

A nonempty run of completed wait W_i and gain G_i
has all its interior descent heights in an integer
interval of length ell_i<=1+W_i+G_i/2.
Indeed each post- or preheight differs from the
starting height by elapsed time minus half gain;
the minimum is >=start-G_i/2 and maximum <=start+W_i.
The sums of W_i and G_i are <=T and <=G.
We use zero length for empty runs. Consequently

    sum_i max(K,ell_i) <= K N_run+T+G/2
                         << T+K.                 (1)

There is no requirement that these intervals be
disjoint in height. They may overlap substantially.

## 3. Uniform short-interval density and a logarithmic cap criterion

For Y=cT, fixed c>0, let B be the high-clock
set from 326eb62 (heights at which either
2b+1 or |2b-5| has a prime divisor >Y).
Only heights 1<=b<=T+3 are considered.
For large T, each such divisor is p>Y with
positive quotient k bounded by a constant
depending only on c. Thus for each sign
and k, heights in an interval of length L
give primes in an interval of length
<=2L/k+O(1). The classical Brun-Titchmarsh
upper bound for primes in an arbitrary
interval of length l>=2 gives O(l/log l)
for large l. Summing finitely many k/signs,
for L sufficiently large in terms of c,

    |B intersect I| <<_c L/log L.               (2)

The same holds for B enlarged by any fixed
number of height shifts, with constants
depending also on that enlargement. No
prime lower bound or asymptotic in short
intervals is used. Alternatively the
elementary fixed-primorial argument in
326eb62 gives the weaker L/loglog L,
and the results below hold with log K
replaced by loglog K. The stronger stated
criterion uses the standard upper bound,
not an empirical prime-density estimate.

For each low run use (2), enlarging its
height interval to length max(K,ell_i)
if necessary. The number of z-small
descent occurrences on B is at most
C_z(K) times this prime-clock count.
By (1),

    sum_(b in B) D_z(b)
         <<_c C_z(K) (T+K)/log K.              (3)

This is deterministic and valid for
arbitrary canonical trajectories and
for their low-only versions. It counts
all visits, including long returns from
outside any individual height band.
In particular the sufficient condition

    liminf_(K->infinity) C_z(K)/log K = 0        (4)

implies sum_B D_z=o(T) for every fixed z.
The limit order is T->infinity with K
fixed, then K along a suitable sequence.
A uniform-in-T growing-primorial
transfer is unnecessary for (3).
The analogous bound holds for
fixed-p arrival counts and the enlarged
sparse sets B_z from 891cdb3, with
C_p^arr(K) in place of C_z(K).
This is much weaker than requiring
the TOTAL small-descent maximum
A_(z,0)(K)=o(K).

## 4. Truncate local maxima and isolate excess reward

A single exceptional height may make
C_z(K) large. For each run and height
use D<=m+(D-m)_+ whenever D>0.
By (1)-(2) and the definition of
A_(z,m)(K),

    sum_(b in B) D_z(b)
      <<_c m (T+K)/log K
             +A_(z,m)(K)(1+G/(p_+(K)-1)).       (5)

Here the excess is measured WITHIN
each low run, not after combining
all runs. Thus the capped portion
includes visits by multiple runs
to the same height and is already
accounted for by (1). A new
sufficient condition is the
existence of K->infinity and
integer m=m(K) with

    m=o(log K),    A_(z,m)(K)=o(K).             (6)

Condition (4) is the special case
m=C_z(K). Condition (6) allows
large maxima on isolated heights
provided their total excess is
small. This is a deterministic
tail estimate, not a bound
obtained by assuming independent
successive returns.

## 5. Spatial packing: no need to use the worst excess per run

Work on a single spatial cell of length
Q=Q_K in the half-distance coordinate
x in {0,...,Q-1}. For each x and possible
restricted prefix displacement d (0<=d<=x),
define V_(z,m)(x,d) as the maximum
of sum_b (D_z^prefix(b)-m)_+ over
all starting clock phases whose prefix
has displacement d. If no such prefix
exists omit that option. Include d=0
with reward zero. Translation of a
run by a whole spatial cell with the
same clock phase changes its absolute
height but not this reward.
The reward is nondecreasing under
extension of any one prefix.

Any two consecutive low-run starts
in the full trajectory are separated
in half-distance by at least d+s,
where d is the completed displacement
of the earlier run and

    s=(p_+(K)-1)/2.

Indeed they are separated by the earlier
low prefix and a high firing. This
remains true if empty runs are omitted.
Thus independent maximization of every
run is unnecessarily pessimistic.
Define the finite dynamic program

    F(0)=0,
    F(x+1)=max(F(x),
          max_d [V_(z,m)(x,d)+F(max(0,x-d-s+1))]).

F(x+1) is the exact optimum in the
RELAXED packing problem on positions
0 through x, with each chosen prefix
followed downward by the mandatory
separation s. At the lower boundary
we impose no constraints on later
starts outside the cell; this is
an upper relaxation. The recurrence
follows by deciding whether the highest
available position is a start, and
then restricting all lower starts.
No compatibility of the clock phases
of different runs is imposed, which
can only increase the optimum.

Put rho_(z,m)(K)=F(Q)/Q.
All low runs with starts in a given
spatial cell have total excess reward
at most F(Q). The actual half-distance
range has length G/2; it intersects at
most G/(2Q)+2 cells. Consequently

    sum_i sum_b (D_z^i(b)-m)_+
                 <=rho_(z,m)(K) (G/2+2Q).     (7)

Combine the capped part of (5) with
(7):

    sum_(b in B) D_z(b)
      <<_c m(T+K)/log K
               +rho_(z,m)(K)(G/2+2Q).          (8)

Thus it suffices to prove, along
some K->infinity,

    m=o(log K),    rho_(z,m)(K)->0.            (9)

Again take T->infinity first for
each fixed K. This is a further
relaxation of (6), since the number
of starts per cell is at most
1+Q/s and hence rho<=A_(z,m)(K)
(1/Q+1/s). No asymptotic bound on
rho is proved here.

For m=0 equation (7) directly
bounds the total small-label
descent reward independently
of B. The exact K=7 and K=11
computations below both give
rho_(5,0)=2/15. Since p=3
contributes no interior descent
length and p=5 contributes one,
we obtain the concrete finite
certificate for every trajectory:

    N_5 <= G/15+308                       (K=11),
    N_5 <= G/15+28                        (K=7).

Here N_5 is completed p=5 firings,
and the additive constants are
2F(Q) in (7). These are deterministic
consequences of finite enumerations
plus the packing proof, not a
formal Lean theorem. The tighter
constant uses Q=105, F=14.
For z=7,K=11, m=2 the excess
coefficient is only 31/1155,
even though the total reward
coefficient is 317/1155.

## 6. Connection to high-label gain and remaining conditions

For the low-only process with cutoff
Y=cT, the small-label toll W_(<=z,Y)
of 326eb62 is <=2/Y times the
left side of (8). If (9) (or (4)
or (6)) holds for every fixed z,
then this toll tends to zero,
deterministically and uniformly
over canonical phases. The
large-label descent toll is
bounded by the uniform long
interval prime density from
326eb62, tending to zero as
z->infinity after T. The baseline
is O_c(1/log T). The exact high
alphabet deletion law therefore
gives Pr_formal(any p>cT)=o(1)
and expected total gain from
such labels o(T), counting even
subsequent repeated high firings.

This would replace the previous
mean fixed-prime return-tail
problem by a deterministic
finite-state asymptotic bound.
It does not itself solve actual
growing-alphabet CRT discrepancy,
nor the total gain of all labels
below cT, and so does not prove
the desired mean gain below T/3.
The finite computations do not
establish any of (4),(6),(9).
In particular a maximum observed
in a random sample is a LOWER
bound on the true maximum, not
an upper bound. The exact small
periods cannot be extrapolated.

## 7. Executed audits

Both final scripts were executed in the ECMAScript
research runtime, fetched at exact remote commits and
re-executed with matching counts. Reproduce with node.
No separate Node or Lean invocation.

A. research/min_local_negative_small_height_local_capacity_audit.mjs
   commit 49b5c454012c06807f09457db43beada84d87c12
   blob bb2515570d69dbf77f49725c8c20a06ca8ba2743

All arbitrary even-position and clock phases for
K=3,5,7,11 on Q_K by 2Q_K periods. Direct absorption
simulation, track exact local descents and fixed-prime
postheight multiplicities, check same-label same-sign
spacing and truncated excess for m=1,2,3,4.
Additionally coherent arbitrary-phase random CRT
environments, 10000 each for K=13,23,47,97,127,
with gain cap 64K (no sample hit the cap).

    exact phase states                   2690568
    exact completed event steps          9069780
    same-label repeat spacing checks        8381
    excess/cap checks                   10762272
    sampled arbitrary phases               50000

    K   exact C5  exact C7  max N5(h)  max N7(h)
     3       0        0         0         0
     5       1        1         1         0
     7       2        2         2         1
    11       2        4         2         3

At K=11 exact A_(5,m) for m=1,2,3,4 is
[1,0,0,0]; A_(7,m) is [6,3,1,0].
For K=127 the SAMPLE maxima are C5=3,C7=6,
A_(5,m)=[4,2,0,0], A_(7,m)=[14,7,3,2].
These are not upper certificates for K=127.
The sampled mean per-path maximum D5 is
.8219 and D7 is 1.1267 there.

B. research/min_local_negative_small_prefix_spatial_packing_audit.mjs
   commit d73e19083b95a36e3da4dc4ddcd8483cdfa9c976
   blob b79c3efa643557724dcf62c75a4b50e0e40f61b8

Enumerate every restricted run from every phase
for K=3,5,7,11. For each prefix displacement
store maximum reward over clocks, with z=5,7
and m=0,1,2. Compute relaxed packing DP;
compare to the weaker spacing-only DP and,
for Q<=15, exhaustive recursive packing.
The initial extension had a scratch variable
name collision; it was fixed before updating
the committed script. Both runs passed.

    exact phase states                   2690568
    prefix steps                         9069780
    packing options                       64620
    exhaustive small-cell comparisons        12

    K   z   m    Q      F(Q)       rho
     7   5   0    105      14       2/15
     7   5   1    105       1       1/105
     7   5   2    105       0       0
     7   7   0    105      33       33/105
     7   7   1    105       8       8/105
     7   7   2    105       0       0
    11   5   0   1155     154       2/15
    11   5   1   1155      31       31/1155
    11   5   2   1155       0       0
    11   7   0   1155     317       317/1155
    11   7   1   1155     107       107/1155
    11   7   2   1155      31       31/1155

The exact packing optimum is only for
the relaxed independent-phase prefix
problem, hence an upper bound on actual
attainable reward, not an actual trajectory
construction attaining that optimum.

## 8. Status

The new deterministic logarithmic-cap
criterion and excess-packing criterion
give specific routes to the sparse-height
bound. The latter allows a small number
of unusually large return counts, and
the finite exact certificates yield a
global p=5 firing bound. No proof that
the limiting caps or excess packing
rates have the required asymptotic
behavior has been obtained. No actual
square-root discrepancy bound, total
mean saving, twin-infinitude proof or
Lean verification. No changes to
canonical Lean targets, sibling branches,
or Context files.
