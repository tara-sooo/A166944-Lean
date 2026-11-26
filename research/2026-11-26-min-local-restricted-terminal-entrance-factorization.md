# Restricted-terminal factorization of first-high entrance cohorts

2026-11-26 JST. Continuation of 55d79b1a400e5f2f55a2bd9d2e92e0e37bc108f4.
Address the root-entry term in the weighted inverse kernel by retaining
the entire actual lower-clock competition. An exact partition
factorization, periodic certificates for fixed cutoffs, a displacement
moment bound and a near-square-root energy obstruction.
Paper deductions and executed finite diagnostics; no Lean kernel
verification, external novelty claim, or twin-infinitude proof.

## 1. Exact restricted clock map and first-high factorization

Fix T>=5. The restricted MIN map L_T uses only eligible odd
prime labels p<T, with the same first-clock and least-label
tie rule as ordinary MIN. It stops at an even offset with no
eligible lower label. For a common boundary J it also stops
at the first arrival >=J (including overshoot). Define its
terminal signature as follows:

    rough terminal below J: the terminal offset alone;
    boundary exit: the full terminal state (u,v).

If no boundary is used, retain only the rough terminal
offset as signature. Existence follows from the inherited
primorial wall: Q=2 product_(3<=p<T) p is divisible by every
lower label, no such event can strictly cross a multiple
of Q, and no lower clock is eligible there. Positive
gain ensures finite termination. No envelope assumption
is needed for this termination.

Start with any finite set of ordinary canonical roots
X=0 mod6, v0=X/2+3, below J. Stop ordinary MIN at its first
event p>=T, or at the boundary exit if that happens first.
Record first-high events by marked arrival (U,n,p,e),
as in 86d425e; include an event whose source is below J
even if its arrival overshoots J. These marks include
twin events if the threshold condition holds.

The ordinary prefix before the first high event consists
entirely of lower events, and equals the restricted
trajectory step for step. At a first high source x,
pre-time t, firing time n, there is NO lower clock tick
in (t,n]. An earlier lower clock would win by time; a
lower clock at n would win by least-label tie-breaking.
There are two cases.

* If x has no eligible lower prime, the restricted
  terminal is x, with the phase forgotten.
* Otherwise, for every possible pre-time t that selects
  this particular first high mark, the next restricted
  event is the first lower clock strictly after n.
  Hence every such origin has the SAME restricted
  continuation, which can be computed from (x,n).

The marked arrival determines x=U-p+1 and n. Thus each
first-high cohort is contained in one restricted
terminal-signature cohort. The boundary stop is compatible
with this argument, since x<J and the next lower event
is identical. If ordinary MIN exits with no high event,
its restricted terminal signature is the actual exit
state.

Let m_j be the masses of distinct first-high marks,
and b_i the masses of restricted terminal signatures
for the whole root ensemble. Then

    max m_j <= max b_i,
    E_first=sum_j m_j^2 <= E_res=sum_i b_i^2.       (1)

More precisely the partition by first-high marks
and exact no-high exit states together refines the
restricted terminal partition. Thus the energy of
no-high exits can be added to the left side of (1).
There is no hypothesis on the number or physical gain
of the intervening lower events. This is an actual
clock comparison, not a relaxed inverse graph.

The signature choice matters: at rough terminals,
different pre-times can select one high mark, and
there is no common next lower event to identify those
times. One must forget the phase there. Conversely a
boundary exit can retain its phase. Merely grouping
first-high sources by offset is not necessarily a
refining partition: at one source different high
firing marks may preempt different lower clocks.
The finite audit finds four such source-offset
incidences. No offset-only refinement is asserted.

More generally on an ordinary history, at every
event p<T the restricted terminal signature (for
a fixed boundary ahead) is unchanged from its
prestate to arrival: the event is precisely the
next restricted event. Thus the signature is a
constant of motion along ANY consecutive lower
segment, not just the initial one. A high event
may change it. For previously merged entrants
one can apply the same partition factorization,
but the bound is then a weighted terminal energy
with their actual incoming masses, not the
canonical-root count.

## 2. Exact displacement moment bound

Let N be the number of canonical roots in the
finite ensemble, and U_X the offset of the
restricted terminal, with or without a common
boundary. Define G_X=U_X-X>=0. Group first by
terminal OFFSET, and write b(U) for that mass.
The roots in one group are distinct multiples of
six not exceeding U. Ordering them downwards,
the k-th has displacement at least 6(k-1).
Therefore

    sum_(X: U_X=U) G_X >= 3 b(U)(b(U)-1).

Summing, and noting that retaining phase at a
boundary exit only refines the partition, yields

    E_first <= E_res <= sum_U b(U)^2
                        <= N+(1/3) sum_X G_X.       (2)

For any fixed integer k>=1, the same argument
using sum_(j=0..b-1)(1+6j)^k >>_k b^(k+1)
bounds the (k+1)-st terminal mass moment by a
constant times sum_X (1+G_X)^k. This makes
restricted displacement moments a concrete
sufficient bound for all fixed entrance mass
moments. It does not estimate those displacement
moments asymptotically.

For example a uniform bound on mean restricted
displacement O(log^(3-delta) R), delta>0, would
give E_first=O(R log^(3-delta) R) for a slab
with N=Theta(R). That energy target is not
claimed; section 5 describes an obstruction to
the naive terminal-energy approach at sqrt scale.

## 3. Exact periodic finite certificates

Let y be the largest admitted odd prime and
Q=2 product_(3<=p<=y) p. Use the unrestricted-in-
space restricted map (no common boundary).
The canonical seed translation

    (X,v0) -> (X+2Q,v0+Q)

commutes with all lower clocks: 2p divides Q
for every admitted p. Therefore one full seed
period has offset length P=2Q, with N0=P/6=Q/3
distinct canonical seed residues. Translating
back the terminal offset modulo P accounts
correctly for seeds ending exactly at a wall
in the next cell. The number of seeds in each
absolute terminal basin is exactly the number
in the corresponding folded terminal class
in the period. In particular both the maximal
basin mass and the squared-mass sum per
terminal period are finite computable functions
of y. The absolute terminal may be at a wall,
so folding is essential.

For an arbitrary interval of roots of length R,
their full restricted terminal offsets lie in
an interval of length R+Q. Each actual terminal
offset basin is contained in the corresponding
full periodic basin. Its energy is thus at most
(R/P+O(1)) times the period energy, with the
O(1) absolute. A boundary-exit signature also
refines the FULL restricted terminal offset
partition, since continuing from that exact
exit state gives one terminal offset. This
allows the same full-period upper bound on
first-high energy even when a boundary is used.

For y>=3, the exact number of rough terminal
residues in a period is

    A_y=2 product_(3<=p<=y) (p-2).

Every rough even residue is divisible by 6
because it avoids both forbidden residues
modulo 3. It is itself a canonical root
which terminates immediately. Thus every
rough terminal residue is occupied in the
full-period root ensemble. By Cauchy-Schwarz,

    E_period/N0 >= N0/A_y
       = (1/3) product_(3<=p<=y) p/(p-2)
       = Theta(log^2 y) as y->infinity.              (3)

The last relation is the ordinary Mertens
product, since the logarithmic difference
between (1-2/p)^(-1) and (1-1/p)^(-2) is
summable over odd primes. This is a LOWER
bound: terminal cohort energy cannot remain
uniformly bounded in the cutoff. By (2),
the mean full-period displacement is at
least 3(E_period/N0-1). Equation (2) also
holds for the folded period: lift all roots
of any terminal class by multiples of P so
that they have one common absolute terminal
offset, preserving displacement and making
the roots distinct multiples of 6.

The exact computations through y=17 below
give a global maximum basin mass 24 for
the cutoff allowing all odd primes <=17
(equivalently T=19). Thus any first-high
mark of label >=19, from any finite set of
canonical roots, has at most 24 distinct
origins BEFORE any earlier label >=19.
The bound holds for arbitrary R, not just
the tested positive representatives, because
all residues of the period are covered.
This is a computer-assisted finite
certificate plus the periodic reduction,
not a Lean-checked theorem. It gives no
bound of 24 after several high events.

## 4. Replace the initial entry factor of the weighted kernel

The marked inverse induction of 86d425e applies
from the first-high mark onwards. Instead of its
initial root-entry factor B+2 and entry cost,
we may use an upper bound b_* on the actual
first-high mass from section 1. Suppose a target
high mark is reached through at most H subsequent
high-to-high steps, total intervening lower gain
<=M and elapsed time <=W0, in the appropriate slab.
The previous geometric kernel with
C=(4/3)J_factor(B+2) bounds its possible first-high
entry marks by

    A=2 C^H 2^(W0/T+M/B).

Thus its actual origin mass is <= A b_*.
For any deterministic stopping rule assigning
each first-high mark to at most one final mark
within the budgets, the squared-mass inequality
from 86d425e gives

    E_final <= A E_first <= A E_res.               (4)

If the stop is chosen separately by each root
(e.g. variable boundary X+D), use (4) only on
a deterministic mark stopping subproblem;
the pointwise ancestry mass bound remains
valid for any root-specific truncation.
The entry estimate itself has no preceding
lower-gain cutoff, so (4) removes that
particular loss from the inverse induction.
No estimate for arbitrary later high-to-high
steps is implied. For fixed T the full-period
energy is exact; for T near sqrt R its period
is exponentially larger than R, and a uniform
upper bound on actual local restricted
terminal energy is still needed.

## 5. Square-root scale: necessary energy at rough entrances

There is a constraint on the proposed
subcritical entrance-energy target.
Take T comparable to sqrt R, with fixed
positive comparison constants, and a local
window D<=C0 T. Stop each ordinary canonical
ray before its first high event outside the
window; count actual first-high marks whose
source lies inside. Use the actual pre-gain
bound to get d_pre<=6+5D. Restrict to
non-twin source offsets x in [R,3R).
If a first-high event occurs at a rough
restricted terminal x (no eligible p<T),
then q(x)>=T.

The inherited rough-flux bound
sum_(non-twin x in [R,3R)) q(x)
<<R^(3/2)/log^3 R implies

    # non-twin rough terminal offsets in this slab
          << R/log^3 R.                            (5)

At each such offset, there are only O(1)
possible first-high marks with source in
the local window: the number of eligible
prime labels >=T is O(log R/log T)=O(1);
the pre-time interval has length O(T) by
the deficit bound, the wait <=2q(x)=O(T)
by non-twin roughness, and for each label/
side the firing times are in a progression
of spacing >=2T. This counts marked arrivals
even if they overshoot the window.

If N_rough roots have such a first-high
entrance, their marked arrival classes
are among O(R/log^3 R) classes. Cauchy-Schwarz
now gives the actual necessary bound

    E_first >> N_rough^2 log^3 R / R.               (6)

In particular if a positive fraction of
canonical roots have first-high events at
non-twin rough terminals within D=O(T),
their actual entrance energy is at least
order R log^3 R. Thus an estimate
E_first=o(R log^3 R) would force this
population to be o(R), not merely
establish an almost uniform entrance mass.
It would leave preemptions at nonterminal
offsets and paths without first high in
the local window to be controlled. The
argument does not assume that the positive
fraction exists. Twin sources are excluded
from (5)-(6); under finite twins all
sufficiently large sources are non-twin.

A related restriction applies to the
restricted terminal partition itself:
for any finite slab with N=Theta(R),
if N_r of its roots end at non-twin rough
terminals within [R,3R), the offset-only
terminal energy is >> N_r^2 log^3 R/R.
A boundary exit must not be counted as a
rough terminal just because its phase
signature is defined. The fixed-cutoff
periodic lower bound (3) and the local
near-sqrt lower bound (6) concern
different domains.

There is a direct alternate target:
choose T>sqrt(3R+1). Every rough
restricted terminal x in [R,3R) is
a twin center, because a composite
neighbor <=3R+1 has a prime divisor
<T. Hence showing that at least one
canonical root in [R,2R) terminates
strictly before 3R in the restricted
system, along unbounded R, would
establish twin infinitude. This needs
no control of high-event preemptions
in ordinary MIN. For example a mean
full restricted terminal displacement
o(R) would suffice; even a single root
with terminal gain <R suffices. The
primorial wall only gives Q, far too
large at this cutoff. This is a
separate sufficient target, not a
proved supply of terminating roots.

## 6. Executed finite diagnostics

Source research/min_local_restricted_terminal_entrance_audit.mjs,
final commit b2fb8beea41bda01b40954463d7fd99e8473e973,
blob 560c36b0a1eacb5df2c621747dd0f7bc7d3d556b.
Reproduction: node research/min_local_restricted_terminal_entrance_audit.mjs.
Executed as ECMAScript in the research runtime, fetched at the exact
commit and re-executed with identical results. No Node process
or Lean process invoked.

Full periodic enumeration for y=3,5,7,11,13,17,
including all canonical root residues, exact
restricted first clocks, memoized terminal
states, wall checks, and folded terminal
offsets. The upper cutoff here is INCLUSIVE y.

    y     Q       roots   rough   period energy  max mass   mean gain
    3       6         2       2           2          1        0
    5      30        10       6          18          2        2.4
    7     210        70      30         206          5        5.82857
    11   2310       770     270        3048         10       10.14545
    13  30030     10010    2970       49274         15       14.12907
    17 510510    170170   44550     1015400         24       19.08841

For y=17, mean basin mass seen by a random root
is E_period/N0=5.96697. Maximum gain=210,
sum of terminal gains=3248274. This is not
an asymptotic displacement bound. All exact
rough-residue counts, energy/displacement
checks, and literal restricted GCD ticks
passed. 181032 full-period root/cutoff
incidences; 365439 memoized restricted
steps, 816 literal restricted ticks.
The first two finite periods include
small offsets only via positive lifted
representatives, avoiding invalid u=0.

Separate actual slab controls use EXCLUSIVE
T and a common upper boundary J=R+len.
All multiples of six in the stated interval
are tracked until first high mark or exit.
Compare each actual root to its exact
restricted terminal signature from the same
seed, then independently replay the
restricted continuation from (x,n)
when a high clock preempts a lower one.
The energy E_res retains phase on boundary
exits and discards it at rough terminals.

    R        len   T   roots  E_res    E_first  preempt   rough first high
    10000    10000 13   1667    6587      4390      260        1406
    100000   30000 31   5000   45484     32468      688        4304
    100000   30000 127  5000  108330     96962      273        4709
    1000000  60000 251 10000  378712    357859      477        9480
    1000000  60000 503 10000  587238    552165      355        9582
    1000000  60000 997 10000  826098    758900      482        9454

41667 actual root/cutoff incidences, 702715
lower ordinary events, 41470 first-high marks
counted by root incidences, 197 no-high exits,
2535 preemptions and 38935 rough terminal
first-high incidences. These controls allow
twin sources; rough terminal count here is
not a non-twin-only sample. 127300 memoized
restricted steps, 41470 factorization checks,
10579 literal unrestricted GCD ticks. Four
source-offset incidences in the first two
slabs admit different restricted terminal
signatures from distinct high marks; the
marked partition always refines. All
assertions passed. Example X=10146,
first high source x=10152,v=5082,p=13,
n=5085, next lower clock wait13, restricted
terminal x=10182. The full first-high
mark uniquely determines that restricted
terminal.

At R=10^6,T=997, E_first/N=75.89,
E_res/N=82.6098, max first-high mass=284.
Mean restricted displacement 826.1144.
The common boundary is much farther than
O(T) in this diagnostic; (6) is not
tested as an asymptotic estimate here.
The entrance energy is already close
to restricted terminal energy at the
larger tested cutoffs; this supports
investigating actual terminal basins
rather than assuming the bound is sharp
at asymptotic near-sqrt scales.

No changes to canonical Lean targets or
sibling branches. The full-period upper
bounds and displacement comparison do
not supply a uniform local entrance
energy estimate when T grows like sqrt R.
No favorable unbounded reset family or
twin-infinitude proof has been obtained.
