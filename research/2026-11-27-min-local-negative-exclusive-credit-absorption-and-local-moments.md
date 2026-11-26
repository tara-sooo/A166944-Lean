# Negative MIN: exclusive merger credit, absorbing-word encoding, and local basin moments

2026-11-27 JST. Continuation of bf8a5da150db8e443aa896915527dac95e10edee.
This research block treats all three requested directions: fast/slow
gain integration, all-depth bad-basin estimates for additional
classes, and a forward asymptotic for successful mass and energy.
The new all-depth cut inequality eliminates common suffixes;
a periodic absorbing-word encoding eliminates arbitrary low-label
gaps and, in a second form, repetitions of previously known labels;
the finite-budget local-profile formula gives an actual weighted
sieve asymptotic below polynomial height. Neither the unrestricted
bad-energy bound nor a sufficient near-square-root successful-mass
lower bound is obtained. All arguments here are paper-level
deductions from the branch's previous results and standard upper
sieve inputs, not Lean verification or a literature priority claim.

## 1. Fast/slow gain balance and actual positive credit

Use the canonical negative MIN seed A in [R,2R], 6|A, h=3.
The state is (a,n), with h=n+a/2. At an event of odd prime p,
wait w, gain g=p-1, the height change is dh=w-g/2.
Call an incidence fast if 4w<p and slow otherwise.
The terminology is incidence-specific: different roots may arrive
at the same physical firing key at different times, so their waits
and their fast/slow classifications need not agree.

Since w is integer, fast implies 4w<=g, so 4 dh<=-g.
Since w<=2p, slow implies 4 dh<=6g+8<=10g.
For any completed prefix from h0=3, with fast and slow
gain sums F,S, respectively,

    4h+F <= 10S+12.                              (1)

For a fast-only run from any nonnegative height h0,

    4h_end+G_fast,run <=4h0.                     (2)

There is a more precise credit identity. Write

    c_i=max(0,4w_i-g_i).

This is positive only for slow incidences, and c_i<=11g_i.
Since h=3+W-G/2 for completed prefixes,

    G =12-4h+sum_i(4w_i-g_i)
      <=12+sum_i c_i.                           (3)

It applies at every completed arrival, including the seed.
An incomplete idle interval before a meeting does not alter
the gain. It is not necessary to charge it as a completed wait.

## 2. Exclusive merger cuts, without an event-depth restriction

Fix a gain budget L and first POST-tick height H, with H+L=o(R).
Consider any selected successful root cohort, grouped by endpoint a.
Let m=m_a be its mass. A physical event key e=(source distance,
absolute firing tick) in the basin has a unique label and gain.
Let U_e be its participating selected roots, n_e=|U_e|,
s_e the number of those incidences classified slow, and

    Q_e=sum_(i in U_e) max(0,4w_(i,e)-g_e).

Here n_e is TOTAL participation, not slow participation.
The U_e form a laminar family (disjoint or nested) within a basin:
once two physical states coincide they cannot separate before
the common first-height endpoint. In particular if a key is shared,
the remaining event sequence after it is identical. The slow
subsets of U_e are not asserted to be laminar.

Take roots A_i<A_j in this basin. If they share a completed key,
look immediately before their first shared key, at the common
source position. Otherwise use their common terminal position.
The gain of the larger root up to that source/terminal position
is at least A_j-A_i. All completed keys in its prefix before
the first shared key are exclusive to it relative to the smaller
root. If the pair merged during a wait or at a birth, these
exclusive completed keys still suffice: the gain is unchanged
through a wait. Applying (3),

    A_j-A_i <= 12 + sum_(e in U_j, e not in U_i) c_(j,e).
                                                               (4)

In (4) all exclusive events can be used; those after the first
meeting are absent automatically. The ordered-pair contribution
for any one e is at most Q_e(m-n_e), since its participating
root has at most m-n_e possible nonparticipating smaller roots.
The canonical roots have spacing at least six, hence

    sum_(i<j)(A_j-A_i) >= m(m^2-1).

Summing (4) gives

    m(m^2-1) <= 6m(m-1)+sum_e Q_e(m-n_e),
    m^2 <= 6m-5+sum_e Q_e(1-n_e/m).              (5)

In particular put

    K_bad = sum_(non-twin endpoints a)
                sum_(e in basin a) Q_e(1-n_e/m_a).

Then the complete bad energy satisfies

    C_bad <= 6 N_bad + K_bad.                    (6)

No restriction on the number of events, on the prime
alphabet, or on the shape of the merger tree is used.
The common trunk (n_e=m_a) contributes zero. The actual
credit may be considerably smaller than 11g_e per slow
incidence. The coarser version is

    C_bad <=6 N_bad
       +11 sum_(bad a,e) g_e s_e(1-n_e/m_a).     (7)

One can also choose the smallest canonical root in each
basin as a reference and sum (4) over the remaining roots.
Since sum_j(A_j-A_min)>=3m(m-1), it yields
3m(m-1)<=12(m-1)+sum_(e not on reference)Q_e.
This is another all-depth common-path subtraction.
Neither (6) nor (7) is an upper estimate of K_bad itself.
They supply a sufficient new target K_bad=O(R log^2 R)
for the full proposed energy bound.

An initial scratch computation incorrectly assigned a single
slow/fast status to every incidence at one key. It failed a
credit-subset check; the actual wait is arrival-dependent.
The final code distinguishes total participation, slow
participation and the exact summed credit, including 5327
mixed-wait keys in the finite controls.

## 3. Wall-assisted removal of sufficiently large fast labels

This gives a further all-depth reduction of the cut charge.
Fix a finite low alphabet P including 3, with spatial
wall maximum half-gap M from 0116e3e. Put

    D=2(M-1), B0=7D/4+8, T0=ceil(8B0+1).

Each contiguous P-only run has gain <=D, and by the
mod-30 potential its net height increase is <=B0.
These statements are independent of the starting height
and absolute time. In a completed prefix mark every event
outside P with p<T0, and every outside-P event with
p>=T0 and slow wait. The remaining outside-P events are
large fast events. Denote their total gain by F*, their
number by nf, and the marked count by nm.

Split at outside-P events. The total low gain is at most
D(nf+nm+1). The total net low height change is at most
B0(nf+nm+1). Every unmarked large fast event loses at least
g/4 in height. Thus nonnegative terminal height gives

    (1/4-B0/(T0-1)) F*
       <= h0+B0+sum_marked [B0+max(dh,0)],

using nf<=F*/(T0-1). As T0-1>=8B0,

    F* <=8(h0+B0+sum_marked [B0+max(dh,0)]).

The remaining total gain is bounded by low gain plus
marked gain. Since D/(T0-1)<=1/14, this yields

    G <= K0 + sum_marked W_i,                    (8)
    K0=9(h0+B0)+D,
    W_i=g_i+D+9[B0+max(dh_i,0)].

For a canonical prefix h0=3. This holds without any
bound on the number of small or large fast events.
If no marked event occurs, total gain is <=K0.
For a run after a reset one can instead insert its
initial height into K0.

Using (8) in the pair argument (4)-(5), with Q'_e the
sum of W_i over marked incidences at e (zero for the
others), gives

    m^2 <= 1+K0(m-1)/2
                    +sum_e Q'_e(1-n_e/m),
    C_bad <= (K0/2) N_bad
                    +sum_(bad a,e) Q'_e(1-n_e/m_a).             (9)

For the last inequality K0>=2 and h0=3 is used.
This bound charges no low-label events and no large fast
events; the medium marks p<T0 outside P have weights O(M),
and slow marks p>=T0 have weights O(p) with p/8-rough
sources. It is useful as a reduction of the target even
though the finite constants are not optimized. If M is
polylogarithmic of exponent <=2, the base term is already
O(R log^2 R). The remaining medium cut incidence count
and large-slow weighted cut charge are still uncontrolled
asymptotically. In particular the argument does not
assert that the number of fast events is small.

## 4. Periodic absorption for a fixed prime alphabet

Let P be any finite set of odd primes including 3.
Restrict the MIN rule to the eligible clocks with labels in P.
If there are no eligible labels, stop at that position,
called P-rough. Otherwise a next event exists within
2 max(P) ticks. The spatial walls of 0116e3e prevent crossing
the preceding wall, so at most D full gain can be consumed.
Every jump has positive even gain. Therefore this restricted
process always absorbs at a P-rough position after finitely
many jumps. It also makes sense in the formal congruence
extension for arbitrary even positions; all proofs in this
section concern that extension, and actual successful paths
in the physical slab are covered by it.

For canonical seeds A=6j define

    M_P=2 prod_(p in P, p>=5) p,
    V_P=prod_(p in P, p>=5)(1-2/p).

Translation j->j+M_P changes a by 6M_P and absolute
time n by -3M_P. Every eligible low clock is unchanged.
Thus absorption displacement, elapsed time and path are
periodic in j mod M_P. All P-rough positions are divisible
by six (since 3 is included). Over one j-period, exactly
M_P V_P residue classes are P-rough. The absorption map
takes each of the M_P initial residues to one of these
classes, and every P-rough class has its own seed.

Let b_P(a) denote the total number of canonical roots of
the infinite formal line absorbed at a. It is finite by
the wall bound and is a periodic function of a/6 mod M_P.
Then, exactly,

    sum_(a/6 mod M_P) b_P(a) = M_P,
    average(b_P | P-rough) = 1/V_P.              (10)

For the first identity, different canonical roots in one
residue class are translates with distinct translated
endpoints, so a given actual endpoint receives at most
one from each class. Count all residue classes once.
This is a conservation identity for all event depths,
not a probabilistic independence model.

## 5. All-depth bad mass from an alphabet of small modulus

Set H=4 floor(sqrt(R)/(log R)^B), L=floor(H/4),
B>0 fixed as in the preceding notes. Endpoints of successes
are K-rough for K comparable to sqrt(R)/(log R)^B.
Any non-twin endpoint has a composite neighbor a+e=q r,
q<=r prime, e in {-1,1}, K<q<=sqrt(2R+1).
Let P contain 3, all its labels <K, and M_P<=R^delta
for fixed delta<1/2.

A successful path using only labels in P follows the
restricted process exactly until it reaches its endpoint,
since the actual winner at every completed event belongs
to P. The endpoint is P-rough, hence its restricted
absorption position. In particular its basin multiplicity
is at most b_P(a) (or the gain-truncated version).
This holds for arbitrarily many events.

For fixed residue j0=a/6 mod M_P and q,e, the possible r
lie in one class modulo 6M_P, since q is coprime to 6M_P.
The parameter interval has length O(X), X=R/(q M_P),
which is polynomially large. Sieve r and q r-2e on
odd primes <=R^xi, excluding factors of 6M_P and q,
for sufficiently small fixed xi>0. Every remaining
prime gives two forbidden residues; removing the factors
of M_P costs at most V_P^(-1) in the sieve product.
The upper sieve used in d9f6049 (level sqrt X, CRT
remainder <=2^omega(d)) gives, uniformly,

    # bad centers in this residue for fixed q,e
        << R/(q M_P V_P log^2 R).

Weight by b_P(a), use (10) and the reciprocal q sum
O_B(loglog R/log R). It follows that

    N_bad(P) << R loglog R/(V_P log^3 R).         (11)

For any P with M_P polynomial in R,
V_P^(-1)<< (loglog R)^2: split its primes at log R,
use Mertens below and the product bound above, as
in the exceptional-prime product in bf8a5da.
Thus (11) yields O(R (loglog R)^3/log^3 R), uniformly
over a single such alphabet. For example P can be
all odd primes <=c log R with sufficiently small c,
or an arbitrary noncontiguous set with the product cap.
This is an all-depth bad mass bound, not an all-depth
bound for the union over every adaptive support.
A union over a prescribed collection of o(log^3 R/
(loglog R)^3) alphabets satisfying the same uniform
caps still gives o(R) bad mass. The analogous upper
sieve without the composite q condition gives total
successful mass O(R/(V_P log^2 R)) for a single P.
Consequently a single small-modulus alphabet cannot
account for a positive density of all successes at H
of this scale. There is no claim that a suitable small
collection covers the entire successful population.

## 6. Gap-free word encoding and direct count of initial roots

Previous 9314cd5 and bf8a5da enumerated the gains
of the gaps between terminal marked labels. The following
encoding eliminates that enumeration for a larger
all-depth class.

Fix a base alphabet P as above, M_P<=R^delta0, and
a number k of outside-P marked EVENTS. Suppose all
the other events of a successful trajectory belong to P,
and each outside-P event occurs at a P-rough source.
The latter condition follows if it is slow and its
prime exceeds 8 max(P), but slow wait itself is not
required for the encoding. Assume the marked primes
are <=R^phi, distinct from P, and delta0+k phi<1/2.
For the main bound take them in [R^theta,R^phi]
with fixed 0<theta<phi.

A signed word (p_1,c_1),...,(p_k,c_k) records only
the outside-P labels, c=0 for minus and c=2 for plus.
Fix the canonical root residue j0 mod M_P.
Starting at relative gain G=0 and elapsed time t=0,
run the restricted P process until absorption.
At a genuine marked source the restricted process
has exactly that same prefix, because all its previous
events were P winners and it has no remaining eligible
P clock. The displacement G and elapsed time t at
this source are determined by the root residue and
previous signed marks. The high mark pins

    A == G-1 mod p (minus),
    A == G+1 mod p (plus).

As A/2 parity is known from j0, the pinned A mod p
determines A/2 mod2p. Its wait is therefore uniquely
determined by the clock n=3-A/2+t and the chosen side.
Update G by p-1 and t by this wait, then run P to
absorption again. Repeated p imposes a consistency
test on its pin; a conflict discards the word. After
the final marked event, run P to absorption. The
endpoint of any actual successful path with that word
must be this final position, since it is P-rough.
There may be additional competitors in the actual
process, so arbitrary compatible words are NOT asserted
to be actual trajectories. They supply a necessary
encoding.

For each root residue and signed word, the entire
displacement and marked source offsets are fixed,
not free gap variables. Let P_hi be the product of
distinct marked primes. Root A lies in a unique
class modulo 6M_P P_hi if the pins are compatible.
If the final displacement is G and a=A-G, a also
lies in one such class. An additional composite factor
q is coprime to this modulus because the marked
labels are o(K) and all P labels are <K.
For fixed q,e the semiprime parameter r lies in
one class modulo 6M_P P_hi, with available length
X comparable to R/(q M_P P_hi) >> R^epsilon.

If at least s of the k marks are slow, add the
two rough-neighbor forms at each of those sources
to the endpoint pair, as in bf8a5da. Their shifts
are distinct because between marked sources there
is a positive marked jump of size >=R^theta-1.
Sift 2(s+1) forms, excluding the prime factors
of 6M_P P_hi and the nonzero product of shift
differences (all polynomially bounded), and
the finitely many primes <=4(s+1).
Choose the cutoff a sufficiently small fixed
power of R, below the slow-source roughness
and endpoint roughness. The fixed-dimension
upper sieve gives

    << R/(q M_P P_hi)
         * (loglog R)^(2s+2)/log^(2s+2) R

candidates for each root residue and word.
The exceptional-prime factor proof is the
same as in bf8a5da; the combined product of
excluded primes is polynomially bounded.
Summing over all M_P possible root residues
cancels that denominator exactly. Summing
1/P_hi over the finitely many equality patterns
and ordered prime assignments in the fixed
polynomial band costs O_(k,theta,phi)(1).
Sum the q reciprocals as before. Thus the
number of BAD ROOTS (not merely possible
endpoint/word pairs) in this all-depth class is

    N_bad,abs << R (loglog R)^(2s+3)/
                       log^(2s+3) R.           (12)

There is no low-gap gain enumeration, no
restriction on the total number of low events,
and no need to bound prefix depth. The same
argument without the composite q gives

    N_success,abs << R (loglog R)^(2s+2)/
                       log^(2s+2) R.           (13)

Hence for fixed k this class cannot supply a
positive-density success cohort by itself;
the natural sufficient lower bound to seek
for this class is instead Omega(R/log^(2s+2) R).
It is NOT proved at the near-square-root height.

For endpoint-only sieving (s=0), the lower bound
R^theta on high labels can be dropped: allow
any prime outside P with p<=R^phi. The sifting
primes may include small marked p, so exclude
their factors along with the modulus factors.
The sum of prime reciprocals is now O(loglog R)
rather than O(1); summing equality patterns
costs O((loglog R)^k). Thus the bad-mass bound
is O(R (loglog R)^(k+3)/log^3 R), still o(R)
for every fixed k. It includes moderate labels
rather than requiring polynomial lower bounds.
No uniform estimate for growing k follows.

For fixed P and k polynomial-scale high EVENTS,
a reverse bound also gives m_a<<_(k,theta) M^(k+1)
where M is the maximum half-gap of low walls.
Indeed choose the final low-run gain (at most D),
then the incoming high prime as a divisor of
one of two integers of size O(R), with only
O_theta(1) choices above R^theta. Continue
through k marks; the earliest low run has at
most M possible canonical root offsets.
Thus for this class

    C_bad,abs <= O_(k,theta)(M^(k+1)) N_bad,abs.

If M<=log^eta R and eta(k+1)<5+2s, (12) gives
C_bad,abs=o(R log^2 R). This is an all-depth
energy estimate for the selected class,
with no restriction on low-run event count.
It is not asserted for arbitrary repeats of
high labels counted only once, which is the
different encoding in the next section.

## 7. Absorbing innovations: arbitrary repetitions of known labels

Extend the previous encoding as follows. Start with
known alphabet P. Whenever a new label outside the
known alphabet first appears, require its source
to be rough for the entire currently known alphabet.
After that event add its prime to the known alphabet.
The inter-innovation runs may contain arbitrary
repetitions of any previous prime. By the same
finite-alphabet wall argument they can be replayed
until absorption. With the pinned residues for all
known primes, and the original root parity, all
their clocks and positions are determined. When
a new label appears, its sign and current displacement
pin the new residue, and its wait is determined.
Thus the root residue modulo M_P and the signed
sequence of k DISTINCT newly introduced labels
determine every completed event of any trajectory
in this class, including arbitrary repetitions.
No giant integer representative is required:
the replay can use relative displacement and time,
plus the known residues A mod p and root parity.

The final actual endpoint is rough for all used
labels for sufficiently large H: its least neighbor
factor is >9H/32-7, whereas each completed label
is <=L+1=H/4+1. Also require the base P labels
<K as above. Hence the last replay segment ends
at the actual endpoint. A sufficiently separated
slow innovation p>8 max(known alphabet) guarantees
the needed roughness at its source, but that is
only a sufficient condition.

For fixed k with delta0+k phi<1/2, exactly the
same CRT count as in section 6 applies, now with
a word of first appearances and no repetition
factor. The source offsets of the distinct slow
innovations are separated by their large jumps
in the polynomial-band version. Equations (12)
and (13) remain valid for this innovation class.
The endpoint-only variant dropping the polynomial
lower bound applies as well. In a common
constant-ratio polynomial band, distinctness
of the new labels additionally supplies log^(-k) R
in both bounds, since sum 1/p<<1/log R there.
This additional factor is not claimed for the
fixed-P repeated-event word with unconstrained
gaps, where the repeated-prime constraint
used in 9314cd5 need not be linear in the
other labels after replay.

The gain of these results is all-depth control
with only a bound on the number of distinct
innovations at absorbing sources. They do not
cover innovations that preempt existing eligible
clocks, an unbounded number of innovations,
or a marked product outside the sieve range.
A distribution/covering theorem for the
remaining actual trajectories is still missing.

## 8. Exact finite-budget local basin profile

This is a forward rather than merely bad-mass result.
For a general gain budget L, let

    T_g=floor(9g/4+8),
    Z_L=2 floor(9L/4+8)+7.

Consider a first post-tick height H with
H>=35L/4+73 and H=O(sqrt R) (or H+L=o(R)
where the physical argument below applies).
By the missed-clock barrier of 15daec2,
any successful endpoint is a stationary canonical
survivor d_3(a)>H. It is divisible by six and
rough at every prime <=Z_L, since a stationary
survivor has both neighbor least factors
>(2H-5)/3 >Z_L. Conversely if a is such a
stationary survivor, a canonical root A=a+g,
g in {0,6,...,6 floor(L/6)}, contributes to its
basin precisely if it reaches a within elapsed
time T_g (g=0 is the birth). In fact reaching a
costs exactly g gain, and the mod-30 potential
bounds the completed arrival time by T_g.
During these ticks the height-local factor rule
uses only primes <=2T_g+7<=Z_L, as preheight
is at most 3+T_g. Once it arrives, its height
is <=11+7g/4<H; because the endpoint is Z_L-rough,
there are no early clocks skipped below height 3.
The exact stationary condition d_3(a)>H then
ensures idle passage to H. Conversely all
successful roots must have this arrival property.

Thus the basin multiplicity, away from the
slab boundary, is a local function

    b_L(a)=sum_(0<=g<=L, 6|g) 1{reach a from a+g by T_g}.

It depends only on a/2 parity and a mod p
for p<=Z_L. For a rough endpoint it is evaluated
by the height-local MIN tick rule, stopping on
overshoot. Its domain of allowed residues is
the set of Z_L-rough canonical positions.
Define M_L=2 prod_(5<=p<=Z_L)p, V(Z_L)=prod_(5<=p<=Z_L)(1-2/p),
and the exact local moments

    mu_r(L)=E[b_L(a)^r | Z_L-rough]              (14)

over one uniform j=a/6 mod M_L period.
Equivalently take independent uniform
a mod p outside {1,-1}, p<=Z_L, and an
independent uniform a/2 parity. CRT makes this
an exact finite residue average, not a
heuristic model for actual large integers.
The endpoint-conditioned finite laws for any
fixed g do not change if more primes beyond
2T_g+7 are included in the conditioning.
In particular mu_1(L) is nondecreasing with L.

The moment upper bound is useful. Restrict to
all primes <=Z_L. Every local arrival counted
in b_L is part of its restricted absorption
map: the finite simulation agrees until arrival,
then the restricted rule stops at the Z_L-rough
center. Hence b_L <= b_(P_L). By (10),

    mu_1(L) <= 1/V(Z_L) << log^2(L+2),
    mu_r(L) <= (floor(L/6)+1)^(r-1) mu_1(L),
                                                  r>=1.       (15)

This is uniform in L and needs no event-depth
estimate. It also distinguishes the finite
local law from a claim about the distribution
of actual basins at square-root height.

## 9. Forward moment asymptotic and weighted bad upper sieve

Take L<=c log R with a sufficiently small
absolute c so M_L<=R^delta for fixed delta<1/2.
This follows from Chebyshev's bound on the
prime product, Z_L=O(L+1). Assume H->infinity,
H>=35L/4+73, log H=o(log R).
For any fixed allowed residue j0 mod M_L,
the exact stationary survivor condition
d_3(a)>H excludes 0,1 or 2 residues for each
free prime p>Z_L up to 2H+1. The count is
determined by j0 parity and the short/long
clock heights of 15daec2. It excludes both
neighbor residues up to (2H-5)/3, and none
above 2H+1. Therefore the free-prime sieve
product is, uniformly in j0,

    (1+O(1/log H)) V(H)/V(Z_L),

by the reciprocal sum in a constant-ratio
prime band around H. Here
V(H)=prod_(5<=p<=H)(1-2/p).
The progression length N is comparable to
R/(6 M_L). The fundamental lemma in 74a6796,
level sqrt N, gives relative 1+o(1) uniformly
since log N/log H->infinity; the CRT remainder
sum O(sqrt N log N) is negligible compared
to the main term. Multiplying each class
count by its nonnegative constant b_L^r
does not enlarge the relative error.
The number of residue classes allowed by
the small-prime roughness is M_L V(Z_L).
A boundary contribution or discrepancy from
root constraints A in [R,2R] is
O((L+1)^(r+1)), negligible in this range
for fixed r.

Consequently, writing m_a(H,L) for actual
successful basin multiplicities,

    sum_a m_a(H,L)^r
          ~ (R/6) V(H) mu_r(L),                (16)

uniformly for these budgets and fixed integer r>=1.
For r=1 it is a genuine forward successful
mass asymptotic; r=2 gives the full selected
energy asymptotic. For L=0 it recovers the
static rough frontier count. In contrast to
the distinct-state formula of 15daec2, the
coefficient mu_r records actual dynamical
merger multiplicity. For H=R^alpha with
sufficiently small fixed alpha>0 and same
modulus cap, the same lower and upper sieve
give a two-sided constant-factor estimate
instead of relative 1+o(1). Neither result
extends a lower sieve to near sqrt R.

At H=4 floor(sqrt R/(log R)^B) the local
profile is still exact for L<=c log R.
For a fixed composite q, sign e and allowed
residue j0 mod M_L, count r in its progression
modulo 6M_L as in section 5. Since Z_L<<K,
q is coprime to 6M_L, and the available
length is polynomial. The upper sieve on
the two forms gives

    << R/(q M_L V(Z_L) log^2 R).

Multiply by b_L^r, sum all allowed classes,
then q,e. The V(Z_L) factor cancels and yields

    sum_(bad a) m_a(H,L)^r
      << R loglog R/log^3 R * mu_r(L).          (17)

In particular uniformly up to L<=c log R,

    N_bad(H,L) << R (loglog R)^3/log^3 R,
    C_bad(H,L) << R (loglog R)^3/log^2 R.

These bounds are unrestricted in event depth,
but the gain budget is much smaller than H/4.
The corresponding total-success upper sieve
without the q factor gives
N_success(H,L)<<R mu_1(L)/log^2 R=o(R).
A sufficient forward lower bound at this
height would be Omega(R mu_1(L)/log^2 R)
along unbounded R, since (17) would be
smaller by O(loglog R/log R). No such
lower bound near sqrt R is obtained.
The exact finite local profiles do not
remove the parity obstruction for the
remaining free prime conditions.

For the full gain budget H/4, M_L can be
far too large to use this residue-by-residue
argument. Thus neither (17) nor the other
selected-class estimates establish the
unrestricted bad-energy target. The cut
inequality (6)/(9) is a possible way to
treat that larger budget, but requires
an additional quantitative cut bound.

## 10. Executed checks and exact finite coefficients

Three reproducible ECMAScript audits, all fetched at the exact
remote commit and re-executed with identical output:

A. research/min_local_negative_exclusive_gain_and_local_profile_audit.mjs
   commit c28e019cacf802192fb946f3910f7211090f48ba
   blob 02e509744b07ca7c9aadb613669304ac035ef339

Six near-sqrt slabs R=3000,12000,48000,192000,480000,1000000.
289172 canonical roots, 2541188 completed events, 100550 successes,
7593 bad successes. 2541188 fast balance and fast-run checks each;
13482 basin cut and actual-credit cut checks each;
77193 independent pair-exclusive checks, 35165 shared-key
checks, 11460 laminar nesting checks; 5327 mixed-wait keys.
For R=1000000, N_bad=4425, C_bad=72195,
total bad slow gain 303620, exclusive slow gain (before
the factor 11) 179531.463175..., and actual exclusive
credit 519358.840750.... The cut upper bound is valid
but not sharp numerically.

Local profile: five slabs R=12000 through 1000000,
L=6,12,24,48 and H=max(160,ceil(4 sqrt(2R+1)),
ceil(35L/4+73)). 20 controls, 49731 endpoint-level
comparisons of complete individual root lists, 236206
root reach checks, 1105028 nonstatic endpoint exclusions.
For R=1000000, H=5657, the 6702 static in-slab centers
give the following actual in-slab endpoint moments:

    L     root mass     energy     mean mass per static center
     6       11017       19647          1.64383766
    12       13660       31874          2.03819755
    24       18690       65232          2.78871979
    48       25462      133350          3.79916443

The L=48 boundary adds one success outside the endpoint slab.
The values at this finite square-root scale are not a
proof of (16) there.

The formal product measure (14) was evaluated by adaptive
residue tests, first in floating point and then independently
using exact integer counts of remaining assignments.
For each allowed prime coordinate a residue test divides
the current assignment count by the current size of its
allowed set; recurse on the singleton success and the
remaining failure set. The tick rule and the gain/time
cutoff determine the finite tree. For a joint reach
test of two offsets, run the second simulation with
the residue restrictions left by the first, so that
correlations are retained. 136618 single-offset integer
tree nodes and 23042 joint integer tree nodes checked.
Exact rational values are in the script output.
In particular

    mu_1(6) = 6028126/3660525 = 1.646792741478...,
    mu_2(6) = 3587776/1220175 = 2.940378224435... .

    L     exact mu_1         exact mu_2 (when computed)
     6     1.6467927415       2.9403782244
    12     2.0406788543       4.7612803994
    18     2.4349956009       7.1131730218
    24     2.7969081517       9.7833190992
    30     3.0616855879
    36     3.3403671567
    42     3.5753910946
    48     3.8024866427

For larger L the script also samples 4000 fixed-seed
pseudorandom independent-coordinate environments.
Sample means at L=96,192,384,768 are 5.2955,7.32175,
10.02025,13.584; sample second moments are 44.559,
98.41225,217.54025,472.2545. These are observations,
not an exact moment calculation or an asymptotic
growth law. In particular mu_1(L)->infinity is
not established; the upper bound (15) is proved
at the paper level.

B. research/min_local_negative_absorption_word_audit.mjs
   commit dc3ff5e730fe1a052806b6d040c2abf02f7b369a
   blob c05cc56561a48e5835860ecb895a7c2a2bed573f

Enumerate all 10862 root residues in five restricted
periods P={3},{3,5},...,{3,5,7,11,13}.
10862 translation checks, five exact mass conservation
and rough-residue counts. In the last period M_P=10010,
2970 rough endpoint residues, mean mass 3.370370...,
mean square 16.590572..., max mass 15,
maximum canonical absorption gain 132.
The wall maximum half-gap is 219.
The exact average agrees with (10).

Six actual near-sqrt slabs as above; for five base
alphabets, 502750 success/album classifications
(the classifications are overlapping), 357736
fixed-base absorbing-event word replays,
590376 marked event timing checks, 517513 pins,
38240 repeated-label word incidences, 357736
low-gap wall checks. Adaptive absorbing-innovation
replay: 352875 covered success/base-alphabet
incidences, 26536 bad incidences, 1679908 exact
individual replayed events, 76842 repeated
previously introduced-label incidences, 49558
separated slow-innovation checks. All matched.
For R=1000000 and P={3,5,7,11,13},
43920 successes satisfy the fixed-P source
roughness condition; 44215 satisfy the adaptive
innovation condition, with 1607 repeated-event
incidences in the latter. These finite counts
do not include the asymptotic fixed k, product,
and polynomial-scale restrictions of (12).
They are encoding tests, not lower bounds for
the asymptotic classes.

C. research/min_local_negative_marked_credit_cut_audit.mjs
   commit 69426af94163149822af8280dec9da65c388283a
   blob 23afab27e267ac9ba99cf7ec61d23011bc5927e6

Four slabs R=48000,192000,480000,1000000 at
both the near-sqrt and 4S first heights,
gain cap floor(H/4). Three wall alphabets
{3},{3,5},{3,5,7}, with (M,T0)=(3,121),
(9,289),(54,1549). 573340 root/horizon
controls, 8278900 events, 24836700 prefix
inequality checks, 13050549 low-run wall/
potential checks, 57870 excluded large-fast
incidences, 11381265 medium-mark incidences,
347016 large-slow marks, 76536 basin cut
checks, 830628 pair marked-charge checks.
All passed. For the third alphabet the high
fast cutoff exceeds the finite gain cap,
so exclusion is vacuous there; the first two
have actual excluded high-fast incidences.
The marked-charge constants are generous;
this is not a numerical optimization.

The scripts can be reproduced with node.
No separate Node or Lean invocation here.
The same finite slabs recur across the
audits, so their root counts should not be
summed as independent data. No asymptotic
upper-sieve constant is inferred from the
finite computations.

## 11. Status and remaining proof

The fast/slow balance is confirmed; the
all-depth exclusive cut estimate (6) and
its wall-assisted version (9) discard
common paths and large fast events.
The absorption-word method proves an
all-depth bad-mass bound for fixed small-
modulus alphabets and fixed absorbing
innovation classes, including arbitrary
repetitions of known labels. The local
moment asymptotic (16) gives a forward
successful-root and energy formula in
the subpower-height range, with explicit
exact finite coefficients. The weighted
bad upper sieve (17) applies near sqrt R
at logarithmic gain budget, without
restricting event depth.

A complete contradiction would require
a sufficient near-square-root successful-
mass lower bound, or another construction
of unbounded low-gain witnesses. For the
full H/4 gain budget it also requires
control of the exclusive cut contribution
or a covering/estimate of the residual
paths. The present classes need not carry
enough mass and the proven forward lower
range stops well short of sqrt R.
No unconditional proof of twin infinitude,
no Lean verification, no modifications
to canonical Lean targets or sibling branches.
