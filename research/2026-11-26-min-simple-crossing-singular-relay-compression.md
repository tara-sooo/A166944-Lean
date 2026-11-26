# Exact low-prime relay compression and a growing-word bound with phase classes

2026-11-26 JST. Continuation of 7f1287f97a0501ebbbfcdd1b1afdf8186215ebf3.
The interrupted chat's preceding paper and both audits were recovered at
that commit. Their exact executed local blobs matched the remote recorded
blobs. This note extends the growing-word estimate by using the actual
clock evolution between high events; it does not assume independent
relay gains. New mathematical deductions and executed finite audit.
No proof of full stable wait o(R^2), twin infinitude or Lean verification.

## 1. Exact relay determined by a finite residue

Use the same common-boundary MIN: integer seeds X in [R,3R/2], 6|X,
initial (X,X/2+3), stop at first U>=2R; M=R/12+O(1).
For a fixed integer cutoff z>=3 put

    Q=2 product_(3<=ell<=z, ell prime) ell,    L=2Q.

The restricted clock system considers ONLY labels <=z. At an even
offset u each eligible prime has its usual firing progression:
n=0 mod 2p for p|u-1, n=p+2 mod 2p for p|u+1. Choose the first tick
and then its least active prime, exactly as in the full system.
Terminate the restricted run as soon as neither neighbor has such
a factor. Its physical gain is <=Q: a p<=z step cannot strictly
cross a multiple of Q, and a multiple itself is a sink. The run
has <=Q/2 events and elapsed wait <=3Q.

The restricted evolution is translation invariant under
(u,v)->(u+L,v+Q), and also under (u,v)->(u,v+Q).
For a fixed even residue a=u mod L and an even adjusted time
coordinate d=2v-u mod L, the restricted run's displacement,
elapsed wait and event count are therefore determined exactly.
Write its displacement as E_z(a,d). No assumption on source
mass, actual deficit or initial reset ancestry enters the
periodicity. For d=0 or 6 as exact singular arrival deficits,
the permissible a are multiples of 4. Define D_z^sing as the
maximum of E_z on those residue pairs; D_z^sing<=Q.

Now consider two consecutive events with labels >z in an
actual full path (the intervening events, if any, all have
label <=z). Suppose the first arrives at (U,V) with d=2V-U
and the second has wait >2z. Every intervening event agrees
with the restricted clock system: it wins even against all
large competitors, so also wins against just the small ones.
The source of the second high event is a restricted sink,
since any eligible p<=z would supply a tick within 2z.
Consequently the entire relay, not just its total physical
gain, is the restricted run from (U,V). In particular

    relay gain = E_z(U mod L, d mod L).

The statement is valid even when the first high event is
not itself long-wait. It requires the second's wait >2z
and that these are consecutive among ALL labels >z, not
merely among an arbitrarily selected same-band subsequence.
No arbitrary stopping or early preemption of a restricted
run is allowed in this lemma.

## 2. Growing words with deterministic relays

Fix a dyadic high band [T,2T), T growing, T<=sqrt(2R+1)
up to a fixed factor. Take z<=log T, L<=T^(1/10), and
h=ceil(8 log T/log log T), subject to

    L (2T)^h <= sqrt R.

Consider h consecutive events in the sequence of ALL labels
>z on one actual path, with every one non-twin, label in
[T,2T), wait >=T/log T, and singular arrival (even V,d=0
or odd V,d=6). The wait lower bound exceeds 2z eventually.
All small-prime relays are now determined, so they need not
have the previous paper's freely specified E<=floor(log^1/4 T).
The only bound on their gain is D_z^sing<=Q.

More generally fix any nonempty set A of J even residues
modulo L; require each high arrival's deficit modulo L
to belong to A, rather than exact singularity. Define D_z(A)
as the maximum E_z(a,d) for even a modulo L and d in A
(<=Q). For both statements below write D_* for the applicable
maximum. The singular case has J=2 and the smaller domain
U=0 mod4; the same count applies. In the general case
orientation can be separately specified, costing at most
two choices per event. These phase classes can contain
arbitrarily large absolute deficits; they are NOT a bound on
the number of distinct actual rank values.

Given initial source residue rho mod L, the ordered high
labels p_i, their arrival deficit residues and orientations
e_i in {-1,1}, all source gains G_i=x_i-x_0 are determined
recursively: after p_i use the deterministic E_z on the
arrival residue (rho+G_i+p_i-1,d_i). Then

    x_0 = rho mod L,   x_0=e_i-G_i mod p_i.

For each compatible tuple the source belongs to ONE class
modulo L P, where P is the product of the distinct high
labels. Distinct high labels are coprime to L. Repetition
imposes compatibility, not an additional free relay choice.

At the first source, the long wait implies both neighboring
integers avoid all odd prime factors <T/(2 log T).
On this progression, sieve the two forms x_0+-1 using
odd primes z<ell<=floor(T^(1/20)). All high primes exceed
the cutoff. The inherited explicit Selberg upper sieve
(record-displacement-and-supply, section 3) applies with
these two distinct roots modulo every retained prime,
interval length comparable to R/(LP)>=sqrt R, and error
O(T^(3/10)). Omitting the small primes <=z costs at most
O(log^2(2z)) in the Euler product; the standard truncated
Euler-product / mean log index argument remains uniform,
since z<=log T and g(ell)<=2/ell. Thus the source count
for each fixed tuple is

    O(R/(LP) * log^2(2z)/log^2 T).                       (1)

It counts source offsets, not source phases or origin mass.
We use it only on a single monotone path, on which the
same source offset cannot recur.

For words with h distinct labels, sum (1) over rho,
orientations, deficit residues and ordered prime tuples.
The factor L cancels. By Chebyshev on the band,

    N_distinct << R log^2(2z)/log^2 T
                       * (C J/log T)^h.                (2)

This is the key benefit of exact compression: there is NO
factor proportional to D_* or Q per relay. For example
in the singular case it holds even when Q is a small power
of T, provided the stated product room holds. There is
no claim that the repeated words are all controlled in
that larger-Q regime.

## 3. Minimal returns with a joint two-prime sieve

A repeated word contains a shortest return subword
p_0,p_1,...,p_(j-1),p_0, whose first j primes are distinct.
Since D_*<=Q=L/2<=T^(1/10)/2, for large T consecutive
equal labels are impossible: p_0 would divide the odd
nonzero integer 1+e_1-e_0-E_0 of absolute value <T.
Thus 2<=j<h. The usual endpoint congruence gives exactly

    p_(j-1) = a p_0 + c,
    c=j+e_j-e_0-sum_(i<j) E_i-sum_(1<=i<j-1) p_i,

where 1<=a<=4j for large T. Positivity follows because
sum of interior primes + sum of relay gains -j-e_j+e_0
is positive. Also |c|=O(jT). If c=0, the two primes cannot
be distinct: p_(j-1)=a p_0. Exclude c=0.

Fix rho, a, all orientation and phase-class choices, the
j-2 other interior primes, and the residue of p_0 modulo L.
Then all relays E_i BEFORE the last one are determined
from the fixed residues. Only the final relay E_(j-1)
depends on the as-yet unspecified prime p_(j-1). Enlarge
the count by enumerating its integer value in [0,D_*].
For every choice c is now fixed and nonzero. We do not
require the actual last relay to match this guess in the
prime-pair count; doing so could only decrease it.

On the progression p_0=b+L n, sieve the two linear forms
p_0 and a p_0+c. The parameter interval has length O(T/L),
enlarged to comparable length. Omit odd primes <=z and
those dividing ac. On all remaining primes below T^(1/20)
there are exactly two forbidden residues, since L,a are
invertible and c nonzero modulo the prime. Both candidate
prime values exceed the cutoff. The explicit two-form
sieve gives uniformly

    # pairs << (T/L) log^2(2z) (log log T)^2 / log^2 T. (3)

Indeed the omitted small-prime product costs O(log^2(2z)),
and the additional loss
product_(ell|ac,ell>2)(1-1/ell)^(-2)
is O((log log T)^2) since |ac|=O(h^2 T); split its prime
factors at log(3|ac|), use Mertens below and the bound on
the number of larger prime factors above. The error
O(T^(3/10)) is absorbed by T/L>=T^(9/10).
All bounds are uniform in the coefficients, residues,
and j<=h. This uses a second sieve on the label pair,
in addition to (1) on source offsets, not an independence
assumption. Once an actual prime tuple is fixed, its
source progression is as in (1). The extra last-relay
guess overcounts, and has no effect on that upper bound.

There are at most L choices each for rho and the p_0
residue, O(j) choices for a, at most (2J)^(j+1) orientation
and phase choices, D_*+1 last-relay guesses, and
(CT/log T)^(j-2) free interior prime tuples. Multiply (3)
and (1) with P>=T^j and sum. The two L factors cancel
against the denominators of the two sieves. The number
of shortest-return occurrences on any one path obeys

    N_j << (R/T) j C^j J^(j+1) (D_*+1)
            log^4(2z) (log log T)^2 / log^(j+2) T.     (4)

In contrast to a sum over independent intermediate gains,
the relay-displacement loss is just D_*+1, not a power
depending on the return length. In particular this gains
a logarithm compared with counting the determined prime
without requiring its primality.

Each shortest-return occurrence can belong to at most h
of the h-windows in the high-event sequence. Weight the
first event of each window by its actual wait <=4T.
For J=o(log T), sum the geometric tail in (4) starting
at j=2, and combine with (2). The wait of the FIRST
events of all such windows, on any path, satisfies

    W_word(T) << R T log^2(2z)/log^2 T
                     * (C J/log T)^h
              + R J^3 (D_*+1) log^4(2z) log log T
                     / log^3 T.                       (5)

No bound on the number of labels, the number of repeated
labels, or the mass of an exact state is assumed.

For fixed eta in (0,1), if

    J^3(D_*+1) <= log^(2-eta) T,

then J<=log^((2-eta)/3) T, and the h chosen above makes
the first term O(R/T) for sufficiently large T. The
second is O_eta(R/log^(1+eta/2) T), absorbing the fixed
powers of log log T. Summing over eligible dyadic bands
T>=T0(R)->infinity and M origins gives

    W_words <<_eta R^2/log^(eta/2) T0=o(R^2).           (6)

The uniform bound holds for any one fixed choice of A at
a given band, including a choice fitted to that path.
It does not sum over arbitrarily chosen, changing A for
each individual window.

In particular for the singular case J=2 and Q<=log^(3/2) T,
D_*<=Q yields the more direct bound from (5)
O(R (log log T)^5/log^(3/2) T), hence O(R/log^(5/4) T).
Its all-origin dyadic sum is O(R^2/log^(1/4) T0).
A z tending to infinity and satisfying Q<=log^(3/2) T
exists by the elementary primorial bound log Q=O(z).
The exact compressed relay can be much longer than the
previous floor(log^1/4 T) cutoff. If an improved bound
on D_z^sing were available, (5) would also permit larger
Q subject to the product and sieve-room constraints; no
such asymptotic improvement is assumed.

A further unconditional special case allows ALL even
arrival deficit residues, J=Q, D_*<=Q, if
Q<=log^(3/8) T (so J^3(D_*+1)<=2log^(3/2) T).
Thus the exact relay compression does not intrinsically
require singular arrivals; the singular phase set is what
permits a larger small-prime cutoff.

## 4. Precisely what transport is still not covered

Split the sequence of all labels >z into maximal runs of
good events (in [T,2T), long wait, allowed arrival phase
class), interrupted by the other high events. All but the
last h-1 events of each run start a window counted by (5).
Let N_bad count the interrupting events with label >z.
Then for the good events on any one path,

    W_good(T) <= W_word(T)+4T(h-1)(1+N_bad).             (7)

Unlike a relay-gain charge, (7) does not penalize a long
relay consisting entirely of labels <=z; its exact
evolution has already been included. At eligible growing
scales a macroscopic W_good requires Omega(R/(Th))
genuine interrupting HIGH events. If all such separators
have gain >=T h log^2 T, the gain budget bounds their
contribution in (7) by O(R/log^2 T); this is a restricted
case, not a general theorem about the separators.

The product constraint still excludes polynomial scales
T=R^eps for growing h. More importantly, high events
outside the chosen comparable band or phase classes can
interrupt many runs. Large nonsingular phase diversity and
mixed intermediate/high scales remain uncontrolled. The
bound does not prove that a macroscopic proportion of
stable wait lies on good runs. It does not imply the full
wait estimate W=o(R^2), a basin bound or twin infinitude.
No lower sieve for prime pairs has been used.

## 5. Executed audit and a lifted nonzero-relay return

Source research/min_simple_singular_relay_audit.py, source
commit c501ae01983cc17eac945bf80a3943dcf222f90c, blob
8cf2f0534e0d88d2736605555a2e7e940086ff6a. Exact remote
readback matches the locally executed file (git hash-object).
Python stdlib and inherited min_simple_crossing_audit.py:

    python research/min_simple_singular_relay_audit.py 1000 10000 100000 1000000

Enumerated all singular arrival residue pairs at z=3,5,7,11;
independently replayed literal restricted GCD ticks at a
translated positive offset for every pair, not only modular
clock formulas. Counts and exact maximal observed displacement:

    z     Q       residue pairs   positive relay   max gain
    3       6               6          4              4
    5      30              30         24             14
    7     210             210        180             32
    11   2310            2310       2040             74

These are complete finite tables for the specified cutoffs,
not an asymptotic bound for D_z^sing.

Independent literal full-clock control at seed
X=13020+12*101!, a 162-digit integer: labels
(29,3,31,29), waits (14,1,15,11). The three high labels
(29,31,29) arrive singular, with d=6,6,0, and the low relays
have gains 2,0 for z=3. All quiet ticks checked by GCD,
nonzero odd raw defects <=101. The shift preserves their
prime residues. L*29*31=10788 and its square <X, exercising
the actual distinct-prime CRT product room for a nonzero
relay and repeated label. The growing h and sieve cutoffs
are NOT exercised by this three-event control.

Actual origin replay at R=10^3,10^4,10^5,10^6, z=3,5,7;
matches previous graph totals. For each consecutive pair of
labels >z with first singular arrival and next wait >2z,
the restricted relay's full gain, wait and event count
match actual evolution exactly. All observed same-band
singular h-windows for h=2,3,4 with every wait >2z were
checked for source-residue CRT consistency, actual
per-tuple offset counts and shortest-return linear
relations. The diagnostic wait threshold is >2z, not
T/log T, and h is fixed, not the asymptotic theorem.

At R=1000000, M=83334, 294268 cached states including twin
terminals, 2564511 non-twin origin visits, wait 66822800:

    z   compressed pairs   nonzero relay   same-band pairs
    3        180595           99632             4155
    5        140575           89109             3218
    7        117674           84540             2742

For z=7, 2047 of the 2742 same-band pairs had positive
relays; 116 three-windows (86 distinct,30 repeated),
2 four-windows. Maximum relay gain 32. For z=3, 189
three-windows, 63 repeated, and 18 four-windows; for z=5,
161 three-windows, 80 repeated, and 4 four-windows.
All integer checks passed. The sampled slab words did
not have the full sieve-room inequality; the lifted
control tests that arithmetic separately. No numerical
verification of the asymptotic sieve estimate is claimed.

Next target: control the true high-event interruptions in
(7), especially those of nearby but different scales, and
polynomial-scale words without a long CRT product-room
condition. The exact compression improves one part of
singular/phase-restricted transport, not the full residual.
