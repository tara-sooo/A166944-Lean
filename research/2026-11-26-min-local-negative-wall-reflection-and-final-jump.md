# Negative-offset wall reflection and the final-jump criterion

2026-11-26 JST. Continuation of 3734e4c3bc33d7c0b6cfdb4ed6ab42993e9912fe.
Change the direct deterministic lane to a finite negative-offset
model with a fixed terminal offset. Exact embedding at positive
primorial walls, a last-event twin criterion, and phase
synchronization diagnostics. This does not repair the excluded
constant-gap Laplace route. Paper deductions and executed finite
audits; no Lean verification or twin-infinitude proof.

## 1. Negative-offset model with a fixed terminal

For A>=6 a multiple of 6, start

    u=-A, v=-A/2+3.

Use the same lexicographic clock rule as positive MIN. At
u=-a<0 with a positive even integer, minus-side primes divide
a+1, with firing times n=0 mod 2p; plus-side primes divide
a-1, with firing times n=p+2 mod 2p. These are ordinary
positive prime divisors of the absolute neighbor values.
After a clock of p fires with wait w, a decreases by p-1
and v increases by w. Stop at a=0.

All labels satisfy p<=a+1, because they divide a+1 or a-1.
There is always a minus-side prime divisor of a+1>=3.
Thus a strictly decreases by a positive even amount and
never becomes negative. Every trajectory terminates at a=0.
This holds for any initial integer phase v with h=v+a/2>=0.

The ordinary nonnegative-deficit argument remains valid
without assuming u>0: d=2v-u>=0 and d'=d+2w-(p-1)
>=3-p; at a minus firing d'=0 mod 2p, at a plus firing
d'=6 mod 2p. These exclude negative d' (including p=3).
Also w<=2p<=3(p-1). In particular for canonical roots,
after physical displacement G=A-a the height satisfies

    0<=h=v+a/2<=3+(5/2)G.

A further exact feature: if v<0 at any negative source,
some minus clock fires at n=0, so the selected firing
time is <=0. In particular a path ending at phase zero
has all its actual firing times <=0. If time reaches
0 before the wall, later time becomes positive.

Let P(A) be the LAST label and H(A) the terminal time,
which equals terminal half-deficit at u=0. The final source
is a=P(A)-1, and the selected side must be minus:
a+1=P(A), while a-1=P(A)-2 cannot be divisible by P(A).
Consequently

    P(A) is prime,  H(A)>=0,  H(A)=0 mod 2P(A).

H(A)=0 does not itself certify twin primes. For instance
arbitrary-phase noncanonical seeds can terminate via a
prime P whose lower neighbor P-2 is composite.

## 2. Exact embedding at positive primorial walls

Let Y>=3 and J>A+2 be divisible by

    4 product_(3<=p<=Y, p prime) p.

Translate (u,v) to (J+u,J/2+v). The translated initial
state is canonical X=J-A, X/2+3. For all admitted primes
p<=Y, source eligibility and clock congruences are preserved
because J is divisible by 4p. In this section use ordinary
positive MIN with all odd primes allowed, or any restriction
admitting every odd prime <=Y.

General embedding: if Y>=5A+11, the translated ordinary
trajectory agrees event for event with the negative model
up to hitting J. Indeed at any matched source J-a<J,
there is an eligible minus prime divisor of a+1, so the
least eligible prime q<=a+1. The actual winning wait
w<=2q. The firing defect is 2(h+w)+1 or 2(h+w)-5;
it is odd, nonzero, and divisible by the winning prime.
Using h<=3+(5/2)(A-a),

    p <= 7+5(A-a)+4q <=5A-a+11 <=5A+11.

Thus the actual winner is among the known congruence-
preserved primes; their selected clocks agree. Induct
until reaching J. The arrival is (J,J/2+H(A)).

Sharper zero-phase embedding: if H(A)=0, it is enough
that Y>=A+1. At every tick from the matched source until
the negative winner (inclusive), relative time n<=0.
The tick height h_tick=n+a/2 satisfies 1<=h_tick<=a/2
since the source height is nonnegative. Both odd defect
forms have absolute value <=a+1 (also for a=2).
Any eligible positive-world prime at these ticks divides
the corresponding nonzero defect, hence p<=a+1<=Y.
All these tests agree with the negative model. In
particular no extra larger prime can preempt the known
negative winner. This proves the sharper embedding,
without any claim about what happens AFTER hitting J.

The translated wall J is NOT necessarily a genuine
terminal in unrestricted positive MIN. It is rough for
the base primes <=Y, and a later prime >Y may fire.
The finite negative model has deliberately fixed its
terminal at 0; reflection does not establish primality
of J-1 and J+1.

A consequence is a certified large exact phase basin:
for any fixed Y>=300001 and any positive J divisible
by the above product, the 49993 zero-phase seeds from
the finite audit in section 4 all arrive at the SAME
positive state (J,J/2). The ordinary trajectories
then coincide thereafter. Thus an extremely large
canonical origin mass can occur at arbitrarily large
offsets, although this gives a fixed cohort size, not
a lower bound growing with J. The finite phase audit
is used here together with the embedding proof;
no asymptotic synchronization claim.

## 3. A deterministic last-jump criterion for twin infinitude

Write E=A-(P(A)-1) for the physical gain BEFORE the
last event. Let W_pre be the preceding elapsed time and
w the final wait. Exact total time is

    W_pre+w=A/2-3+H(A),

and W_pre<=3E. If P=P(A)>=5 and P-2 is composite, its
least odd prime factor q<=sqrt(P-2) is eligible at the
last source. So w<=2sqrt(P-2). Consequently

    A/2-3+H(A) <=3E+2sqrt(P-2),

or equivalently

    P <= 5E+7+4sqrt(P-2)-2H(A).                    (1)

Thus if P>=5 and the STRICT reverse inequality holds,
P-2 is prime. This certificate uses the clock selection
and total preceding time, not the assumption of small
terminal phase. It does not require H(A)=0.

As E=A-P+1, inequality (1) also implies

    P <= 5A/6+2+(2/3)sqrt(P-2)-H(A)/3.

If twins are finite, all P with P-2 prime are bounded;
P=3 is bounded too. Therefore under finite twins,

    limsup_(6|A,A->infty) P(A)/A <= 5/6.             (2)

Conversely if P>=13 and P-2 are prime, the twin center
A=P-1 is a multiple of 6. From the canonical negative
seed, v=(7-P)/2<0. The minus P clock next fires at 0.
The plus P-2 clock has previous firing 4-P<v and
next firing P>0. So the minus P clock wins, jumping
directly to 0 with H(A)=0 and E=0.

In particular the following is an exact paper-level
equivalence:

    infinitely many twin primes
      iff limsup_(6|A,A->infty) P(A)/A > 5/6
      iff limsup_(6|A,A->infty) P(A)/A = 1.          (3)

The reverse direction of the first iff is (2).
The forward direction of both is the direct jump
on twin centers and P(A)<=A+1.

A useful sufficient target is an unbounded sequence
with E/A<=1/6-epsilon for any fixed epsilon>0.
It only concerns the gain before the final jump
of a finite, terminating trajectory. The proof
uses no distribution of CRT lifts or upper-bound
sieve. It is not a proof that such a sequence exists.
In particular even eventual H(A)=0 alone would
not prove (3): last labels could stay bounded,
or their predecessors could have high deficit.

General initial height h0 (noncanonical) changes
the exact time identity to W_pre+w=A/2-h0+H and
the composite-neighbor bound to

    P <= 5E+1+2h0+4sqrt(P-2)-2H.

This version was used for nonvacuous composite-
neighbor controls in the audit.

## 4. Executed diagnostic

Source research/min_local_negative_wall_reflection_audit.mjs,
final commit cf500e895217a2ad9f55c64cb27364637c68d6f3,
blob 2119648f37e0625acb9703cb22c5349a8029783c.
Reproduce: node research/min_local_negative_wall_reflection_audit.mjs.
Actually executed as ECMAScript in the research runtime,
fetched at exact commit and re-executed identically.
No separate Node or Lean invocation.

All 50000 canonical negative seeds A=6,12,...,300000.
Exact factor-based event clocks; memoize the eventual
last label, last wait and terminal phase at each
negative state (a,v), not merely at each offset.
166400 distinct evaluated transitions, 42509 memoized
suffix hits, 166400 minimum-clock and nonnegative-
height/wall checks, 166393 negative-time ceiling checks.
200 independent nonmemoized comparisons, including
100 seeds through A=600 and 100 regularly spaced
seeds through A=300000. All passed.

Terminal phases:
    H=0: 49993
    H=12: 1
    H=24: 1
    H=66: 5

Nonzero phases occur exactly at the tested seeds
A=6,24,90,96,126,132,144. All 49993 zero-phase paths
in this finite range end with an actual twin label
P>=5; the seven remaining paths have P=3.
No composite P-2 with P>=5 occurred in the canonical
sample, so the composite-neighbor inequality's
canonical branch was vacuous in this sample.
49925 seeds satisfy the strict numerical twin
certificate (1); 2992 direct twin-seed reset
checks passed.

    A range          roots  zero phase  certified by (1)  mean P/A
    6..3000            500      493          446           .937342
    3006..30000       4500     4500         4479           .985229
    30006..300000    45000    45000        45000           .996222

The last range contains 2529 DISTINCT terminal
twin labels, not 45000 different twin pairs.
The observed concentration of P/A near 1 is
finite data; no limiting lower bound is proved.
No claim that all A>=150 have H=0 or P-2 prime.

Additional arbitrary-phase control: all A=6..600
by 6 with initial h0=0..min(A/2+20,80).
7530 phase controls, 47592 events, 25 final
labels P>=5 with composite P-2, 6630 twin final
labels, 875 P=3. The generalized time inequality
for all 25 composite cases passed, as did the
terminal and zero-time checks.

Independent BigInt literal-tick gcd embeddings
at Y=31,101,251,997, J=4 prod_(3<=p<=Y)p
and its double. For each A<=Y-1 use the general
criterion Y>=5A+11 or the zero-phase criterion
from section 2. 436 translated root incidences,
3102 literal clock comparisons and 436 exact
wall arrival comparisons, all passed. These
include both positive terminal phases and zero
phases; not a test of factoring J+-1 or the
unrestricted continuation past J.

## 5. Research direction and remaining gap

The negative model removes the unknown location
of termination and exposes a last-jump statistic
that is tightly concentrated in the finite data.
The concrete issue is to prove that the negative
canonical paths cannot all spend at least about
one sixth of A before the last jump, for all large A.
One possible approach is to bound preterminal
gain via the actual negative-time clock maps:
at each negative tick the candidate primes divide
that tick or the tick minus 2, independently of
the initial distance. The evolution of all
negative seeds can therefore be compared on
a shared time axis. No suitable estimate
on their preterminal gain has yet been obtained.

Large synchronization at positive primorial walls
also illustrates why a uniform small merger-mass
bound cannot follow from mere CRT roughness.
No new unrestricted local termination theorem,
no asymptotic synchronization or last-jump bound,
no twin-infinitude proof. No changes to canonical
Lean targets or sibling branches.
