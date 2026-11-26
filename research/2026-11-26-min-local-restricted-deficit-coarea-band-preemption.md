# Deficit coarea potential and dense-band preemption

2026-11-26 JST. Continuation of 43c8442d3cc61867fb4cd657961765b14e70776a.
Replace the uniform small-relay cap for FIRST band activation by a
level-crossing charge on the actual old trajectory. The comparison
works for dense old alphabets, subject to probabilistic old-displacement
and event-count bounds. Exact arithmetic, paper estimates, executed
finite audit. No Lean kernel verification or twin-infinitude proof.

## 1. Quiet-tick opportunities and the conditional CRT law

Let y>=7, A a finite set of odd primes <y containing 3, and
H a subset of the primes in [y,2y]. Let the old canonical
restricted trajectory use A, starting at X=0 mod6 and v0=X/2+3.
Write P=4 product_(r in A)r for the old seed period. For a fixed
old seed residue, all translations X+P k preserve the old relative
trajectory. Modulo the new primes in H, these translations are
independent and uniform over the full enlarged period, by CRT.

Write h=v-u/2 (half the ordinary deficit) at a source, and let w
be the next old waiting time. At a relative tick 1<=j<w put
h_j=h+j and n=v+j. A new clock of prime p in H can fire there
only if

    p | 2 h_j+1   when n is even,
    p | 2 h_j-5   when n is odd.                   (1)

Conversely each such divisibility gives exactly one lift residue
Delta X = e-u mod p (e=+1 even, -1 odd) at which the new p-clock
is eligible at that tick: u translates by Delta X and v by
Delta X/2, with Delta X divisible by 4. For even n the clock
requires p|u-1 and p|n, equivalent to the first expression once
the offset residue holds. For odd n use p|u+1 and p|n-2.
The defects are odd and nonzero. There is no zero-defect
exception. Since p exceeds every old label, equality of clock
times with an old event cannot cause preemption.

Let C_p^pre(X) be the union of these eligible shift residues over
all QUIET ticks of the old path; let C_p(X) add the two eligibility
residues at the old terminal. The exact conditional probabilities
over lifts of this one old seed residue are

    P_pre(X) = 1-product_(p in H)(1-|C_p^pre(X)|/p),
    P_any(X) = 1-product_(p in H)(1-|C_p(X)|/p).    (2)

The first event in H is a preemption iff at least one preemption
opportunity exists; if no opportunity occurs until the terminal,
it fires there iff at least one terminal residue is met. This
uses actual first-clock competition; no independence between
ticks or stages is assumed. Formula (2) is a refinement of the
union computation in 43c8442; it is exact for dense A as well.
A union bound gives P_any<=P_pre+2 sum_(p in H)1/p.

## 2. Coarea identity for the half-deficit

At each old event of label r and gain g=r-1, the height rises
by w during its waits and falls by g/2 at firing. Restricted
nonnegative deficit and w<=3g were established in 56614c0.
Define, for integer h>=1,

    a_y(h)=sum_(p in H) (1_(p|2h+1)+1_(p|2h-5))/p,
    Phi_y(H0)=sum_(1<=h<=H0) a_y(h), Phi_y(0)=0.

For old source height h_i, firing height k_i=h_i+w_i,
arrival height h_(i+1)=k_i-g_i/2, put

    U=sum_i [Phi_y(k_i)-Phi_y(h_i)],
    V=sum_i [Phi_y(k_i)-Phi_y(h_(i+1))].

All terms in U,V are nonnegative, including the last firing
tick in U. The quiet-tick union bound (1)-(2), which only
uses the appropriate parity and excludes the firing tick,
is <=U. Exact telescoping yields

    P_pre(X) <= U = Phi_y(h_end)-Phi_y(3)+V.        (3)

This is an identity for the level occupation weights, not an
identity for the preemption probability: repeated residues
and mutually incompatible opportunities can make the union
bound loose. It applies to any finite old prefix as a bound
on preemption along that prefix; for P_any the endpoint must
be the actual terminal. It replaces the positive-time sum
by charges to downward jumps, of lengths (r-1)/2, and an
endpoint term. No uniform low-run cap is used.

## 3. A dense-band estimate for old paths of linear gain

Fix C>=1. Consider an old canonical trajectory of total
gain G<=Cy and N events. Its every intermediate height,
including firing heights, is in [0,3+3Cy], since the
total waits are <=3G. Every nonzero multiple of a new
prime in either defect in (1) has bounded positive integer
multiplier O_C(1) (for large y; the negative defects have
absolute value <=3). Thus

    Phi_y(h_end) <<_C 1/log y.

Indeed each p has O_C(1) hits and the dyadic reciprocal
prime sum is O(1/log y).

More locally, for any interval I of l>=1 consecutive integer
heights in this height range,

    sum_(h in I) a_y(h) <<_C (l+1)/(y log(2+l)).   (4)

To prove this, write 2h+1=mp or 2h-5=mp, and sum over the
O_C(1) positive m. For each m the prime p must lie in an
interval of length at most 2l+2, intersected with [y,2y].
The standard uniform upper bound for primes in a translated
interval of length L is O((L+1)/log(2+L)) (e.g. the
Brun--Titchmarsh inequality with modulus 1, or the usual
one-dimensional upper sieve). Divide by p>=y. This bound
does not require primes to be uniformly distributed within
individual intervals. Bounded l is covered by the trivial
integer count.

Apply (4) to each downward interval of length g_i/2 in (3).
Since g_i>=2 and log(2+g_i) is comparable to log(2+g_i/2),

    P_pre(X) <<_C 1/log y
            + (1/y) sum_i g_i/log(2+g_i).          (5)

The same estimate holds for P_any, using (2) and the
dyadic prime reciprocal bound. This is a gain-weighted
charge, not a charge proportional to the total waiting
time or to a uniform maximum relay length.

For any z>=2, split the sum into g_i<=z and g_i>z.
Then it is <=Nz+Cy/log(2+z). With
z=max(2,sqrt(y/(N+1))), (5) implies

    P_any(X), P_pre(X)
        <<_C 1/log(2+y/(N+1))                     (6)

uniformly for G<=Cy. This includes N=0 by (2), and when
N is comparable to y the bound is merely O_C(1).
In particular linear old displacement and sublinear old
event count suffice for vanishing activation probability.
This is substantially weaker than the uniform old gain
cap o(log y) from 43c8442. It does NOT assert a bound on
N from G alone. The equivalent useful variant is that the
gain of bounded labels is negligible relative to y as
the label bound tends to infinity after y; see (5).

## 4. Probabilistic dense-band extension theorem

Now let A=A_y consist of ALL odd primes below y, and H
contain ALL primes in [y,2y]. Write G_y,N_y for the old
terminal gain and event count of a uniformly chosen old
canonical seed residue. The following two assumptions
are enough (as y tends to infinity):

    G_y/y is tight in probability,
    N_y/y -> 0 in probability.                    (7)

Here tightness means that for every epsilon>0 there
exists fixed C such that limsup Pr(G_y>Cy)<epsilon.
Sufficient moment conditions are E G_y=O(y) and
E N_y=o(y), by Markov's inequality, but neither moment
bound is proved here.

To see the consequence, average (6) over the old seed
residue and then use (2) and CRT for the enlarged period.
For fixed C, restrict to G_y<=Cy and N_y<=delta*y.
The bound in (6) is O_C(1/log(2+1/delta)) for large y.
The complement costs at most Pr(G_y>Cy)+Pr(N_y>delta*y).
First choose C using tightness, then delta small and
finally let y grow. Therefore

    Pr(any new band label is selected) = o(1).       (8)

If there is no new label, the entire enlarged path
coincides with the old one, including terminal gain.
Couple the old and enlarged periods by projection.
For any D>0, pointwise

    min(G_enlarged,D) <= min(G_y,D)
                         +D 1_(any new label).

Taking D=y^2, tightness of G_y/y implies that
E[min(G_y,y^2)]/y^2 ->0 (bounded random variables
converge to zero in probability). Thus

    E_enlarged[min(G_enlarged,y^2)] = o(y^2).        (9)

This covers a dense dyadic extension without assuming
a uniformly bounded old relay, or any estimates for
second or later high events. Rare activated paths can
have arbitrarily long trajectories, which is why the
gain is truncated. It also does not require the entire
enlarged period to be enumerated. Equations (2)-(6)
can be computed using only old paths.

Under (7), the enlarged distribution of G_enlarged/(2y)
is itself tight and N_enlarged/(2y)->0 in probability
along these same scale pairs, by (8) and coincidence
on unchanged paths. This is a one-step propagation,
NOT an induction proving (7) for all y: accumulating
exceptional sets over an increasing number of dyadic
steps may lose control. The activation estimate need
not be summable across dyadic scales. No recovery of
long outlier paths has been established.

## 5. Local scope and remaining obstacle

The level-crossing identity and exact residue-set
construction are valid for each actual old trajectory
at any absolute X. However the conditional probabilities
in (2), and therefore (5)-(9), are uniform probabilities
over the CRT LIFTS of an old residue. They are not
bounds for the empirical activation probability in a
local slab of length O(y^2). The old period is already
exponential in y for the dense alphabet.

At a fixed actual X, activation is the exact indicator
that some C_p contains the zero shift. The coarea sum
counts the weighted size of these sets, not whether
zero is included. Transferring this weight bound to
actual local origins would require a distribution
estimate for these trajectory-dependent residue sets.
No such estimate is assumed. In particular the local
sample in section 6 compares the two distinct quantities
and does not treat one as an estimate of the other.

This gives two concrete targets for the restricted
termination route: (i) prove tightness of G_y/y and
sublinear N_y/y for the old full-period distribution
(or find a different bound for the coarea charge);
(ii) transfer the resulting small activation or small
displacement bound to intervals of length comparable to
y^2. Neither has been established. The earlier
unconditional periodic lower bound G_y mean
Omega(y/log y) is consistent with (7), but does not
supply it. No twin-infinitude contradiction obtained.

## 6. Executed diagnostic

Source research/min_local_restricted_deficit_coarea_audit.mjs,
commit 429b3aebc4e03a813aad7406430d8e9c611013b5,
blob e9159eded1bfbb7be28e8223b1fb2fbcef1e6bdb.
Executed in the ECMAScript research runtime, committed,
read back by exact commit, and re-executed.
Reproduce: node research/min_local_restricted_deficit_coarea_audit.mjs.
No Node or Lean process invoked here.

Five complete OLD periods, y=7,11,13,17,19. The H
period need not be materialized: compute (2) exactly
from finite residue-set sizes (floating arithmetic
for probabilities). Three separate actual local
samples of 2,000 roots each, y=127,503,997. Old
paths censored if G>64y for period controls or >8y
for local controls; in this run none was censored.
The coarea identity is checked with floating weights.
Independent small-subset comparisons of quiet-tick
residue sets against exact translated p-clock waits,
and independent ACTUAL first high competition for
every tested root.

    kind    y    roots  mean G   mean N   mean P_pre   mean P_any
    period  7      10     2.40     0.80      .10450       .55554
    period 11      70     5.83     1.53      .14636       .53965
    period 13     770    10.15     2.37      .13964       .47904
    period 17   10010    14.13     2.90      .13736       .46006
    period 19  170170    19.09     3.63      .13022       .41645
    local 127    2000   112.34     9.69      .04908       .27351
    local 503    2000   591.59    26.09      .04345       .21927
    local 997    2000   921.62    30.72      .01860       .18753

In the local samples R=100000 for y127 and R=1000000
for y503 and y997, length 12000 in every case. The
last two probability columns for local rows are
averages of conditional lift probabilities computed
from those PARTICULAR local old transcripts, NOT
observed local frequencies. Actual band activations
were 828,578,113 respectively; actual preemptions
82,49,85. The distinct frequencies emphasize the
unresolved distribution problem; the local samples
are also much shorter than y^2 at larger y.

Totals: 187030 root/cutoff incidences, 782136 old
events, 5363128 quiet ticks, 187030 coarea checks,
116622 translated-clock residue checks, 187030
independent actual band-activation comparisons,
all passed. Actual preemptions 23745 and any
activations 77320 across controls. No inference of
(7) from these finite samples, or of an asymptotic
constant in (5)-(6).

No canonical Lean target or sibling branch changed.
