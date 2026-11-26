# Negative MIN: affine priority certificates and adaptive winner law

2026-11-26 JST. Continuation of 1c961a8956cf381d9caeefd69f61d919aae46693.
Restore the least-clock priority conditions missing from the
fixed high-word counting relaxation. Obtain an exact Cartesian
product certificate for finite-alphabet complete event transcripts,
and an exact conditional next-winner law on complete CRT periods.
Also record a finite-interval sieve for fixed long-wait skeletons.
No general upper bound on stopped-prefix wait or twin infinitude.

## 1. Affine candidate clocks

For a canonical root A=6j, before an event write
a=6j-G, v=3-3j+W, where G,W are the cumulative
gain and elapsed completed wait. The event label q
with side e in {-1,+1} is eligible when a=e mod q.
Its clock firing residue is c(q,-1)=0 or
c(q,+1)=q+2 mod 2q. For q>=5 eligibility fixes

    j=r(q,G,e)=6^(-1)(G+e) mod q.

Fix j parity epsilon. The two congruences for j
fix one class mod 2q. Thus the candidate wait

    d(q,G,W,e,epsilon)
      = least positive representative of
        c(q,e)-3+3j-W mod 2q

is constant over that class. This is an exact
conditional candidate time even before knowing the
actual root residue. For q=3 eligibility instead
is independent of j: -G=e mod3. If eligible,
the wait depends only on epsilon and W because
3j mod6 is fixed. Handle this prime by a
deterministic gate, not inversion of 6.

## 2. Exact finite-alphabet transcript certificate

Fix a finite alphabet P of odd primes, and restrict
the clock rule to those primes. Work with the formal
congruence maps on all even distances and integer
clocks, without the physical stopping condition.
For a prescribed complete transcript of events
(p_i,e_i,w_i), not merely the high subsequence,
all G_i,W_i are fixed by earlier entries.

Initialize an allowed set C_q=Z/qZ for each q>=5
in P, and a true gate for q=3. At step i:

* Require p_i in P and its chosen side eligible.
  Intersect C_(p_i) with its required residue,
  or require the deterministic q=3 gate.
  Require the conditional candidate wait to equal w_i.
* For every candidate side (q,e) whose pair
  (d(q,G_i,W_i,e,epsilon),q) is lexicographically
  less than (w_i,p_i), delete r(q,G_i,e) from C_q.
  If an eligible q=3 candidate precedes it, reject
  by the deterministic gate.

The remaining roots of parity epsilon realize exactly
the prescribed prefix if and only if the gate is true
and j mod q belongs to C_q for every q>=5 in P.
Necessity follows from eligibility, clock timing and
priority. Sufficiency follows inductively since the
chosen event is eligible at the specified time and
every earlier competing event is excluded.
All updates are intersections on one CRT coordinate,
including repeated queries to an already selected
prime. A prime's allowed set may be empty.
A transcript containing a wrong wait is rejected.

Let Q=prod_(q in P,q>=5) q. Writing j=2l+epsilon,
on l modulo Q the exact number of roots realizing
the prefix is

    M=1_(gate) prod_q |C_q|.                       (1)

On an interval of N consecutive l values the count
is <=ceil(N/Q) M; if M=0 there are no roots in any
interval. To add the physical stopped-prefix
conditions, intersect with the actual inequalities
on a, n and A. For a prescribed transcript these
are deterministic linear inequalities in j.
No unrestricted physical path is inferred from
a restricted congruence transcript.

For a partial alphabet P containing all labels
selected in a prescribed unrestricted transcript,
the same certificate is NECESSARY, not sufficient:
omitted primes could preempt a selected event.
For roots with A<=X and decreasing positive a,
using all odd primes <=X+1 is enough to make
the certificate exact after imposing the physical
bounds. This enormous alphabet is a formal
description, not an efficient short-interval count.

In particular, every earlier negative answer for
a prime remains as a forbidden residue when that
prime is subsequently selected. Positive-only
fixed-word CRT counting misses these restrictions.

## 3. Adaptive conditional next-winner law

Condition on an exact nonempty restricted transcript
in a full CRT period of fixed parity. By (1) the
residues j mod q are independent and uniform on
their respective C_q. All candidate times at the
next state can be calculated from the transcript.
Order the candidate sides by (d,q), omitting
ineligible deterministic q=3 sides.

Scan that list. If C_q has current size m_q, a
candidate with residue r has conditional success
probability

    h=1/m_q if r in C_q; 0 otherwise.

For eligible q=3 the conditional probability is 1.
On a negative answer delete r from C_q. On a
positive answer the scan ends. Consequently the
probability of a particular next winner is the
product of preceding failure probabilities times
its current success probability. The probability
that all fail is the probability of no next event
in the restricted model. Conditioning on the
winner produces precisely the next transcript's
Cartesian certificate. This is exact even when the
winner and the queried primes depend on previous
events. It replaces the invalid operation of
conditioning the fresh-prime law of 1c961a8 on
the adaptively selected actual word.

A prime not yet selected after m events has at
most 2m forbidden residues. Its conditional hazard
at an unexcluded candidate, before scanning the
current event, is at most 1/(q-2m) when q>2m.
Within the current scan at most one other side
of that prime can have been excluded, so the
corresponding bound is 1/(q-2m-1) when positive.
For a previously selected prime the allowed set
is a singleton (or empty). No uniform lower
hazard follows: a candidate may already be
forbidden. These bounds are full-period statements,
not short-interval conditional probabilities.
They do not give a uniform lower rate of early
firing after arbitrarily many events.

## 4. Finite-interval priority sieve for fixed long-wait skeletons

For actual unrestricted events with source
a=6j-G and wait w, every odd prime q with
2q<w must divide neither a-1 nor a+1, since an
eligible q would fire within 2q. Suppose a fixed
skeleton specifies m distinct completed events
having waits >2z, at cumulative gains G_1<...<G_m,
where z>=5. Between successive such sources the
gain includes the earlier selected jump p-1,
and w<=2p implies p>z. Thus their gain gaps are
at least z-1, so the 2m shifts

    D={G_i-1,G_i+1: i=1,...,m}

are distinct. All these events require
6j-d nonzero modulo every odd prime q<=z
for d in D.

For fixed m, suppose j ranges over N consecutive
integers, all G_i=O(N), and z>=N^epsilon for a
fixed epsilon>0. We obtain the uniform upper
bound for the number of roots compatible with
this fixed skeleton:

    <<_(m,epsilon) N (loglog N/log N)^(2m).        (2)

Indeed outside primes dividing 6 and the nonzero
product of pairwise differences of the 2m shifts,
the 2m forbidden residues are distinct.
Also exclude the finitely many primes <=2m.
The bad-prime product is polynomial in N with
degree depending only on m. For a squarefree
modulus supported on the good primes, the
forbidden-residue sieve input has (2m)^omega(d)
residues and interval remainder O((2m)^omega(d)).
Apply the standard dimension-2m Selberg upper
sieve at a sufficiently small fixed power of N,
using primes <=z; this is the same upper-sieve
argument as 9103219 with fixed dimension 2m.
Mertens supplies (log N)^(-2m); removing bad
primes costs at most O_m((loglog N)^(2m)),
by separating their factors at log N and using
the polynomial bound on their product.
No lower-bound sieve or independence on the
actual adaptive trajectory is needed for (2).

More generally, if selected positive congruences
pin j to a single residue mod Q0 with Q0<=N^(1-delta)
for fixed delta>0, apply the same argument to the
progression parameter of length O(N/Q0+1).
Exclude the primes dividing Q0 as additional
bad primes; their product is still polynomial
in N. Then (2) has N/Q0 in place of N and a
constant depending also on delta. This statement
is for fixed positive residue and fixed skeleton,
not the union over possible words. An incompatible
positive congruence can only remove roots.

Corollary: if a prescribed family of K different
such gain-offset skeletons covers a set of at
least eta N roots, then K >>_(m,epsilon,eta)
(log N/loglog N)^(2m), by the union bound.
Conversely a family with K=o((log N/loglog N)^(2m))
covers only o(N) roots. This is a conditional
entropy obstruction in a finite interval that
does not require an enormous full CRT period.
It requires m fixed, polynomially long waits
and a controlled family of actual gain offsets.
It does NOT bound the number of all adaptive
skeletons. Long total wait W need not contain
m polynomially long waits, and even if it does,
their offset entropy may be much larger than
this logarithmic threshold. The sieve asymptotic
was derived at paper level, not numerically or
formally proved by the audit.

## 5. Executed finite audit and persistence

Source research/min_local_negative_priority_certificate_audit.mjs,
commit 989b9258bdf61ed7dbb8e3eb0e28fcb51482e05c,
blob e3b52081dbf96e57e66d4e7631e84d7b8ff4ae75.
Executed in the ECMAScript research runtime, fetched
at that exact commit and re-executed with identical
output. Reproduce:
node research/min_local_negative_priority_certificate_audit.mjs
No separate Node or Lean invocation.

Use alphabets {3,5,7,11} and {5,7,11,13}, both
root parities, complete periods 385 and 5005
respectively. Formal congruence trajectories up to
four events, without physical stop, include
nonpositive-distance residues. Enumerate all
observed nonempty prefixes and corrupted-wait
negative controls. Compare certificate membership
against the direct winner computation at every
root in the respective full period.

    full-period root incidences             10780
    formal event evaluations                16144
    transcript controls                      1675
    exact root/transcript checks           7223755
    empty transcript certificates             746
    nonempty certificates                     929
    strict reduction from positive-only
      eligibility and timing certificates     567
    forbidden residue deletions             10203
    short-interval count checks               3350
    adaptive candidate branches               5533
    conditional winner histogram checks       1844
    adaptive nonzero prime hazards            1260
    hazards at not-yet-selected primes          954

All assertions passed. The negative controls
include deliberately wrong waits, so the 746
empty certificates are not all due to preemption.
The strict reduction count compares actual
positive-only membership to full priority,
and measures the additional effect of priority.

Independent unrestricted canonical controls:
909 seeds A=120,318,...<=180000; at most
12 completed events, stop before half-crossing
or firing after -1. For every event, inspect all
candidate primes through 97 and additionally the
actual selected labels for partial-certificate
consistency. 8467 events, 406416 prime/side
candidate checks up to 97, 19290 eligible
affine-wait/priority comparisons, 11619 necessary
roughness checks, all passed. The partial
certificate is not claimed exact for all
unrestricted words. Four fixed offset skeleton
controls, 92 local factor checks verify the
2m dimension away from collision primes.
The asymptotic upper sieve and skeleton entropy
corollary are not finite-experiment conclusions.

## 6. Remaining gap

The adaptive winner law is exact under a complete
finite CRT period; the fixed-skeleton sieve gives
a finite-interval result but pays for the number
of skeletons. Neither controls the unrestricted
canonical adaptive process over root intervals of
size comparable to A. In particular, no estimate
has been obtained that forces a positive fraction
of roots, or any unbounded sequence, to have
W(A)/A<1/4. Further progress needs to exploit the
history of excluded residues or compress the
possible long-wait skeletons, without charging
unobserved residue independence on short intervals.
No twin-infinitude proof or Lean verification.
No changes to canonical Lean targets or sibling
branches.
