# Restricted prime extension and unavoidable periodic displacement moments

2026-11-26 JST. Continuation of f5e06442d69348dbab08ee25ac0de4a5dfe96292.
Study the terminal displacement target by adding or deleting an actual
clock, not by replacing the lower-only path with an arbitrary displacement.
Exact CRT coupling, sparse extension theorem, a uniform growing-cutoff
lower bound, and a counterexample to pointwise monotonicity. Paper
deductions and two executed finite audits. No Lean kernel verification,
external novelty claim or twin-infinitude proof.

## 1. A coupling for adding one prime

Let A be any finite set of odd primes containing 3.
Restricted MIN uses exactly A with the original first-clock
and least-label tie rule. Let Q=2 product_(q in A) q,
P=2Q. For each canonical root X=0 mod6 with time X/2+3,
write G_A(X) for its terminal displacement and U_A(X)
for its terminal offset. The primorial wall gives finite
termination and gain <=Q for any starting phase.
Translations (u,v)->(u+P,v+Q) commute with the restricted
map. Thus the canonical roots modulo P form a full period.

Let p>=5 be a prime greater than every prime in A and
not in A. The enlarged period is Pp. Each old seed residue
has precisely p lifts X+kP, k=0,...,p-1, with the old
trajectory translated in offset by kP and in time by kQ.
Since p does not divide P, each old source offset u and
each side e=+1,-1 determines exactly one lift
k=(e-u)/P mod p with p|u+kP-e. On that lift the first
p-clock time is completely determined by the actual
translated pre-time. It is invariant under changing the
lift by p, since pQ is divisible by 2p.

For each nonterminal old state (u,v) of old next wait w,
mark that lift if the p-clock wait is strictly less than w.
Equality does not count: every old label is smaller than p.
At the old terminal mark both eligibility lifts, since
there is no old clock. Let C_X be the union of all marked
lifts, and P_X the union from nonterminal states only.

The enlarged path selects p at least once iff k is in C_X:
before its first p selection it is the exact old path,
and at the earliest marked state its next event is p.
The first p selection preempts a nonterminal old event
iff k is in P_X. These are exact finite union formulas;
overlapping residues are counted once. In particular
|C_X|>=2 for every old root residue. No independence
between steps of the old path is presumed.

At any restricted arrival d'=2(v+w)-(u+r-1) is
0 mod 2r (minus) or 6 mod 2r (plus). Starting with
d>=0, w>=1, gives d'>=-r+3. For r>=5 the negative
representatives of those two classes are below -r+3;
for r=3 the elementary lower bound itself is >=0.
Thus nonnegative deficit holds in the restricted
system even if an arbitrary restricted phase does
not satisfy the original upper time envelope.
Also w<=2r<=3(r-1). We only use these two facts.

For a p-preemption at an old state with deficit d,
nonnegativity after the p-step gives p-1<=d+2w_p,
where w_p<=w-1. Consequently a necessary condition is

    p+1 <= d+2w.

Let N_sus(X) be the number of such old nonterminal states.
Then |P_X|<=2 N_sus(X), and |C_X|<=2+2 N_sus(X).
With old total gain G and old total wait W,
d+2w<=6+2W<=6+6G. The number of old events is <=G/2.
Hence

    P(preemption) <= (2/p) E_A N_sus
         <= (1/p) E_A[G 1_(G >= (p-5)/6)],
    2/p <= P(p used) <= 2/p + P(preemption).        (1)

Here E_A is the uniform average over the OLD seed
period, and probabilities on the enlarged period.
The union bound in the second line may be replaced
by 2/p+(2/p) E_A N_sus, which is an upper bound but
NOT necessarily 2/p plus the actual preemption rate
if the terminal classes overlap preemptions.
In fact the exact union yields the displayed
inequality with the actual preemption rate as well.
This identifies the preemption cost in terms of the
actual old displacement tail, not its primorial
worst case alone.

For any lift with no p selected, the terminal is
unchanged. For one first selecting p at the old
terminal, the displacement increases by >=p-1.
For a preemption the new displacement is >=p-1,
so its increase is >=p-1-G. Thus for period means,

    mu_(A+p)-mu_A >= (p-1) P(p used)
                   - E_enlarged[G 1_preemption]
      >= 2(p-1)/p
           - (1/p) E_A[G^2 1_(G >= (p-5)/6)].      (2)

The first inequality is also valid with exact
preemption probabilities from the union formula.
For dense cutoffs the second-moment term can be
large, so (2) is not a positive incremental bound
without extra estimates.

## 2. Sparse extension: exact usage probability and mean increment

Let L be any uniform upper bound on the gain of
an A-only path, for arbitrary even starting offset
and integer clock phase. Q is always valid. One
can compute a much smaller phase-independent
upper bound for small alphabets by the acyclic
offset-only recurrence in a cell [0,Q]:

    F(Q)=0,
    F(u)=max(0, max_(r in A, r|u-1 or u+1)
                          (r-1+F(u+r-1))).

All considered transitions remain in the cell
by the primorial wall. L=max F(u) is valid
regardless of clock selection, including after
an added p-event. This is not a claim that
every maximizing path is realized by clocks.

If p>6L+5, no canonical old path can have a
p-preemption by section 1. Exactly the two
terminal eligibility lifts per old seed use p.
After the p-event, a consecutive A-only run
gains at most L. The next event cannot be p:
two consecutive p-events in the p-subsequence
require an intervening gain E>=p-1. Indeed
the first arrival is 0 or -2 modulo 2p;
the next source is p+1 or p-1 modulo 2p.
The nonnegative even difference E is in one
of the classes p-1,p+1,p+3 modulo 2p.
Since p>=5 and L<p-1, a repeat is impossible.
The A+p trajectory therefore terminates after
at most one added event, with subsequent A-only
gain between 0 and L.

For every changed lift the difference of
terminal displacements is between p-1 and
p-1+L. Every other lift is unchanged. Thus

    2(p-1)/p <= mu_(A+p)-mu_A <= 2(p-1+L)/p.     (3)

In particular along primes p/L->infinity
the mean increment tends to 2.
This theorem permits sparse alphabets, not
only initial segments of all primes.

The same argument applies to a finite interval
of canonical roots of length R by grouping
old seed residues modulo P. Within each residue
class the changed lifts occupy exactly two
classes modulo p, so their count differs from
2/p times the number of roots by O(1). Summing
over at most P/6 classes gives O(P) count error.
Thus the total mean-displacement INCREMENT in
that interval has the corresponding bounds
in (3), with an additive O(P(p+L)/R) error
when N=Theta(R). This uses the old terminal
displacement of the very same roots. It is
useful for sparse extensions with pP=o(R),
but not for the full initial segment of all
primes up to sqrt R (P is far too large).

## 3. Dense extension obstruction: terminal displacement is not monotone

The old terminal can move LEFT when a prime
is added, because an earlier preemption can
bypass a long part of the old path. This is
not just a hypothetical possibility.

Exact restricted-clock example from the audit:
canonical root X=106758, v0=53382.
For A={3,5,7,11}, the path has label/wait list

    7/14, 5/1, 3/3, 7/5, 11/2, 5/3, 3/1,
    3/1, 5/5, 3/1, 7/6, 5/6, 3/6, 7/11.

It terminates at u=106818, displacement 60.
Adding 13 changes the label/wait list to

    7/14, 5/1, 3/3, 13/4,

and terminates at u=106782, displacement 24.
Both terminal states have no admitted prime
factor of their neighbors in their respective
systems. This is a counterexample to the
pointwise inequality G_A<=G_(A+p) even for
consecutive prime cutoffs. It is not a
counterexample to a possible monotonicity
of the FULL-PERIOD MEAN, which is a separate
question. Thus the sparse extension theorem
cannot simply be summed across consecutive
primes on the assumption of nonnegative
pointwise changes.

## 4. Deleting each label gives an unconditional periodic lower bound

Now let A_y consist of ALL odd primes <=y,
with y>=5. For each p in A_y other than 3,
delete p and run the restricted system B=A_y
minus {p}. Its period P_B is coprime to p
and still divisible by 6. In the full A_y
period there are p lifts per B-seed residue.
The deleted-system terminal offset satisfies
p|U_B-1 or p|U_B+1 for EXACTLY two lifts.
On any such lift the A_y trajectory MUST
select p at least once. If it selects p before
the B-terminal, this is already true; otherwise
it follows the B-trajectory exactly until that
terminal, where p is eligible and the only
new clock. For this inclusion, p need NOT
exceed the other labels. Ties with larger
old labels cause no problem: until p actually
wins the enlarged dynamics are identical.

Let I_p be the indicator that p appears at
least once on the full restricted trajectory.
Uniformly over the full A_y seed period,

    E_y I_p >= 2/p.

This lower bound holds simultaneously for
every p separately; no mutual independence
of the I_p is required. Consequently

    E_y[# distinct used primes >=5]
           >= 2 sum_(5<=p<=y) 1/p,
    mu_y=E_y G_y
           >= 2 sum_(5<=p<=y) (p-1)/p.             (4)

More generally, for any fixed integer k>=1,
G_y^k >= sum_(p>=5) I_p (p-1)^k by nonnegative
gain and the elementary superadditivity of
integer powers on nonnegative numbers. Thus

    E_y G_y^k >= 2 sum_(5<=p<=y) (p-1)^k/p
                         >>_k y^k/log y.           (5)

The last estimate follows from the standard
prime number theorem on [y/2,y], or the
corresponding dyadic prime count lower bound.
For k=1 the explicit lower sum in (4) is
asymptotic to 2 pi(y), hence ~2y/log y.
These are lower bounds, not asymptotics of
the actual moments.

There is also a direct band tail lower bound.
Delete all primes in a set D subset A_y with
3 not in D and let B=A_y minus D. For each
B-seed residue, the full lifts modulo product
of deleted primes have independent uniform
terminal residues at those primes by CRT.
Whenever at least one deleted prime divides
a B-terminal neighbor, the full trajectory
uses SOME deleted label (possibly earlier).
Therefore, if m=min D,

    P_y(G_y>=m-1) >= 1-product_(p in D)(1-2/p).     (6)

For D the primes in (y/2,y], this gives a
fraction >>1/log y of roots traveling at
least y/2-1. This is a deterministic period
count and does not assume independent clocks
along the actual path.

Equations (4)-(6) rule out any full-period
upper bound mu_y=O(log^C y) for fixed C, a
possible overly strong target suggested by
the preceding entrance-energy comparison.
They do NOT rule out mu_y=o(y^2), which is
consistent with the desired square-root
local termination scale. Nor can they
directly transfer to intervals of length
O(y^2): full periods have exponential
length. This is an actual quantitative
constraint on the periodic approach, not
a twin-prime scarcity theorem.

## 5. The unresolved dense cutoff step

The previous note reduced twin infinitude
to short restricted terminal displacement
at cutoff T>sqrt(3R+1). The present sparse
extension (3) gives exact control of large
gaps in the admitted alphabet and (1)-(2)
is a coupling of actual clocks even for
consecutive primes. But the uniform bound
on the mean increase in a DENSE band is
not proved. After the first new label the
subsequent trajectory can include repeated
new labels, and the mean increment may
have contributions from old preemption
tails. The full-period lower bounds show
one cannot hope for uniformly polylogarithmic
mean displacement on that period.

A concrete remaining target is an upper
bound on the cumulative gain from all
new labels and their intervening old runs
in a dense dyadic extension, retaining
actual preemption and allowing repeat
labels. Even a full-period upper bound
o(y^2) would still require a separate
short-interval transfer at R comparable
to y^2. The sparse local transfer condition
pP=o(R) does not cover that domain.
No favorable unbounded reset family,
twin-infinitude proof or Lean verification.

## 6. Executed finite audits and persistence

(a) research/min_local_restricted_prime_extension_audit.mjs
commit 8f11743a4a3fe67bbe603b888913be888e6bdc50,
blob cd4f55c99b088d01404d2269d4656c6c2f1e05ce.
Eight complete lifted seed-period controls:
consecutive additions 5,7,11,13,17, and sparse
additions 101 to {3,5}, 293 to {3,5,7}, 907 to
{3,5,7,11}. The last two meet p>6L+5 using
offset-only L=46 and 148 respectively; the
101 control with L=16 is just outside this
sufficient condition (101=6L+5) but also has
no preemptions empirically. The all-prime
base caps for max prime 3,5,7,11,13 are
4,16,46,148,436 respectively.

900940 lift/root incidences; 900940 exact
union comparisons against the actual enlarged
restricted clock paths. 31708 changed roots,
9098 preemptions, 22610 first additions at
old terminals, 472 negative displacement
changes (56 on adding 13,416 on adding 17).
2226 repeat-relay checks, 253 literal GCD tick
checks. All assertions passed.

    old alphabet       added p   mean increment   preemptions
    <=3                  5        2.400000          0
    <=5                  7        3.428571          5
    <=7                 11        4.316883         48
    <=11                13        3.983616        616
    <=13                17        4.959335       8429
    <=5                101        2.067327          0
    <=7                293        2.053047          0
    <=11               907        2.023543          0

(b) research/min_local_restricted_label_deletion_audit.mjs
commit abc97d21f87b018d6a81d62bf8c9ec85c006853c,
blob 7a3e2486a30d87ed081a21a6dafefd5d058304f8.
Full period y=5,7,11,13,17, delete each
admitted p>=5 in turn, then compare actual
full trajectories with every CRT lift of
the deleted-system terminal. 181030 root
incidences, 649156 full events, 216384
deleted-system steps, 893350 per-label
deletion controls. Every forced usage
count equals 2N/p exactly; every forced
root actually uses that p. All gain and
squared-gain moment comparisons passed.

    y    roots   mean gain   lower bound (4)
    5      10       2.4000        1.6000
    7      70       5.8286        3.3143
    11    770      10.1455        5.1325
    13  10010      14.1291        6.9786
    17 170170      19.0884        8.8610

At y=17, p=5,7,11,13,17 forced counts
68068,48620,30940,26180,20020, and actual
usage counts 93982,70799,47804,39317,27663.
Counts overlap across primes; not independent
samples. The analytic moment lower bounds
are deductions, not fitted rates.

Both scripts were executed as ECMAScript
in the research runtime, committed, fetched
at the exact commit, and re-executed with
identical output. No Node or Lean process
invoked. Reproduction:
node research/min_local_restricted_prime_extension_audit.mjs
node research/min_local_restricted_label_deletion_audit.mjs

No changes to canonical Lean targets or
sibling branches.
