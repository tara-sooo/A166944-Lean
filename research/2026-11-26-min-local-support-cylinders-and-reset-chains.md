# Frequent/significant support, exact clock cylinders, and reset chains

2026-11-26 JST. Continuation of e90e72b941c05ecbc657823a30f5f48dccbb1ff1.
Paper deductions conditional on the inherited paper capacity lemma where
specified, plus executed finite diagnostics. No Lean verification, novelty
claim, or proof of twin infinitude. No canonical theorem or sibling changed.

## 1. Relax the local support hypothesis

Use the exact ordinary uncut MIN of the plan, starting at (X,X/2+3),
6|X, with D=ceil(X^(3/4)), through the first post-offset >=X+D.
Include the exit event. Suppose every pre-offset is non-twin. Write
g=p-1 for an event gain, w for its wait, and W for total wait.
Inherited facts: W>=D/2-3, w<=2p, w<=2 sqrt(X+D+1), and
each label p has total wait <= C D/log^2 p in this segment
(local-label-diversity note, sections 1--2, pinned parent 5aef6a4).

Let L be the number of distinct p<X^(1/4) occurring more than X^(1/8)
times, and H the number of distinct p>=X^(1/4) having at least one
event 4w>=p-1. Fix 0<delta<1. The following is sufficient for twin
infinitude: an unbounded sequence of multiples of 6 with
L <= floor((1-delta)log_2 log X) and H=o(log^2 X).

Paper proof. Infrequent low labels cost at most
2 X^(1/8) sum_(p<X^(1/4)) p = O(X^(5/8))=o(D), and their event
count is O(X^(3/8)). All significant high labels cost
O(D H/log^2 X)=o(D), including their insignificant events.
The other high events have w<g/4; all gains except the exit
event sum to <D, and its wait is O(sqrt X) under the non-twin
hypothesis. Their cost is <=D/4+O(sqrt X).
There are O(D/X^(1/4)+1)=O(X^(1/2)) high events.

For frequent low labels scan in increasing order as in the inherited
support-gap proof with T=ceil(log X). Stop before the first p>=T with
p>TQ, where Q=2 times the product of included labels. The recursion
Q_i<=T Q_(i-1)^2 and the L bound imply log Q=o(log X) uniformly.
If there is a stop, all remaining frequent low labels cost
O(D L/log^2 T)=O(D/log log X); they interrupt included-label
runs at most D/(p-1)+1 times. If none, this tail is empty.
In either case each consecutive included run costs <=3Q by the
primorial wall. The extra interruptions by infrequent low and all
high events cost O(Q(X^(3/8)+X^(1/2)+1))=o(D).
The tail-interruption cost is O(D/T+Q). Hence the frequent low
cost is o(D). Sum all costs: W<=D/4+o(D), contradicting W>=D/2-3.
All constants are uniform for fixed delta. The finite-twin assumption
makes every sufficiently large reset non-twin throughout, so the
asserted subsequence is sufficient. This is a reduction, not an
existence result. The same argument allows any fixed significance
threshold w>=alpha*g with alpha<1/2.

## 2. Exact finite relative clock cylinders (including absent events)

Put a=X mod 4, t=v-(X/2+3), and G=u-X. At a tick t>=1 use the
pre-tick G. The parity of n=X/2+3+t is determined by a,t.
Let e=1 for even n, -1 for odd n. The exact candidate divisors are
the odd primes dividing the nonzero odd integer
h=2t-G+7 (e=1) or h=2t-G+1 (e=-1)
and satisfying X=e-G mod p.
This follows by eliminating X from the two neighbor and clock
congruences; conversely p|h plus neighbor divisibility implies the
appropriate clock. The chosen label is the least such prime, or none.
The preceding envelope gives G<=2(t-1)+6, hence h>=3 or h>=-3
respectively. Also G>=0, so |h|<=2T+7 for t<=T.
In particular factorization is only of relative-size integers.

For a fixed realizable tick transcript through T, recover G at every
tick from its selected labels. For each p and each tick where p|h:

* if no label is selected, forbid residue e-G modulo p;
* if label r is selected, forbid the residue for p<r, require it for
  p=r, and impose no constraint for p>r.

Intersect these conditions for each p, also impose X=0 mod 3
and the fixed even a modulo 4. Let A_p be the remaining residues
mod p. The transcript is reproduced EXACTLY iff these independent
constraints hold; proof by induction over ticks including unit ticks.
For M_T=4 product_(3<=p<=2T+7) p, its cylinder consists of
product_p |A_p| classes modulo M_T, with relative natural density
(product_p |A_p|)/M_T among all integers. Divide by the reset/parity
density 1/12 for conditional density. In an interval of length R
the count is density*R plus error at most product_p |A_p|.
One may omit unconstrained primes from the modulus. This is an exact
finite count, not an assumption that successive selected labels or
origins are independent. The full modulus is exp(O(T)); a fixed word's
density alone need not bound its contribution at T=X^(3/4).

There is also a finite-prefix obstruction: any realizable fixed word
through T can be made non-twin at every visited offset, including the
last post-offset, on an unbounded arithmetic progression. Choose two
fresh distinct primes >2T+7 for each of the finitely many offsets G;
impose X+G-1=0 mod one and X+G+1=0 mod the other. CRT preserves the
original cylinder; for sufficiently large lifts these are proper
factors. Thus no fixed relative transcript by itself forces a twin.
This does not extend a finite word to a single infinite ordinary ray,
and does not exclude a construction with T growing with X.

## 3. Unconditional supply of quiet starts and reset-to-reset events

For fixed parity a and 6|X, absence of any event through T is automatic
if X avoids both +/-1 modulo every prime 5<=p<=2T+7.
Conversely, if a prime 5<=p<=T/2 divides either neighbor, its
clock fires within T, so no-event roots must avoid these residues.
The exact cylinder density conditional on a and 6|X is therefore
between the products of (1-2/p) with these two cutoffs.
By Mertens' product estimate both products are of order 1/log^2 T
as T grows (their ratio to the square of the usual Mertens product
has a positive convergent limit). For T=floor(c log R) with a fixed
sufficiently small c>0, the full modulus is o(R) by Chebyshev's
theta bound. Counting complete and partial periods in [R,2R)
gives Theta(R/log^2 log R) quiet starts. These starts have first
selected p>T/2 by w<=2p. This is an unconditional initial-event
supply statement, not a full local crossing bound.

More specifically fix a prime p=1 mod 12. Impose X=0 mod 12,
X=-1 mod p, and X not equal +/-1 mod q for all odd primes q<=p+6
other than p (q=3 is already handled). Then the exact FIRST event is
the plus clock at w=(p-1)/2. Indeed the quotient (X+1)/p is 1 mod 4,
so n=(X+p+5)/2 is p+2 mod 2p; its prior clock is 2p ticks earlier.
For every earlier tick and the chosen tick, |h|<=p+6 at G=0,
so all competing labels are excluded. The post-state is
(X+p-1,(X+p-1)/2+3), again a reset divisible by 12.

These sufficient residue conditions have density
(1/(12p)) product_(5<=q<=p+6,q!=p)(1-2/q)
=Theta(1/(p log^2 p)) among integers as p grows.
With p<=c log R for small absolute c, the modulus is o(R)
uniformly. Consequently there are Theta(R/(p log^2 p)) roots
in [R,2R) satisfying this sufficient cylinder. This supplies an
exact large-first-label regeneration without assuming primality
of either neighbor. For example one can choose p=1 mod 12
growing by Dirichlet's theorem, then R sufficiently large.
It does not control the next event.

## 4. Arbitrarily long finite chains of exact non-twin resets

For each fixed integer m>=1 there exists a finite increasing list
of primes p_1,...,p_m, all 1 mod 12, and an arithmetic progression
of unbounded positive integer roots X, for which the first m events
are the short plus clocks w_i=(p_i-1)/2, every one of the m+1
states is a deficit-6 reset divisible by 12, and all m pre-offsets
have two composite neighbors.

Construction. Let B be 12 times the product of odd primes <=2m+3.
Choose p_i by Dirichlet in the class 1 modulo B times the product
of the preceding p_j, with p_i>2m+3 and p_i>2p_(i-1)+6 for i>1.
Put G_i=sum_(j<i)(p_j-1). Impose X=0 mod 12 and X+G_i=-1 mod p_i.
For every q<=p_m+6, q odd prime, exclude X+G_i=+/-1 mod q
at each stage with q<=p_i+6, except when q=p_i (required -1).

These requirements are consistent prime by prime:
- q<=2m+3: all G_i vanish mod q, so X=0 works.
- q=p_j: earlier stages have q>p_i+6; at stage j require -1;
  thereafter the residue of X+G_i is -2 mod q, because all
  subsequent increments are multiples of q. Hence no conflict.
- any other q>2m+3: at most 2m forbidden residues, fewer than q.

Apply CRT. Section 3 applies at each successive reset, giving the
specified exact events. To force non-twin pre-offsets choose m fresh
distinct primes r_i>p_m+6, impose X+G_i=1 mod r_i and lift X above
all factors. The plus neighbor already has proper factor p_i; the
minus neighbor now has proper factor r_i. All m events survive.
An optional two fresh factors at the final post-offset likewise
make that state non-twin.

This gives explicit finite non-twin reset chains with arbitrary
length, not a proof of a long crossing. The construction with
representatives X>=M, where M includes every odd prime up to p_m+6,
has log X >= theta(p_m+6)-O(1), while G_{m+1}<2p_m by the
chosen doubling. Hence this construction reaches only O(log X)
physical gain, not X^(3/4). This is a scale mismatch for these
chosen representatives, not a lower bound on the smallest root
among all allowed residue classes. Obtaining an adequate short
representative or controlling subsequent actual events is open.

## 5. Executed reproducible diagnostics

Run with Node.js (stdlib only):
    node research/min_local_crossing_support_audit.mjs 1000000
    node research/min_local_reset_chain_audit.mjs

Both programs were executed as ECMAScript in the research runtime,
committed, then fetched by exact commit and re-executed from the
returned source. No Node process or Lean process was invoked here.

Source 1 commit 9bc6e058fbd14d25f262c8245523523c57e96e93,
blob ddb745172bd1d1e9407e9b9d1b4811830dc6b11f.
600 literal GCD vs modular first-clock checks; 25000 exact-cylinder
membership vs modular word checks at T=4,8,16,32,64.
All local crossing endpoints, wait bounds and integer D rounding
checked. All final crossing events included. delta=0.1; diagnostic
relaxed criterion H<=3. Inclusive seed intervals:

    range           seeds   twinStart  twinLater   noTwin  old    relaxed    events
    10000..20000     1667         137       1530        0    57        765      25084
    100000..200000  16667         936      15731        0  1209       8971     372077
    500000..1000000 83333        3604      79729        0  4722      41711    2480585

Old/relaxed count only non-twin STARTS, not twin-free crossings.
Total 101667 roots; 2877746 events. No twin-free exit in these slabs,
so the conditional crossing contradiction has no negative-case
control in this experiment. X=500172 gives (p,w)=(7,7),(500179,250085)
with first twin center 500178. These are finite diagnostics; no
asymptotic inference from correlated trajectories.

Source 2 commit 34a45436bd0a16f0b6aa66cb62584d7ea08e9f6f,
blob 1095e8bba19fb84394b593ac154e683e187ce137.
The explicit list 13,37,61,97 is found by direct residue compatibility
rather than the larger sufficient Dirichlet construction. Constructed
root X=15289136289366603614526767246085587658100790149020
modulus 8028953878666072378188882398052090273291770495460.
Minus proper factors 107,109,113,127 at shifts 0,12,48,108;
plus proper factors 13,37,61,97. Waits 6,18,30,48.
102 literal BigInt GCD ticks, all passed; gain 204, deficit 6.
This is a genuine standard-integer non-twin prefix, not a relaxed
clock word. The chosen root's scale makes gain 204 far too small
for the local crossing.

## 6. Next target

Exploit the exact cylinder constraints without enumerating the full
exp(O(T)) modulus: at each step maintain primewise allowed sets and
a bounded integer interval for X, sieve away incompatible words, and
compare the least actual root to cumulative gain. Seek an unbounded
sequence with controlled frequent low support and significant high
support, or a bound on the wait outside reset chains. The explicit
reset-to-reset construction provides a deterministic source of
regenerations, and the finite-prefix obstruction identifies why
fixed residue control cannot by itself prove twin infinitude.
The needed growing-scale existence argument remains open.
