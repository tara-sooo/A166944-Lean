# Negative MIN: high-alphabet exposure, idle-height occupation, and sublinear stopped gain

2026-11-27 JST. Continuation of f8b242186833d37c9b728dbd99819c560c3461b1.
The previous record-return study isolated first-use old-prime traffic.
Here we instead delete an entire HIGH alphabet and use the common
low-only path to determine the exact first-high-event law, including
events below the previous record. A discrete occupation identity removes
all prime-3 firings from the extra idle-height exposure. We derive an
unconditional formal stopped-gain estimate for EVERY sublinear gain
budget, rather than just the earlier polylogarithmic budgets. A
one-dimensional downward-overlap moment and an aggregate single-prime
discrepancy separate the remaining dynamical and arithmetic obstacles.
For a fixed low alphabet with a macroscopic gap, actual square-root
high-band union probabilities admit a direct first/second-moment CRT
transfer. This is not the transfer for the full growing low alphabet.
Paper-level deductions, no Lean verification, no proof of twin infinitude.

## 1. Exact first-high-event law on the deleted path

Canonical root A=6j, absolute birth n_A=3-A/2, height 3.
At elapsed tick t>=1 let b=3+t-G_(t-1)/2 be PREheight,
n=n_A+t. The least eligible odd prime fires, or the tick
is idle. The height factor is 2b+1 if n is even and
abs(2b-5) if odd; the spatial pin is a=-1 mod p in
the first case, a=1 mod p in the second. With a=A-G,
the required root residue is

    A == G+sigma mod p, sigma=-1 or +1.

Write p=1 on idle ticks. Then postheight is b-(p-1)/2.
Through T ticks G<=2T+6 and all eligible labels <=2T+7.
These identities hold in the formal CRT environment and
on actual slabs R<=A<=2R, 6|A, T=ceil(8 sqrt(2R+1))
for sufficiently large R (before physical termination).

Use disjoint finite alphabets P and Q, with 3 in P and
every q in Q larger than every prime in P. In the main
application P is the set of odd primes <=Y, and Q the
primes Y<p<=2T+7. Fix the root parity j mod2 and all
P coordinates; follow only P through elapsed T.
No Q prime can beat a P winner at the SAME tick,
because it is larger. Thus the first event from Q in
the combined process can occur only at a P-idle tick.
Before that event the two paths coincide.

At each P-idle tick list Q divisors of the height factor
in increasing order and record the corresponding root
residue pin for each. For q in Q let D_q be the SET of
distinct tested residues and d_q its cardinality.
The list, including its order, depends only on the
fixed low coordinates. Conditional on these coordinates,
the A mod q are independent uniform residues for q in Q.

Therefore the exact conditional probability of no
Q firing by T in the combined process is

    S = product_(q in Q) (1-d_q/q).                     (1)

Scan tests by tick and label. Ignore a repeated residue
at a prime; if there have already been k distinct denied
residues at q, the next new test has conditional success
probability 1/(q-k) given survival. Its unconditional
first-winner probability (still conditional on P) is the
current survival divided by q-k. This gives the entire
first event's time, label, and source gain law. If survival
is zero, later first-winner weights are zero. No repeated
negative residue is charged again. This is exact even
with a long history, including repeated visits to a
height and any dependence within the low alphabet.

The same deterministic test list on an actual integer
root identifies the first Q event exactly by its first
matching pin, when running the combined alphabet.
There is NO assertion of a conditional uniform high
coordinate law on an actual finite interval with a
growing low primorial.

In the main application Q contains every omitted
eligible prime, so the probability of ANY high firing
on the full formal trajectory is E_P(1-S). In particular

    Pr(any p>Y) <= E_P sum_q d_q/q.                       (2)

Couple the full and low paths by the same root coordinates.
They differ only if the first high firing occurs.
The total gain from high labels, including repeats
and events below the record, has expectation at most
(2T+6) Pr(any p>Y). Also

    |E G_T - E G_T^(<=Y)| <= (2T+6) Pr(any p>Y).          (3)

These are fixed-time inequalities. The probability
bound does not itself show that the retained low
alphabet has small gain.

## 2. Exact idle-height occupation identity

On ANY completed finite prefix of the low path let
h_end be its final postheight and L(b) the number of
idle ticks with preheight b. Start from height 3.
For a completed nonidle event e of preheight b_e and
label q_e, put k_e=(q_e-1)/2 and define its integer
INTERIOR descent interval

    I_e=[b_e+1-k_e, b_e-1] intersect Z.

It is empty for q_e=3. Its cardinality is k_e-1.
Let D(b)=sum_e 1{b in I_e}. Then pointwise

    L(b)= B_end(b)+D(b),                                (4)

where B_end is 1 on [4,h_end] if h_end>=3, or -1 on
[h_end+1,3] if h_end<3, and zero elsewhere.
Indeed successive preheights satisfy
b_(t+1)=b_t+1-k_t, k_t=0 on idle ticks.
Telescope any discrete antiderivative:
an idle tick adds its weight at b_t, and a firing
subtracts the sum on [b_t+1-k_t,b_t-1].
The endpoints are b_1=4 and b_(T'+1)=h_end+1
for the completed prefix length T'. This proves (4)
for every height, including the signed low endpoint
case, and yields for arbitrary weights w(b)

    sum_idle w(b) = sum_b B_end(b)w(b)
                      +sum_e sum_(b in I_e) w(b).

Prime 3 contributes ZERO to the excess occupation
of idle ticks; treating its jump as a closed interval
of length one would overcount.

Use the nonnegative high-clock weight

    beta_Y(b)=sum_(Y<p<=2T+7)
       [1{p|2b+1}+1{p|abs(2b-5)}]/p
          (1<=b<=T+3).

One actual parity is used at each idle tick, while
beta includes both. Define the baseline and toll

    B0(T,Y)=sum_(1<=b<=T+3) beta_Y(b),
    W_Y=sum_e sum_(b in I_e) beta_Y(b).

Equations (1)-(4) imply

    Pr(any p>Y) <= B0(T,Y)+E W_Y.                         (5)

For the first high event STRICTLY BELOW the previous
maximum preheight, the baseline can be omitted:

    Pr(first high below record) <= E W_Y.                 (6)

Proof: if b>=4 has already been exceeded, there
was necessarily an earlier idle tick at b to
cross up to b+1. The first idle at a given b>=4
is at the running record (including a return to
the same record after earlier firing).
Thus at most L(b)-1_{L(b)>0} idle ticks there
are below record; by (4) this is <=D(b).
For Y>7, all high clock heights are >=4.
Sum possible first-match probabilities using
the union bound over those below-record tests.
This includes the full contribution after such a
first event, via (3); no merger-energy cap is needed.
The record-first high population is also at most B0,
by at most one record idle at each high height.
The earlier first-use record result of f8b2421
is consistent with this stronger group-level approach.

## 3. Uniform elementary bound and sublinear gain stopping

Assume Y>sqrt(2T+7). At each height at most one
prime >Y divides each of the two height factors.
So beta_Y(b)<=2/Y. For each p, each side's possible
heights lie in a single class mod p and have
O(1+T/p) occurrences. Chebyshev's upper bound
on primes, summed over dyadic intervals, gives

    B0(T,Y) << sum_(Y<p<=2T+7) (1+T/p)/p
             << T/(Y log Y).                             (7)

Indeed p<=2T+7, and sum_(p>Y)1/p^2 <<1/(Y log Y).
The sum of the interval lengths |I_e| is <=G/2.
Consequently W_Y<=G/Y on every low prefix.

For an arbitrary gain budget J>=0 stop at the
first completed firing whose gain exceeds J,
or at T if none. Call its total gain G_stop(J).
To bound its overshoot, follow the Y-low
process only until just BEFORE its first
jump crossing J, or until T. A crossing
tick with a low winner cannot be preempted
by a high prime. Every full trajectory with
a first high event and pre-gain <=J has that
event on the resulting low idle list, up to
the first high event itself. The retained
completed low prefix has gain <=J, so (5)-(7)
apply with W_Y<=J/Y. In particular

    Pr(G_stop(J)>J+Y)
        <= Pr(first p>Y before gain crossing)
        << T/(Y log Y)+J/Y.                              (8)

The event at pre-gain <=J may itself cross J.
No assumption that the low process is absorbed,
or that the prior event count is small.
This estimate is purely formal, using independent
high coordinates conditional on the low ones.

Let T grow and J=o(T). Write B=J+T/log T.
For Y>=B and Y<=2T+6, log Y comparable
to log T and Y>sqrt(2T+7) for large T.
Integrate the tail of G_stop-J (positive
part); it is bounded by 2T+6, and on
[Y=B,2T+6] its tail is O(B/Y). Thus

    E G_stop(J)
       << B [1+log((2T+6)/B)] = o(T).                    (9)

The range of (9) includes J=T^alpha for
every fixed 0<alpha<1 and even any
J/T tending to zero. For example with
J<=T/log T the upper bound is
O(T loglog T/log T). Equivalently for
any J=o(Y), Y>=T/log^B0 T, fixed B0<1,
the probability of a first high event
before the gain cap is o(1).
This substantially extends the FORMAL
initial-stage estimate beyond local
polylogarithmic gain budgets. It does not
show E G_T=o(T): gain can still grow
gradually after crossing J. In particular
it is not the actual-slab stopped estimate
for polynomial J; the previous actual
local transfer range is unchanged.

## 4. Replace cohort energy by one-path height overlap

The downward occupation has the exact second moment

    Z_T=sum_b D(b)^2
         =sum_(e,f) |I_e intersect I_f|.                 (10)

This is an ordered pair of events on ONE path,
not a pair of canonical roots. For any z define
D_{<=z}(b) and Z_{<=z} by retaining just
labels <=z in those intervals.
At Y>sqrt(2T+7),

    sum_b beta_Y(b)^2
       << sum_(Y<p<=2T+7) (1+T/p)/p^2
       << T/(Y^2 log Y).                               (11)

The factor two in the first bound comes from
at most two terms in beta. The last dyadic
sum uses sum_(p>Y)1/p^3 <<1/(Y^2 log Y).
Cauchy on heights followed by Jensen gives

    E W_Y <= C sqrt(T E Z_T/(Y^2 log Y)).                (12)

Thus for Y=cT, c>0 fixed, a sufficient
condition for the entire high-label gain to
be o(T) is

    E Z_T=o(T log T).                                   (13)

Only the low-only process with cutoff Y
is needed in this moment, and the statement
controls BOTH record and nonrecord high
events and their repeats. In the wider band
Y=T/log^B T, B<1/2, the stronger E Z_T=O(T)
would also suffice by (7),(12).
No estimate of root-coalescence energy is
required for this sufficient condition.
Equation (13) is not yet proved.

There is a further reduction to fixed small labels.
For fixed c>0 and Y=cT, consider any interval
I of ell consecutive heights in [1,T+3].
Each high clock in it has 2b+1=kp or
2b-5=kp with positive k<=K_c, fixed.
For fixed k and sign the possible primes lie
in an interval of length <=2ell/k+O(1).
For ell>=L large choose a small-prime
primorial Q with primes through a suitably
small multiple of log L, so Q<=sqrt L.
The number of primes >Y in that interval
is bounded by its length times
prod_(q|Q)(1-1/q)+O(Q) (for T large,
Y exceeds all those fixed small primes).
Mertens and sum over the finitely many k
give a uniform upper bound

    # high-clock heights in I
             <= C_c ell epsilon(L),
    epsilon(L)=O(1/loglog L+1/sqrt L) ->0.               (14)

The count is an upper bound even for
possible multiple high factors. No lower
prime distribution in short intervals
is used. A usual short-interval upper
sieve could sharpen epsilon, but is
unnecessary here.

Fix z>=7 large, so any descent interval
of a label >z has length >=(z-3)/2.
By (14), its toll is <=
C_c epsilon((z-3)/2) |I|/Y.
The total long-interval length is <=T+3.
The short-interval contribution satisfies
(12) with Z_{<=z}. Hence

    Pr(any p>cT)
      <<_c 1/log T+epsilon((z-3)/2)
                       +sqrt(E Z_{<=z}/(T log T)).       (15)

It is sufficient to prove, for every
fixed z, E Z_{<=z}=o(T log T), and then
let z tend to infinity after T.
Even the weaker localized condition
E sum_(e:q_e<=z, I_e meets B)
|I_e|=o(T) suffices, where B is the
set of high-clock heights. Thus the
small-label obstruction is specifically
repeated descents crossing rare clock
heights, not arbitrary small-label gain.
The finite diagnostics below show low
occupation moments, but neither sufficient
condition is established asymptotically.

## 5. Actual slab: a single-prime discrepancy criterion

Take actual R<=A<=2R, 6|A, T as above.
For each A compute its Y-low path and
its deterministic distinct pin sets D_p(A)
as in section 1. The full path has at
least one >Y event iff some A mod p
belongs to D_p(A). Define

    W_R=E_R sum_(p>Y) |D_p(A)|/p,
    Delta_R=sum_(p>Y) [
         Pr_R(A mod p in D_p(A))
            -E_R |D_p(A)|/p ]_+.

Then without any CRT independence assumption,

    Pr_R(any p>Y) <= W_R+Delta_R.                         (16)

The deterministic height estimates give
W_R<=B0+C sqrt(T E_R Z_T/(Y^2 log Y)),
or its fixed-small-label version (15).
Therefore for Y=cT the conditions

    Delta_R=o(1), E_R Z_T=o(T log T)

suffice for actual expected high gain=o(T).
This separates a one-prime upper discrepancy
from the dynamical overlap moment; one
does not need joint TV transfer of the
complete trajectory. However Delta_R
involves pin sets chosen by the entire
low path. It has not been bounded for
the growing low alphabet. A small aggregate
actual probability in a finite sample
does not imply small positive-part
discrepancy.

For contrast, if P is a prescribed finite
alphabet with period M=2 prod_(q in P,q>=5) q,
j=A/6 on each class mod M determines
the low path and its entire test list.
For Q above every prime in P, and N_R
canonical roots, the number in this
class matching any one of its d_p
residues is <=d_p(N_R/(M p)+1).
Sum classes and primes. With p_max the
largest Q prime,

    Pr_R(any Q event in P union Q)
      <= (1+M p_max/N_R)
                      E_period(P) sum_(p in Q) d_p/p.   (17)

The mean on the right is over all M low
root classes, not an empirical conditional
distribution. This works for arbitrary
fixed or growing P with small enough period.
For the FULL rule, it is also an upper
bound for its first event OUTSIDE P being
in Q, even if there are omitted intermediate
labels: prior to that event the path has
used only P. It is not an upper bound
on later high events after other omitted
labels have occurred.

## 6. Actual square-root gap model: a relative first-event transfer

Fix P once and for all, including 3.
Its wall bound gives bounded absorption
gain and duration, uniformly over the
finite canonical period. Fix 0<c<d<1/2.
Use only P plus Q={primes cT<=p<=dT}.
For all sufficiently large R, no Q
prime can fire before P absorption,
by the bounded preheight of the
absorption path and the minimum
preheight (p-1)/2. At the absorber
a=A-G_P(A), 6|a, all P clocks
are absent. If any p in Q divides
a+/-1, it has a clock within 2p
ticks, so absorption plus that
wait fits T. Thus the event
that any Q prime fires is exactly
the union of the two spatial pins
for each p at the P absorber.

On each fixed j mod M class,
a=6j-G_P(class), so each p
has exactly two pins. CRT counts
give individual root probabilities

    Pr_R(p divides a+/-1)=2/p+O_P(1/N_R),

and for distinct p,q joint
pin probabilities

    4/(pq)+O_P(1/N_R).

Here p>=5 and distinct signs
are disjoint for a given p.
Sum p and use Bonferroni.
Since #Q=O(T/log T) and
N_R comparable to T^2, the
total pair correction is
O_{P,c,d}(1/log^2 T), including
the CRT remainders even though
p q is of order R. The single
errors sum to O_P(1/(T log T)).
Therefore

    Pr_R(any Q event in P union Q)
       = 2 sum_(p in Q) 1/p
                       +O_{P,c,d}(1/log^2 T)
       ~ 2 log(d/c)/log T.                             (18)

The final asymptotic uses the classical
PNT and partial summation on the fixed
ratio band. The argument also proves
the analogous first-moment approximation
on the formal product model. This is
a genuine actual square-root transfer
without high-prime joint CRT equidistribution:
first and second moment errors suffice
because the event is asymptotically rare.
It is for a GAP alphabet, not the full
rule containing all intermediate primes.
The full-rule first-outside-P event in Q
has the upper bound from (17); the lower
asymptotic (18) cannot be asserted there.

## 7. Executed audits

All three scripts were executed in the ECMAScript
research runtime, fetched from their exact remote
commits and re-executed with matching outputs.
Reproduce with node. No separate Node or Lean
invocation, no new external literature research.

A. research/min_local_negative_high_alphabet_exposure_audit.mjs
   commit e0e7a32b34cc2fcbd250e49e763a73b2f35b3fbb
   blob 32ad21c1e8d1118d2c63c1662e489cbff5ff41ed

Three complete formal controls with (T,P,Q) equal
to (12,{3,5},{7,11,13}), (22,{3,5,7},{11,13,17}),
(34,{3,5,7},{11,13,17}). For every low class
enumerate all high-coordinate lifts. Compare exact
first event time/label distributions, no-event
probability and occupation identity. Four actual
slabs R=12000,48000,192000,480000, with T as above
and Y=ceil(T/4),ceil(T/8),ceil(T/16); deterministic
subsamples of approximately 384 roots per control.
Compare first matching pin to full simulation
including stop at gain floor(sqrt T). Actual
proxy in the output is the product formula
evaluated on the actual low path, NOT an estimate
of the conditional actual probability. Counts:

    low period classes                     150
    full lifted canonical roots        350350
    product checks                        9174
    first-event law comparisons            877
    weighted occupation checks            9024
    empty prime-3 toll checks             39001
    actual root/cutoff controls           4437
    actual first-event comparisons        4437
    stopped first-event comparisons       4437

All assertions passed. At the largest R,
Y=1960 (ceil(T/4), T=7839), among 383
sampled roots actual any-high fraction
.01044, product proxy .29754. For
Y=980, actual .08094, proxy .43809;
for Y=490, actual .25326, proxy .55159.
The gap is a concrete warning against
substituting the product law directly
on growing-period actual slabs.
The mean actual-low-path toll W_Y is
.00900,.05305,.06568 respectively;
the first-high-below-record fractions
are .00522,.01305,.02350.

B. research/min_local_negative_formal_height_occupation_audit.mjs
   commit bfac7f612f5ba84383f87fcbef1d671ae4ccc039
   blob 8a114b0e73ba979e61196210b5c993b9304b4170

Pseudorandom coherent formal CRT environments:
uniform root half-distance parity, independent
A mod p at p>=5 sampled lazily; A mod3=0.
T=256,1024,4096,16384,65536, cutoff
Y=ceil(T/4),ceil(T/8). Sample 512 paths
per control through T=4096, 256 through
T=16384, 96 at T=65536. Compare product
and direct first event, pointwise (4),
and (10) on a small independent interval
pair-sum control. Counts:

    formal sampled paths                   3776
    low tick updates                   26476544
    pointwise occupation comparisons   26487872
    product and first-event checks    3776 each
    prime-3 interval controls             25201
    independent overlap pair-sums           16

All assertions passed. For Y=ceil(T/4)
(the following are sample means):

    T      E Z_T/T   E Z_<=31/T  E W_Y    Pr proxy
     256    .20139     .11313     .09491    .44899
    1024    .20535     .05381     .04649    .37450
    4096    .20818     .02500     .03450    .32014
   16384    .11763     .00812     .01284    .28015
   65536    .10352     .00325     .01103    .24968

Here Z uses downward-interval overlap,
not total idle occupation. At T=65536
the maximum sampled idle local time
at a single height is 25, mean of
maximum per path 7.6979. E G_T/T
(full formal gain) is .26548 in
the 96-sample control. For Y=ceil(T/8)
the analogous mean full gain ratio
is .29150. The finite samples are
not evidence of a proved asymptotic
bound or actual square-root transfer.
In particular (13) remains open.

C. research/min_local_negative_fixed_alphabet_gap_transfer_audit.mjs
   commit ccd0828a10aad9b158a7f00278765c77da0a0d14
   blob f513c8bb144a5f79ffa16369f3cfa37dbc7b9223

P={3,5},{3,5,7},{3,5,7,11}, exact absorption
profiles on their full canonical periods.
Actual slabs R=48000,192000,480000,1000000,
Q=[ceil(T/8),floor(T/4)] primes.
All canonical roots; count exact absorber
single and pair pins, compare with CRT
counting error bounds, and independent
gap-alphabet race simulation every 97th
canonical root. Counts:

    period roots                            850
    actual root/alphabet controls        860010
    eligible spatial pin checks          161944
    independent gap race checks            8871
    single-prime CRT bounds                1377
    two-prime CRT bounds                  93684
    Bonferroni checks                        12

All assertions passed. For largest R=1000000,
T=11314, 187 high primes. The first-moment
prediction 2 sum 1/p=.18500177. Actual
gap occurrence fractions for the three
low alphabets are .17633965,.17600365,
.17655565. The last control's actual
single and pair moments are .18505763
and .00850198. The fixed-gap prediction
is not an approximation for full MIN
with the intermediate primes restored.

## 8. Remaining proof and target

The entire first-high-event probability is now
reduced to a product over distinct residue
tests on a common low path. The downward
interval identity provides a new one-path
moment, removing all prime-3 contributions
and isolating the extra exposure of clocks
below the record. The unconditional formal
stopped-gain bound (9) holds for every
J=o(T). The actual fixed-gap result (18)
demonstrates rare-event transfer at the
square-root scale with fixed low period.

For the growing low alphabet at Y=cT the
missing estimates are the one-path overlap
bound (13) (or localized fixed-small-label
version (15)) and actual one-prime positive
discrepancy (16). Even if both are proved,
macroscopic-label gain alone is controlled;
the cumulative smaller-label gain must
still be bounded to obtain E_R G_T<T/3.
The deleted-path cross-correlation problem
of f8b2421 is not solved by these reductions.
No twin-prime proof, Lean verification,
canonical target or sibling-branch change.
Context was left unchanged per the user's
explicit writeback preference.
