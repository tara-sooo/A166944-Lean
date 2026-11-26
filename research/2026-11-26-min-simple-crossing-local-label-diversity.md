# Local prime-label capacity and growing support in stable carriers

2026-11-26 JST. Continuation of d3cb4323a397d221fbc85946bd393a98a6d4cccf.
Focus: obtain bounds on long stable transport that do not require bounding
the size of a cohort. New paper deductions and an executed audit.
No proof of full wait o(R^2), twin infinitude, or Lean verification.

## 1. Uniform local capacity of a single label

Retain common-boundary MIN: seeds X in [R,3R/2], 6|X, reset
(X,X/2+3), stop at first U>=2R. Let M=R/12+O(1).
At an even non-twin pre-offset u let q(u)=min(lpf(u-1),lpf(u+1)).
For an actual event label p, wait w<=2 min(p,q(u)). Also
q(u)<=sqrt(2R+1). All source offsets in a path are strictly increasing.

Set D=ceil(R^(3/4)). For any real interval I of length <=D in [R,2R)
and odd prime p define the unweighted ambient capacity

    C(I,p)=sum_(u in I, even non-twin, p|u-1 or p|u+1) 2 min(p,q(u)).

Then, uniformly in I and p,

    C(I,p) << D/log^2 p.                                  (1)

In particular the actual sum of waits with label p in ANY single
trajectory segment in I satisfies (1). The bound holds regardless
of the phase, cohort mass, ancestry, or number of events.

Proof. For p>sqrt(R) log^3 R, there are at most 2(D/p+1)
eligible source offsets. Thus C(I,p)<<D/log^3 R+sqrt R
<<D/log^2 p, since only p<=2R+1 can occur.
Otherwise p<=sqrt R log^3 R and D/p>=R^(1/4)/log^3 R.
Split the offsets into q<=sqrt(p)/2 and q>sqrt(p)/2.
The first part costs O((D/p+1)sqrt p)=O(D/sqrt p).
In the second part write the selected neighbor as pm and the
other as pm+/-2. For either sign, m ranges over an interval
of length <=D/p+O(1); both m and pm+/-2 avoid all odd prime
factors <=floor(p^(1/20)) for sufficiently large p.
For each such sieve prime ell the two roots of m(pm+/-2)
mod ell are distinct because ell<p and ell is odd.
Apply the explicit two-form Selberg upper sieve in the inherited
research/2026-11-26-min-primorial-record-displacement-and-supply.md,
section 3, with cutoff floor(p^(1/20)). The bound is

    O((D/p)/log^2 p + p^(3/10)).

Uniformly over this range the error is absorbed, since
p^(3/10)<=R^(3/20) log^(9/10) R and
D/p>=R^(1/4)/log^3 R. Multiplying by 2p proves (1).
Bounded p are covered by the trivial count after enlarging the
absolute constant. If m=1 it is allowed by the sieve.
This proof does not require p to be the least factor, p<=Cq,
a square-root scale hypothesis, or a long actual wait.
It uses arithmetic supply of both neighboring forms.

The same proof works for D>=R^(1/2+epsilon) and D<=R with fixed
epsilon>0, by taking a sufficiently small positive power of p in
the sieve cutoff; constants may depend on epsilon.
For the rest fix D=ceil(R^(3/4)).

## 2. Support gap lemma, independent of mass and phase

Let P be the set of distinct labels in a consecutive non-twin
path segment with all pre-offsets in an interval I as above.
The last event is included even if its arrival lies outside I.
For any subset A of its labels put Q=2 product_(p in A) p.
Consecutive events with labels in A cannot strictly cross a multiple
of Q: if u<J is such a multiple and p|u+-1, the positive even
distance J-u is >=p-1. At J none of the A labels is eligible.
Hence each maximal consecutive A-run has gain <=Q and wait <=3Q,
by w<=2p<=3(p-1).

Suppose A consists of the labels below a cut p_* (the least remaining
label). The number of events with labels >=p_* is at most
D/(p_*-1)+1, since all gains except the final one telescope to
at most D. Combining the run bound with (1) gives

    W(I) <= 3Q(D/(p_*-1)+2)
              + C D sum_(p in P\A) 1/log^2 p.              (2)

If all labels are in A, simply W(I)<=3Q.
The cut may be selected after inspecting the actual trajectory.
In particular (2) measures the tradeoff between a small-label
primorial barrier and the diversity of the larger labels.

Fix delta in (0,1) and set

    K_R=floor((1-delta) log_2 log R),  T=ceil(log R).

Any segment with at most K_R distinct labels has uniformly

    W(I) <<_delta D/log log R = o(D).                      (3)

Proof: scan labels in increasing order starting at Q_0=2.
Stop at the first label p_i>=T with p_i>T Q_(i-1), and take
Q=Q_(i-1), p_*=p_i. If no stop occurs, include all labels.
At each included label p_i<=T Q_(i-1), so Q_i<=T Q_(i-1)^2.
Consequently

    log Q_i <= 2^i log(2T)
       <= (log R)^(1-delta) log(2T) = o(log R).

Thus Q=R^o(1) uniformly. Without a stop, W<=3Q.
With a stop, the small-label charge in (2) is O(D/T+Q),
and the remaining label charge is O(D K_R/(log T)^2)
=O(D/log log R). This proves (3).

There is a robust variant: for fixed epsilon>0 suppose A is ANY
subset of the labels, |A|<=K_R, and every event with label not
in A has p>=R^epsilon. Then just the wait with labels in A
is O_(delta,epsilon)(D/log log R). To prove it scan A instead
of the whole support. The events outside A may interrupt small
runs, but there are at most D/(R^epsilon-1)+1 such events.
They add O(Q D/R^epsilon+Q)=o(D/log log R) to the charge.
The tail labels of A after the chosen gap still cost at most
C D K_R/(log T)^2. No restriction on waits of the outside
events is needed. In particular we can ignore arbitrary large
jumps while estimating the wait from a sparse set of small labels.

For any fixed epsilon>0, all waits with p>=R^epsilon in a
segment using k_high such distinct labels have the bound

    W_high(I) <<_epsilon D k_high/log^2 R.                (4)

Thus for each fixed eta>0, a block segment with W(I)>=eta D
must either use >K_R distinct labels below R^epsilon,
or use Omega_(eta,epsilon)(log^2 R) distinct labels
at or above R^epsilon. Indeed the robust variant eliminates
the low-label wait in the sparse case, and (4) bounds the rest.
The required support is not just a count of events.

## 3. All-history bound on low-diversity heavy-carrier traffic

Use the heavy incoming predecessor decomposition of the earlier
logarithmic merger note, including singleton seed injection and
fixed tie choice. Each occupied state belongs to a unique heavy
chain. At a light arrival an origin changes chains and its
group mass at least doubles. Hence each origin changes chain
at most log_2 M times, including a nonchosen singleton injection.
Partition [R,2R) into half-open blocks of width D, truncating
the final block. A chain-block piece is the consecutive list of
non-twin source states of one heavy chain in one block; twin
pre-offsets double and exit so cannot interrupt a piece.

Every origin encounters at most ceil(R/D)+1+log_2 M different
pieces: the block index is nondecreasing and a chain change
requires a light arrival. Every origin's wait within a given
piece is at most the full unweighted wait of that piece,
even if its mass is arbitrarily large and changes along the piece.
Apply (3) and sum over origins to conclude the unconditional
full-history estimate

    W_(pieces with <=K_R total distinct labels)
       << M(ceil(R/D)+1+log_2 M) D/log log R
       << R^2/log log R = o(R^2).                         (5)

There is no bound on carrier mass, phase width, or number
of events in this estimate. It includes the already-concentrated
old stable carriers. It is not just a fixed-generation statement.

For fixed epsilon in (0,1/2), the robust variant gives exactly
the same O(R^2/log log R) estimate for LOW-label actual waits
p<R^epsilon in pieces with at most K_R distinct such low labels,
regardless of the number of other labels. By (4), the HIGH-label
waits p>=R^epsilon in pieces with <=log^2 R/log log R distinct
high labels are likewise O(R^2/log log R).
The two estimates can be combined and also intersected with
any of the earlier stable/cohort/phase filters (nonnegative waits).
In particular if twins are finite, after all these charges the
remaining non-twin wait is still Omega(R^2). Each remaining
visit has either a low label in a piece of growing low-label
support >K_R, or a high label in a piece of high-label support
>log^2 R/log log R. At the level of a piece carrying >=eta D
unweighted wait, the stronger dichotomy in section 2 holds.
These new estimates control transport itself without needing
to estimate the past mergers that formed the carrier.

The gap lemma permits the sharper K_R=floor(log_2 log R
-(1/2+delta)log_2 log log R), with T=exp((log log R)^(1/2+delta/2))
and a separate gap multiplier log log R in place of T.
Then log Q=O(log R/(log log R)^(delta/2))=o(log R),
small-run charge O(D/log log R+Q), large-label charge
O(D/(log log R)^delta). The simpler K_R and T in (3)
are used in the audit and main statements.

## 4. Executed audit

Source research/min_simple_label_diversity_audit.py, commit
8a03223240174e259ae93cc0c7385ddb4758c4c2, Git blob
9ca52fa877c996a8002fdf4aaaffec32a05e23c5; remote readback
identical to the locally executed source (hash verified).
Stdlib and inherited min_simple_crossing_audit.py. Command:

    python research/min_simple_label_diversity_audit.py 1000 10000 100000 1000000

For each actual graph, checked ambient per-label capacity by exact
finite sum (not an effective numerical verification of the
asymptotic sieve constant), exact consecutive pieces, gap/no-gap
small-run charges, robust low-label charges with threshold
floor(R^(1/4)), and the all-origin piece budget. Independently
replayed all origins and matched weighted piece counts and wait
sums. All integer structural checks passed. Tested delta=1/2
(K=max(1,floor(log_2(log R)/2)); K=1 at these four scales).

    R        D      states  pieces  total wait   max support  max pieces/origin
    1000     178      240     65         2966        8         4
    10000    1000    2649    629       105828       13         6
    100000   5624   27708   6142      2595177       22         5
    1000000  31623 294268  61657     66822800       36         6

At R=10^6, M=83334, max light arrivals per origin 5.
7559 pieces have a support gap for T=14, 54098 have no such gap.
Wait split by total distinct support (cumulative):
    <=1: 1327947 (1.9873%); <=2: 2133975 (3.1935%);
    <=4: 4925988 (7.3717%); <=8: 12995816 (19.4482%);
    <=16: 36639109 (54.8303%); <=32: 65762503 (98.4133%).
With low threshold 31 the low/high wait totals were
12665813/54156987 and max high support was 27.
Low wait on pieces with <=1,2,4,8 distinct low labels:
140244, 348068, 1209480, 8154526 respectively.
Maximum actual single-label wait times log^2(p)/D over pieces
was 2.935829; maximum ambient capacity times log^2(p)/D
was 18.779054. These ratios are finite diagnostics, not
asymptotic estimates. No claim about a uniform constant based
on four samples. Earlier twin-free lower-bound case is not
exercised by these favorable finite graphs.

## 5. Remaining difficulty

We now remove sparse-support carriers, even with unbounded cohort
mass, over growing physical windows. But the bounds do not exclude
large cohorts with many distinct selected labels, including
many small distinct labels. Per-label supply alone cannot bound
the total across such support; counting all possible long words
loses clock selection and has the earlier combinatorial explosion.
To close, a new correlation bound for consecutive distinct
labels (or a different direct path obstruction) is needed,
not merely more fixed-order degree moments. No proof of the
remaining high-diversity stable transport, full-history energy
O(R^2), or twin infinitude has been obtained.
