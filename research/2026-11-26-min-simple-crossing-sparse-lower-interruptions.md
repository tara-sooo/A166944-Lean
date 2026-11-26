# First high-repeat prefixes with growing sparse lower interruptions

2026-11-26 JST. Continuation of 6e449f13cd380348df6cf681db2391693e7b3cf4.
New paper deductions and executed audit. The first repeat is now taken
only among high labels; lower labels may repeat and their number may grow
with prefix length. An additional physical-relay charge is independent
of the number of lower events. No full stable-wait bound, twin-infinitude
proof or Lean verification.

## 1. Statement and parameters

Same common-boundary reset system: seeds X in [R,3R/2], 6|X,
initial state (X,X/2+3), exit at first U>=2R, M=R/12+O(1).
Count only non-twin events; w<=2 min(p,q(u)), and total gain <3R.

For sufficiently large dyadic T define
    l=log T, m=log log T,
    A=T/l^2, U=T l^2, h=ceil(8l/m), W0=T/l^2,
    s0=floor(m/(64 log(2m))), s_max=s0+floor(h/4).
Take the largest prime cutoff z with
    Q=2 product_(odd primes <=z) p <= m.
For T sufficiently large this exists, with z->infinity.
Assume the product-room condition
    2 U^(h+s_max) <= sqrt R.                            (1)

An anchor is a non-twin event with p in [T,2T), w>=W0.
Consider the forward window of h events INCLUDING the anchor in
the sequence of all non-twin labels >=A, omitting all smaller labels
for the purpose of finding these h high events. Require the window
to exist and no high label in it to exceed U.

Within this window stop at the first repeated HIGH label, or at
the h-th high event if all h are distinct. Keep every event with
label >z between the anchor and this stopping event, inclusive.
The resulting prefix has n distinct high labels (n=h in the
all-distinct case) and s occurrences of lower labels z<p<A.
Require only
    s <= s0+floor(n/4).                                 (2)
A lower label may occur repeatedly. There is NO bound on waits or
phases of interior events. The events <=z are arbitrary preempted
low runs, each of physical gain an even integer in [0,Q] by the
primorial wall. No upper bound on their number is imposed beyond
the bound on their physical gain. In a repeated prefix the number
of events with p>z is n+s+1, but the number of distinct prime labels
is at most n+s. Only the latter enters (1).

Theorem. The sum of the actual waits of such anchors on ANY one
path in the slab is
    W_sparse(T) << R/l^(5/2).                           (3)
All constants are absolute for sufficiently large T. The bound
is independent of cohort mass, seed, phase or previous history.
For example the product room holds uniformly on eligible bands
T0(R)<=T<=exp((log R)^(1/3)), T0->infinity. This is not a
polynomial-scale theorem.

## 2. The two useful harmonic sums and source sieve

Let S_H=sum_(A<=p<=U) 1/p << m/l by the Chebyshev upper bound
on each dyadic prime band. Let S_L=sum_(z<p<A) 1/p << m by
summing the same elementary bound over all smaller dyadic bands.
Both sums are over primes.

Fix the high labels, the complete lower-label equality pattern and
its distinct prime values, orientations and all small relay gains.
For the full retained prefix the relative source offsets G_i are
now determined. Eligibility of the labels gives x_0=e_i-G_i mod p_i.
The distinct labels impose at most one residue class mod 2P on
the even initial source offset x_0, P their product. Repeated
low labels are consistency conditions rather than new moduli.
By (1), 2P<=sqrt R.

The anchor wait >=W0 makes both x_0+-1 rough up to W0/2.
On its progression use the explicit two-form Selberg upper sieve
from the inherited record-displacement-and-supply note, section 3,
cutoff floor(T^(1/40)). All high primes exceed the cutoff.
Omit any odd sieve primes dividing the distinct lower labels:
there are at most s of these. Dropping a prime with two
forbidden residues costs at most 3 in the Euler product
(ell>=3). The uniform truncated Euler product / mean log
index argument works with the retained primes; removing
factors only decreases the mean-log-index upper bound.
The remainder O(T^(3/20)) is absorbed since the progression
interval has length comparable to R/P>=sqrt R. Thus
    # sources per fixed compatible tuple << C^s R/(P l^2). (4)
There is only one anchor-roughness sieve, not a presumed
independent probability of all interior clocks firing.

## 3. First high return and a multiplicity-weighted prime pair

If a high label p first repeats after j retained steps,
with endpoint orientations e,e' and intervening retained
prime labels r_1,...,r_(j-1), the exact offset congruence is
    sum_(i=1)^(j-1) r_i = a p+j+e'-e-sum_(i=0)^(j-1) E_i.
Here each E_i is the physical gain of a <=z run, in [0,Q].
The case j=1 is impossible because 1+e'-e-E_0 is a
nonzero odd integer of magnitude <=Q+3<A. In the other
cases the expression for a p is positive: each interior
prime exceeds z>=3 and hence is >=5, so
sum r_i+sum E_i-j-e'+e >=5(j-1)-j-2>0 for j>=2.
Consequently 1<=a<=C(h+s_max)U/A.

If the return has an interior high label, choose one as q.
It occurs exactly once before the first repeated high label,
and is distinct from p. In this case b=1.

Otherwise all interior labels are lower; choose a largest one q.
There are at most s such occurrences, counted with repetitions.
Since sum r_i+sum E_i >= p+j+e'-e and sQ=o(A), necessarily
    q >= A/(2s).
Let b<=s be its multiplicity inside the return. In both
cases the endpoint relation is
    bq=ap+c,                                            (5)
where c=j+e'-e-sum E_i-sum_(r_i != q) r_i is fixed
after all other distinct prime values and the equality
pattern, orientations and relay gains are fixed. All
occurrences of q inside the return are included in b.
Even if q also occurs OUTSIDE the return, its reciprocal
factor in P is used just once. Since p>A/2>b and p,q
are distinct primes, c=0 is impossible by divisibility.
We have |c|<=C(h+s_max)(U+Q). A first high repeat with
n=1 would repeat the anchor p>=T with at most s0 lower
labels in between. Their gain, including the <=z relays,
is at most s0 A+(s0+1)Q+2<T for large T, contradicting
positive a p>=T. Therefore n>=2 in all repeated cases.
If the repeated high is not the anchor and q is high,
n>=3. If q is lower, n>=2 suffices.

### Uniform harmonic sieve for (5)

Fix b,c with 1<=b<=max(1,s_max), c!=0, |c| as above.
Sum over a<=C(h+s_max) U/A and distinct primes p in [A,U],
q in [A/(2 max(1,s_max)),U] satisfying (5). Then
    sum_a sum_(p,q) 1/(p q) << b m^4/(A l^2).             (6)
If p is the original anchor, replace A in the denominator
by T. This second bound will be important for n=2.

To prove (6), divide p,q into dyadic intervals [v,2v),
[t,2t) respectively. The allowed p interval has length
<=min(v,bt/a). Enlarge to comparable length when it is
shorter. Even the minimum v or bt/a is >=T/polylog T
uniformly: s_max=O(l), h=O(l), U/A=l^4, and the minimum
q band is >=A/(4 max(1,s_max)). For any actual solution
the two integers p,ap+c are respectively a prime and b
times a prime, both larger than the sieve cutoff. For
odd sieve primes not dividing abc, the two forms have
distinct roots. The same explicit two-form upper sieve
omits primes dividing abc (and 2). As |abc|<=T^C for a
fixed C, their Euler-product loss is O(m^2), by the
bounded-prime-divisor product estimate of the preceding
first-repeat-prefix note. Its O(T^(3/20)) error is absorbed
by the interval length. The count is
    << min(v,bt/a) m^2/l^2.
Dividing by vt bounds its harmonic weight by
    << b m^2/(a v l^2).
We may overcount solutions by not imposing the extra
congruence b|ap+c during this sieve. This does not
invalidate an upper bound. Sum over a (harmonic loss
O(m)), over t (O(m) bins), and over v (geometric
sum O(1/A), or O(1/T) when p is the anchor).
This proves (6). No lower sieve or independence
assumption is used.

## 4. Growing interruption allowance: counting the prefixes

For fixed n,s the number of ways to interleave lower
occurrences among the high prefix is <=2^(n+s+1).
The lower equality partitions have at most max(1,s)^s
possibilities: assign each occurrence to a class indexed
by a first occurrence. The orientations and small-relay
gains cost at most C^(n+s+1)(Q+1)^(n+s). The source sieve
has the factor C^s from (4). For free distinct lower
labels their harmonic sum is at most (C m)^s, even when
some labels have been repeated. In the case of a determined
low q we remove its harmonic sum and use (6) instead;
bounding the remaining low-label harmonic factors by
(C m)^s only overcounts. The choice of q among low
classes and its multiplicity loss b in (6) cost at most
(s+1)^2. We may also overcount the high-repeat position
and choice of high interior q by n^2.

Put D0=C(Q+1)<=C' m and absorb all lower enumeration,
including the factor b, into
    F_n=sum_(0<=s<=s0+floor(n/4))
              (C m^2(s+1))^s (s+1)^3.
Constants C here can be enlarged finitely to cover all
of the preceding choices, independent of n,s,T.
For large T,
    F_n <= l^(1/4)               if n<8s0,
    F_n <= l^(n/2)               if n>=8s0.              (7)
Indeed in the first case s<=3s0, and log(C m^2(s+1))
<=3 log m+O(1), so log F_n <=9s0 log m+o(m)
< m/4 by the choice of s0. In the second case
s<=3n/8, s<=s_max<=l eventually, so the base has
log <=(1+o(1))m; the polynomial factors and number
of summands contribute O(m)=o(nm) uniformly since
n>=8s0->infinity. This gives the second inequality.
We intentionally use generous exponents.

If all h high labels are distinct, (4) and the harmonic
sums give a source count bounded by
    R/l^2 * F_h (D0 S_H)^h
    << R/l^2 * (C m^2/l^(1/2))^h.
Its first-anchor wait (<=4T) is O(R/T^2) for large T,
because h=ceil(8l/m) and the last power is T^(-4+o(1)).

For repeated high prefixes combine (4), (6), the high
harmonic sum for all remaining free high labels, and
the above enumerations. The two sieves are nested
upper counts: after the other prime values and c are
fixed, sum the compatible pair; for each resulting
tuple apply the source progression count. No independence
of the sieves is asserted. After weighting the anchor
wait by 4T, the three relevant classes at fixed n are
bounded as follows (an extra C^n may be absorbed in D0):
    q high, repeated p anchor, n>=2:
      << R F_n n^2 D0^n m^4/l^4 * S_H^(n-2);
    q high, repeated p not anchor, n>=3:
      << R(T/A) F_n n^2 D0^n m^4/l^4 * S_H^(n-2);
    q lower, n>=2:
      << R(T/A) F_n n^2 D0^n m^4/l^4 * S_H^(n-1).
The last bound is valid even without using an anchor
improvement for the lower pair. In fact a low-only
return to the anchor would require n=1 and is impossible
under (2). The source counts refer to the original
anchor, so no factor h for overlapping return windows
is required. A path visits each anchor offset at most
once.

Sum over n<8s0 using F_n<=l^(1/4) and
D0 S_H<<m^2/l->0. The leading terms of the three
geometric tails (at n=2,3,2 respectively) give
    << R l^(1/4) m^6/l^4
       + R(T/A) l^(1/4) m^8/l^5
       + R(T/A) l^(1/4) m^7/l^5
    = O(R/l^(5/2)),
since T/A=l^2 and any fixed power of m is o(l^(1/4)).
For n>=8s0, use the weakest of the bounds, the second
with two free factors removed and T/A=l^2. With (7),
the resulting sum is
    << R m^2 sum_(n>=8s0) n^2 (C m^2/l^(1/2))^n
    = o(R/l^10).
The bound is uniform in h and in the number of
distinct lower labels. This proves (3).

## 5. Global wait charges including long physical relays

Summing (3) over eligible dyadic bands T>=T0(R)->infinity
gives O(R/(log T0)^(3/2)) per origin, hence
    W_sparse,all = O(R^2/(log T0)^(3/2))=o(R^2).         (8)
The upper-interruption charging lemma from the mixed-window
note now applies to the sequence of labels >=A (instead of
>z): for a fixed occurrence p'>U(T), at most h-1 earlier
anchors at band T can have that occurrence in their forward
h-window. The geometric band sum gives total upper charge
O(R/(log T0 log log T0)) per origin. Similarly missing
h-windows cost O(R^(1/4) log R) per origin by product room,
and short own anchor waits cost O(R/log^2 T0).

There is a further independent charge on physical relays.
For a full h-high-event window, let G_low be the total
physical gain of ALL intervening events with label <A,
including those <=z, from the anchor to the h-th high
source. At fixed band T each occurrence of a low event
lies in at most h-1 such windows with high anchors:
only the h-1 immediately preceding high occurrences
could start a window covering it. Thus sum G_low over
all anchors with full windows at that band is <=3Rh.
The total wait of anchors with G_low>=T l^3 is therefore
    <=4T * 3Rh/(T l^3) = O(R h/l^3).
Summing the decaying O(l^(-2)) bound over all dyadic
bands gives O(R/log T0) per origin, or
    W_long-relay,all=O(R^2/log T0)=o(R^2).              (9)
This charge uses gain even if the number of lower labels
is enormous. The same gain may be counted at different
bands; the summable factor h/l^3 explicitly pays for
that overlap. No uniform upper bound on a single
low-run length is assumed. The threshold is on total
intervening gain, not on the number of low events.
Equation (9) is a paper deduction, not a separately
instrumented numerical count in the audit below.

After (8), (9), and the upper/terminal/short-own charges,
at eligible scales the residual anchor has a full
h-high-event window, no high label >U, and G_low<T l^3,
but before its first high repeat or h-th distinct high
event has MORE than s0+floor(n/4) occurrences with
z<p<A. There is no bound yet on the wait of this
frequent-small-interruption population. Product room
still excludes polynomial-scale labels, and low labels
below T0 are not controlled. The theorem does not
establish W=o(R^2) or E=O(R^2).

## 6. Executed finite audit

Source research/min_simple_sparse_interruptions_audit.py,
source commit 55c9638a7bb1493f0768c39b4c52e2c269e331a6,
Git blob a355de8dcf7b9addd0b6f10474e7f6a3d29e2328.
Exact remote readback matches executed local git hash.
Self-contained stdlib, including independent factor sieve.
Run:
    python research/min_simple_sparse_interruptions_audit.py 1000 10000 100000 1000000

Fixed diagnostic z=3,h=4,A=T/4,U=8T,W0=max(7,T//8),
A>Q+3, prefix cap 2+floor(n/4). These are NOT the
asymptotic parameters (in particular s0 is not yet large).
Literal GCD ticks independently checked for every occupied
non-twin state at R=1000,10000. Replayed all origins at
the four scales; checked prefix equality patterns and
source CRT including repeated low labels, primitive relay
gain bound, (5), positivity, first high repeat, lower
maximum condition where the diagnostic room holds,
dyadic interval constraint for bq=ap+c, and the per-tuple
source count. All checks passed.

At R=10^6: 83334 seeds, 294268 cached states including
twin terminals, 2564511 non-twin visits, W=66822800.
Same eligible anchor population as previous first-repeat
audit: 233398 anchors, W_anchor=49479900. The diagnostic
window now uses h HIGH labels, not h labels >z.

    class                        anchor wait
    own short                         337601
    missing high window             30680377
    upper interruption               1788645
    too many lower in prefix        13780101
    admissible prefix                2893176

There are 24039 admissible prefixes (23003 all-distinct
high, 1036 first high repeat). Distribution of explicit
lower occurrences:
    0: 2465, wait 219980
    1: 5429, wait 642274
    2: 7535, wait 896876
    3: 8610, wait 1134046
5548 prefixes have repeated low labels. A comparison
requiring at most two lower occurrences in the entire
h-high window admits 15394 windows (wait 1754684).
The zero-lower population exactly reproduces 2465
windows of the preceding fixed diagnostic. At R=10000,
24 admissible prefixes; R=100000, 1156. There are
1409 distinct tuples at R=10^6. Return cases:
291 high pair with p the anchor, 589 high pair with
p not the anchor, 156 low pair with p not the anchor.
No low-pair multiplicity b>1 is exercised in these
accepted finite prefixes, although repeated lower
labels themselves are exercised. Example seed 1061460,
retained labels (109,37,5,17,11,17), relay gains
(0,0,0,4,2), gives lower pair p=17,q=11,a=b=1,c=-6.
This checks the low-only return relation. The asymptotic
growth of the interruption cap and the analytic sieve
estimates are not verified by these finite diagnostics.

Next: frequent lower interruptions with limited physical
gain. The remaining population need not be rare merely
because the interruption count increases. The new prefix
count does not bound it. A mechanism for eliminating
or contracting those lower-word histories, or a different
global bound on actual waits, is still required.
