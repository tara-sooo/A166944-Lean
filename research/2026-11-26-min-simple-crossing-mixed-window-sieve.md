# Mixed-scale windows, six-form source sieve, and upper-interruption removal

2026-11-26 JST. Continuation of 3496ff033af3401ff21c6d62e5ab96eaa037aa1a.
New paper deductions and executed finite audit. The goal is to count
different-size labels in a single compressed word and eliminate very
large intervening events without charging the same gain at every scale.
No full stable-wait upper bound, twin-infinitude proof or Lean verification.

## 1. Parameters and exact compressed windows

Use the common-boundary MIN from X in [R,3R/2], 6|X,
(X,X/2+3), stop on U>=2R. M=R/12+O(1). Exclude the twin
event itself from all wait sums. Each non-twin event has
w<=2 min(p,q(u)); total physical gain per origin <3R.

Let T be dyadic and sufficiently large. Write

    l=log T, m=log log T,
    A=T/l, U=T l^2, K=U/A=l^3,
    h=ceil(8 l/m), W0=T/l^2.

Choose a cutoff z>=3 with Q=2 product_(3<=ell<=z, ell prime) ell
<=l^(1/4), L=2Q; for example the largest such prime cutoff.
Thus z tends to infinity as T does, and W0>2z eventually.
Use the product-room condition

    L U^h <= sqrt R.                                      (1)

For example all T0(R)<=T<=exp((log R)^(1/3)) satisfy (1)
eventually if T0->infinity. No polynomial-scale claim is made.

An anchor is an actual non-twin event with p in [T,2T).
Form its forward h-window in the sequence of ALL non-twin
events with labels >z(T), including the anchor. Call it good
if it exists and each of its h labels belongs to [A,U]
and each wait is >=W0. No restriction on exact deficit or
on which of the J=Q even residues modulo L occurs.
All intervening <=z relays are determined by the preceding
arrival offset and deficit residues modulo L, by the exact
relay compression theorem of the preceding paper: every
next wait is >2z. Each relay gain is <=Q.

For a fixed initial source residue rho mod L, labels,
orientations and arrival deficit residues, all relative
source offsets are fixed. If P is the product of distinct
labels, the initial source belongs to at most one residue
class modulo LP, since every p_i>=A>z. Inconsistent tuples
are discarded. All sources are in the actual slab and each
source can occur at most once on a monotone path.
This counts source offsets on one path, not the number of
reachable states or mass of their basins.

## 2. Six-form sieve on the source progression

The first three source offsets of any good window or of
any minimal-return subword of length >=3 have six distinct
integer neighbor shifts c_1,...,c_6 relative to its first
source. They are distinct since consecutive high offsets
differ by at least A-1>2. Their pairwise differences are
O(U+Q), as only two compressed high steps are involved.
All six neighbors avoid every odd prime <W0/2, by the
competing clock bound. On a fixed progression x=x0+LP n,
discard sieve primes dividing L and

    Delta=product_(i<j) |c_i-c_j|,  0<Delta<< (U+Q)^15.

The other odd primes below T^(1/40) do not divide P, and
for ell>7 the six forms exclude exactly six distinct
residues of n. The interval length N=O(R/(LP)) may be
enlarged to comparable length R/(LP)>=sqrt R by (1).
The explicit one-dimensional Selberg upper sieve from
the inherited record-displacement-and-supply note applies
to g(ell)=6/ell on these primes: squarefree residue counts
have error O(rho(d)) with rho(d)<=d; the diagonalized
weights have |lambda_d|<=d since ell>=11. With sieve
index cutoff floor(T^(1/40)) the remainder is
O(T^(3/20)), absorbed by the main term uniformly.
For the denominator G, truncate the Euler product at
a fixed sufficiently small power of the sieve cutoff
and use the same mean-log-index Markov argument as in
the preceding five/seven-condition sieves; g<=6/ell.
The complete product has order (log T)^6, and removing
primes dividing L Delta loses at most O(m^6). Indeed
L Delta<=T^C with fixed C, and for any nonzero integer
|n|<=T^C, prod_(ell|n)(1-1/ell)^(-1)<<log log T:
split at log T, apply Mertens below, and the elementary
number-of-large-prime-factors bound above. For the
six-root local factors the convergent O(ell^-2)
correction is harmless. This proves the uniform count

    # sources per fixed tuple << R/(LP) * m^6/l^6.        (2)

One can also sieve just the first two neighboring forms,
giving the earlier O(R/(LP)*m^2/l^2) bound.
The constants of (2) do not grow with h: only six forms
are used and their shifts lie in a polynomial-size range
in T, not an h-dimensional sieve. This is a necessary
arithmetic constraint on actual good words, not a claim
that every surviving source realizes the clock word.

## 3. Distinct and repeated mixed words

The prime harmonic sum over the wider interval is

    S=sum_(A<=p<=U) 1/p << log(2K)/log A << m/l,

by Chebyshev on dyadic intervals. For all h distinct labels
sum the two-form version of (2) over rho (<=L choices),
orientations, J arrival residues per event, and ordered
prime tuples. The factor L cancels. The number of possible
sources is

    << R m^2/l^2 * (C J m/l)^h.

Since J=Q<=l^(1/4), this power is T^(-6+o(1)).
Multiplying by the anchor wait <=4T gives O(R/T^2)
for sufficiently large T. It is important to use the
reciprocal-prime sum, not count all labels as if they
were at the bottom of the range.

For repeated words take a shortest repeated subword
p0,p1,...,p_(j-1),p0, with the first j labels distinct.
Consecutive equal labels are impossible because their
endpoint congruence would require p0 to divide the
nonzero odd integer 1+e1-e0-E0 of magnitude <=Q+3<A.
Thus 2<=j<h. The previous exact return relation gives

    p_(j-1)=a p0+c,
    c=j+e_j-e_0-sum_(i<j) E_i-sum_(1<=i<j-1) p_i,

where 1<=a<=C j K and c!=0 (otherwise the two distinct
primes would be multiples of one another). Positivity
follows from the sum of the j-1 positive interior primes
and the nonnegative relays minus j+e_j-e_0. Also
|c|=O(jU). Fix rho, orientations, arrival phase classes,
the residue of p0 mod L, a, and the j-2 other interior
primes. All relays except the final one are now fixed.
Enumerate only that last E_(j-1) in [0,Q], as in the
preceding compressed-word proof, making c fixed.
The enumeration overcounts and does not assume that
the guessed last relay is compatible with the resulting
prime pair.

We need the harmonic weighted version of the two-prime
sieve. Split p0 into O(log(2K)) dyadic subintervals of
length comparable to t, t>=A/2, t<=U. On the progression
p0=b+Ln sieve p0 and a p0+c simultaneously, omitting primes
<=7 and dividing Lac. The two roots are distinct on the
remaining sieve primes, below T^(1/40). Here |Lac|<=T^C
uniformly (j<=h, a<=C j K), so the same omitted-prime
argument gives a loss O(m^2), and the parameter length
t/L absorbs the O(T^(3/20)) remainder. The pair count is
O(t m^2/(L l^2)) for each subinterval; impose the additional
restriction p_(j-1)>=A before taking reciprocals. Hence

    sum_(consistent pairs p0,p_(j-1)) 1/(p0 p_(j-1))
        << m^3/(L A l^2).                               (3)

This estimate does not replace the possibly smaller
p_(j-1) by p0. It is uniform across the mixed band.

Multiply (2) by this weighted pair bound, the harmonic
sums of the j-2 other interior primes, the L^2 choices
of rho and p0 residue, O(jK) choices of a, and the
orientation/phase/last-relay counts. The two L factors
cancel. The number N_j of possible shortest-return
occurrences on a single path satisfies

    N_j << (R/A) j K C^j J^(j+1) (Q+1)
                  m^(j+7) / l^(j+6).                    (4)

The source sieve uses the first three sources of the
return, including the repeated terminal source if j=2;
all have the stipulated long wait, so all six forms
are available. Its progression modulus is LP for the
j distinct labels, not the product of all h occurrences.
It fits (1). The prime-pair and source sieves are nested
counts on fixed tuples, not independent probability factors.

Since C J m/l -> 0, the sum of (4) is bounded by its
geometric tail starting at j=2:

    sum_(2<=j<h) N_j << (R/A) K J^3 (Q+1) m^9/l^8.

Each particular return occurrence belongs to at most h
forward h-windows of the compressed sequence. Every
anchor wait <=4T, hence repeated-window anchor wait
is at most

    << R (T/A) K J^3 (Q+1) m^8/l^7
    << R m^8/l^2,                                      (5)

using T/A=l, K=l^3, J^3(Q+1)<=2l.
Together with the distinct case this proves

    W_good(T) << R (log log T)^8/log^2 T.

In particular W_good(T)<<R/log^(3/2) T eventually.
The anchor weighting matters: replacing it by 2U would
lose a factor l^2 and destroy this particular summation.
No restriction on cohort mass, label support, absolute
deficit, or previous history is imposed.

## 4. Geometric removal of upper interruptions at ALL scales

We next charge anchors whose h-window exists but contains
a label p'>U(T)=T log^2 T. This class may also contain
other obstructions; select one such upper interruption
and charge the anchor to it. For fixed T and one occurrence
of p' along the actual path, at most h-1 earlier anchors
in the >z(T) sequence can charge it. Hence the charged
wait is <=4T h(T). This holds even though the cutoff z
changes with T. Sum over eligible dyadic T>=T0 for that
same p'. If nonempty, let T* be the largest charging band.
For large T, h(T) is nondecreasing and h(T)/log^2 T
<<1/(log T log log T). Therefore

    sum_(T charging p') 4T h(T)
        <=8 T* h(T*)
        << p'/(log T0 log log T0).

We used the geometric sum of the dyadic T, NOT the number
of scales times a separate gain budget. As sum p' over
a path is <=1.5 sum(p'-1)<4.5R, this yields

    sum_T W_upper(T) << R/(log T0 log log T0).           (6)

The same reasoning works for backward windows (with the
opposite charging direction) or a union of the two
obstruction classes with at most twice the cost.
This is an actual all-scale bound on upper interruptions,
independent of the number of low interruptions, phase
conditions and prior mergers. It does not count the waits
of the interrupting events themselves as part of the
anchor charge, except if they are also anchors in their
own scale.

Anchors with no h-window cost <=4Th(T) per band, since
only the last h-1 events of the corresponding compressed
sequence can qualify. Under (1), for large T one has
T<=R^(1/4) and h<=log R, so summing dyadically gives
O(R^(1/4) log R)=o(R) per origin. Anchors with own wait
<W0=T/log^2 T cost O(R/log^2 T0) by the gain budget.
Summing (5), (6) and the two other charges over all eligible
bands T>=T0 and M origins, one obtains

    W_removed << R^2/sqrt(log T0)=o(R^2).                (7)

All bounds in (7) apply to arbitrary existing stable
carriers, since they hold per origin. There is no need
to suppose an upper bound on the number of carriers or
their masses. The dyadic good-window sums use disjoint
anchor bands; the upper-obstruction sums pay each
interrupting gain geometrically even if it appears in
many compressed sequences.

## 5. Exact residual, and what this does not resolve

For anchors in eligible scales, classify in order:
own wait below W0; missing h-window; upper obstruction;
lower obstruction; short internal wait; otherwise good.
The first, second, third and sixth classes are controlled
by (7). Each residual anchor has a full forward window,
no p'>T log^2 T, and contains either
  - a label z(T)<p'<T/log T, or
  - an interior wait <T/log^2 T with its label in [A,U].
There are no phase restrictions in this theorem.
The small wait of the second kind of obstruction itself
can be cheap, while it may block many large anchors.
A small lower label cannot pay the 4Th anchor charge
via its gain. Hence the geometric upper-interruption
argument does not carry over in reverse. Polynomial-scale
labels outside (1), and low labels below T0, are also
not covered. Even if a path has arbitrarily many lower
interruptions, it need not be covered by the good-window
sieve. No W=o(R^2) or E=O(R^2) bound follows.

## 6. Executed finite audit

Source research/min_simple_mixed_window_audit.py, source
commit 7eed72ad97e8eca1a3327ec9d5a71abfd3170dc3, Git blob
a8788e479f271107225a16df00b12d3e1e25cd87. Exact remote
readback matches the locally executed source hash.
Python stdlib plus inherited min_simple_crossing_audit.py.
Run:

    python research/min_simple_mixed_window_audit.py 1000 10000 100000 1000000

Complete arbitrary-phase restricted relay tables at z=3
and 5 (36 and 900 residue pairs, respectively), checked
independently by literal GCD ticks at translated offsets.
Max gains 4 and 14. The slab audit uses FIXED diagnostic
parameters z=3,h=4, A=T/2,U=8T, W0=max(7,T//8), T dyadic,
A>Q+3. These are not the asymptotic parameters, which
are outside the finite range. Checked complete origin
replay, exact phase-relay reconstruction (gain and time),
source CRT, minimal return linear relation, distinct
six neighbor shifts and their good-prime residue roots,
per-band upper obstruction multiplicity, geometric
cross-band charge and terminal charge. At R=1e6:
M=83334, 294268 cached states, 2564511 non-twin visits,
total wait 66822800, eligible diagnostic anchors 357139,
anchor wait 53432663.

    class                 anchor wait
    short own wait             419208
    missing window            7360227
    upper interruption        1180976
    lower interruption       44290350
    short interior wait         61667
    good window                120235

There were 1617 good windows (all mixed dyadic labels),
1412 with nonzero compressed relay, 1605 distinct and
12 repeated. These counts are origin-weighted and can
share states. At R=100000, 16 good windows, all mixed,
all distinct. The positive upper-interruption class
was exercised at R=100000 and 1000000. All integer
checks passed. The dominant lower-interruption share
in this diagnostic is about 83% of anchor wait; this
is evidence about the tested classification, NOT a
proof of an asymptotic lower bound or a failure of
the new upper-bound theorem. The audit tests identities
and charging, not the growing-depth sieve constant.
No Lean verification.

Next: handle lower interruptions and short-wait events
inside the high sequence without paying the full anchor
weight per obstruction. In particular the observed
dominance of lower interruptions makes further refinements
of just the good-word count insufficient as a strategy
for closing the full residual. No claim of twin infinitude.
