# Phase-sensitive high-arrival ambiguity after compressed relays

2026-11-26 JST. Continuation of b88435224aa0f49730aa9aa507a0d6d200d794bf.
Focus on the merger/medium-dense obstruction: retain the actual arrival
phase in compressed reverse ancestry, and count branching BETWEEN distinct
large incoming labels. Paper deductions, inherited elementary upper sieve,
and executed finite audit. No Lean kernel verification, novelty claim,
or twin-infinitude proof.

## 1. Exact arrival phase, not just offset factorization

An ordinary MIN main event with label p has pre-offset x,
arrival offset u=x+p-1, arrival firing time v, and orientation
e=+1 (minus/even) or -1 (plus/odd). Put s=0 or 6 respectively.
Then

    e=+1: u=0 mod 2p, v=0 mod 2p;
    e=-1: u=-2 mod 2p, v=p+2 mod 2p;
    d_a=2v-u=2ap+s, a a nonnegative integer for p>=5.

Indeed the two clock congruences and even offset imply all of
these, including the stronger arrival phase modulo 2p.
The exact pre-offset is x=u-p+1. There can still be several
possible pre-event TIMES leading to the same arrival, so
this does not give an injective full event map.

Compress a consecutive relay of labels in A={3,5,7,11}
after this event (empty relay allowed). From the previous
signed-potential note, any endpoint (U,V) has

    0<=U-u<=104, 0<=V-v<=133,
    -16 <= d-d_a <= 192, d=2V-U.                    (1)

In defining reverse candidates, permit ANY state (u,v)
satisfying the high arrival congruences, envelope, and
a>=0, whether or not an earlier legal source event actually
exists. Then allow any prefix of the exact restricted
A-only trajectory from that state. All actual compressed
arrivals are included: a larger event could preempt a future
A-clock, but cannot change a previously selected A-event.
This is a relaxed incoming graph, not a claim of actual
canonical-root ancestry.

**Uniqueness for a fixed label.** For p>=113, at most one
candidate high arrival state (u,v), including orientation,
can lead to any prescribed compressed endpoint (U,V).
For fixed orientation the width 104 is less than 2p, so
the arrival offset is unique. The interval of possible d_a
has length 208<2p, so the multiplier a is unique too.
If both orientations existed, their offsets must satisfy
u_plus=u_minus-2 (the interval width is <2p-2).
The two possible deficits differ by 2p(a_plus-a_minus)+6
and lie in the same interval of width 208. Since
2p-6>208, a_plus=a_minus. Then v_plus-v_minus=2,
contrary to v_minus=0 mod 2p and v_plus=p+2 mod 2p.
This proves uniqueness across signs as well.
It is essential to use the actual firing phase; offset
and deficit congruences modulo p alone do not suffice.

## 2. Distinct-label ambiguity forces a small linear prime equation

Fix an integer K>=1, T>=113, and R>=T^2. Consider endpoints
with U in [R,3R), d>198, d<=2KT, and candidate large labels
p>=T. By (1), d_a>=d-192>6, so all their multipliers are
positive; d_a<=d+16 implies a<=K (integer, T>8).
Thus all candidate labels lie in [T,(K+1)T].
If two distinct labels p,r can lead to the same endpoint,
their multipliers a,b in [1,K] satisfy

    2ap+s_p + delta_p = 2br+s_r + delta_r,
    ap-br=c, |c|<=107.                              (2)

Here both relay changes delta are in [-16,192], and
s_p,s_r in {0,6}. If p,r>K, c cannot be zero:
otherwise p|b and r|a. Hence for T>K the equation is
nondegenerate. It is not assumed that a=b, nor that
the two labels are twin primes.

A pointwise improvement applies in a narrow band:
if both labels lie in [T,(1+eta)T], eta<=1/(2K),
T>214, and a!=b, then |ap-br|>=T-K eta T>=T/2>107.
Therefore every candidate in this band has the SAME
multiplier. If that multiplier is >=54, then two
distinct odd primes would give |ap-br|>=108, again
impossible. Combined with section 1, there is at most
one entire candidate arrival state within this band
when any candidate has multiplier >=54.
This is a genuine high-stratum inverse uniqueness
statement even in the presence of low relays.

## 3. Count all ambiguous compressed states

First keep K fixed and T->infinity, T<=sqrt R.
For fixed a,b<=K and nonzero c with |c|<=107, the number
of prime pairs p,r in [T,(K+1)T] solving ap-br=c is
O_K(T/log^2 T). To see this, let g=gcd(a,b). If g does
not divide c there are no solutions. Otherwise all
integer solutions are parametrized as
p=p0+(b/g)n, r=r0+(a/g)n, with n in an interval of
length O_K(T). For primes ell not dividing abc, the
two forms have distinct roots mod ell: the determinant
is a nonzero signed c/g. Sieve out their zero residues
for odd ell<=T^(1/20), omitting the finitely many
exceptional primes. All actual p,r>T^(1/20) survive.
The inherited elementary two-root Selberg upper sieve
(uniform in translated intervals) gives the stated
bound, with error O(T^(3/10)), absorbed by the main term.
One can pad a shorter parameter interval to length
ceil((K+1)T)+O(1) before applying that estimate.

For each such pair, a,b and orientations, choose the
two relay gains E_p,E_r in [0,104]. The arrival
congruences force

    U=E_p+s_e mod p, U=E_r+s_f mod r,

where s_e is 0 for minus, -2 for plus.
CRT fixes one class modulo pr. The count in [R,3R)
is O(1+R/T^2)=O(R/T^2). For each U, its d lies in a
fixed interval of width 208 by (1), hence there are
O(1) endpoint times V. Summing all choices proves

    # ambiguous compressed states
          <<_K R/(T log^2 T).                       (3)

Here ambiguous means at least two DISTINCT high label
candidates in the relaxed graph, so all actual distinct-
label compressed mergers in this regime are included.
The estimate counts states over the union of all phases,
not trajectories, origins, or only upward-event endpoints.
It needs no roughness of the source neighbors, first-clock
selection of the high incoming events, or finite-twin
hypothesis. Core arrivals are excluded by d>198, which
is necessary: at a=0 the label is no longer tied to
positive deficit.

## 4. Growing low alphabet and growing multiplier budget

For all odd primes <=y use the general primorial wall
Q=2 product_(3<=p<=y) p, so gain<=Q, wait<=3*gain,
and net relay deficit change lies in [-Q,5Q].
Take T>4Q+10, K<T, d>6+5Q and d<=2KT.
The arguments of sections 1--2 still apply:
arrival offsets lie in an interval of width Q,
arrival deficits in an interval of width 6Q,
the two opposite-sign offsets differ by -2,
and 2p-6>6Q. Consequently each fixed label has at
most one candidate arrival state. Distinct labels
satisfy ap-br=c!=0 with a,b<=K, |c|<=3Q+3 and
T<=p,r<=(K+1)T.

Uniformly for K,Q=T^o(1), the two-form sieve in
section 3 now gives for each a,b,c
O((K+1)T (loglog T)^2/log^2 T) pairs.
For completeness the omitted-prime correction is
at most prod_(ell|abc)(1-1/ell)^(-2), up to an absolute
constant from the two-root local factors.
Since |abc|<=K^2(3Q+3)<=T^O(1), split at log T:
Mertens bounds the smaller-prime product by
O((loglog T)^2), and the sum of reciprocals of the
remaining prime divisors is O(1/loglog T).
The usual truncated Euler-product lower bound for
the Selberg denominator uses only an upper bound
2/ell on the retained local density and thus is
uniform after these exceptional omissions.
The error O(T^(3/10)) is uniform and absorbed.
This uses the same explicit weights and Mertens/
Chebyshev truncation as the inherited local
label-diversity upper sieve, not a lower-bound
prime-pair estimate.

There are K^2 choices of multipliers, O(Q+1) choices
of c, O((Q+1)^2) choices of gains, and O(Q+1) choices
of deficit per offset. The two side choices for each
label cost only an absolute constant. CRT still
gives O(R/T^2) offsets per tuple. Therefore

    # ambiguous states
       << K^2(K+1)(Q+1)^4 R (loglog T)^2
                                  /(T log^2 T).      (4)

In particular for K,Q=T^o(1) the bound is R/T^(1-o(1)).
This accommodates a growing small-label alphabet
as well as multiplier budgets growing with the
local crossing width. It is an upper count for
the relaxed graph, not a claim that all possible
arrivals occur in actual MIN.

## 5. Much longer prefix control for distinct-label mergers

Let T=T(R), R^epsilon<=T<=sqrt R for fixed epsilon>0.
Use y=floor((loglog R)^(1/4)), Q as in section 4,
K=(loglog R)^A rounded up, any fixed A>0.
Then Q=exp(O((loglog R)^(1/4))) by Chebyshev,
so K,Q=T^o(1) and all conditions on T hold eventually.

Let 0<delta<1 and set
k=floor((1-delta)*log T/loglog R).
Consider ANY actual prefix from even X in [R,2R),
with all offsets in [R,3R), having at most k events
of label >y (and any number of low events).
The compressed offset-only reverse estimate from
10382d8, with the uniform degree bound C log R,
bounds the number of possible origins per endpoint by

    A_k=(k+1)(Q+1)^(k+1) (C log R)^k
        <= T^(1-delta/2)

for sufficiently large R. Indeed
log A_k <= k(loglog R+O(log(Q+1)+1))+O(log k),
and log Q=o(loglog R). This does not require
good inverse degrees or a small starting deficit.

Multiply this by the bound (4), even if the same
offset carries multiple ambiguous states. It follows
that the number of origin offsets from which ANY
such prefix can visit an ambiguous high-deficit
compressed state is

    <= R/T^(delta/2-o(1))=o(R).                      (5)

This controls all phases, every permitted history,
and all its visits within the non-low budget.
On density-one canonical resets, distinct-large-label
compressed ambiguity therefore cannot arise in this
much longer initial segment, provided the endpoint
is in the indicated deficit corridor and both
candidate labels are >=T. The admissible budget
k is of order log R/loglog R, rather than the
sqrt(loglog R) budget in the earlier first-
significant scarcity theorem. It is a stronger
budget for this PARTICULAR type of ambiguity only;
it does not extend the earlier scarcity bound
on all large waits to the same budget.

For a near-square-root crossing of width
D=O(T(loglog R)^A), canonical d0=6 and w<=3g give
d<=6+5D at every pre-offset within the window.
Thus a suitably enlarged K of the same polyloglog
order covers all high deficits in the crossing;
no separate bound on multiplier growth is needed.
An exiting overshoot outside the endpoint corridor
is not included. In the cutoff y, Q grows much more
slowly than T, so the low-deficit region excluded
by d<=6+5Q is small in height, but its traffic
is not controlled by (5).

The remaining obstruction is precise: even at an
unambiguous endpoint, a unique last high arrival
does not determine its preceding source TIME,
and different paths can reach that same source
offset with different phases, or merge through
intermediate labels. Also the path may contain
more than k non-low events. Therefore (5) is not
a bound on full basin size or all medium-dense
waits. To extend the useful inverse uniqueness
to full ancestry, one must control the phase
fibers of each incoming high event, or establish
a suitable amortized bound on the medium-label
segments that connect them. No product of
independent phase probabilities is justified.

## 6. Executed finite audit and persistence

Source research/min_local_high_arrival_collision_audit.mjs,
final commit 83a14614e69a933a7c5b16fb5e624da30db2b8a0,
blob f40e12f556f1a8e5e685f6c0d46d70eda2d813cd.
Run: node research/min_local_high_arrival_collision_audit.mjs 1000000.
Executed as ECMAScript in the research runtime, fetched at the
exact commit and re-executed with identical results.
No Node process or Lean process invoked.

Seven finite controls, high arrivals in [R,2R), p in [T,2T],
1<=a<=K, with exact arrival parity/congruences and envelope.
Enumerate every prefix of its restricted <=11 relay, retaining
endpoints d>198,d<=2KT. This is the relaxed graph; no claim
all initial arrivals have ordinary reset-origin ancestry.
The finite audit uses the narrower label band [T,2T] rather
than all labels >=T in the general estimate (4).

    R        T    K   distinct endpoints   ambiguous endpoints
    100000   127   6       110812                  3023
    100000   251   6        98314                  1347
    1000000  251   6       980896                 13092
    1000000  503   6       853345                  4616
    1000000  997   6       802315                  2262
    100000   127  60      1245467                 37781
    100000   503  60       945521                  4185

Total 1,718,871 candidate high arrivals,
5,106,098 retained relay-state incidences,
5,036,670 distinct endpoints summed over controls;
66,306 ambiguous endpoints with 72,691 distinct-label
pair incidences (18,331 same multiplier, 54,360 different).
No distinct candidate arrival states shared the same
label at an endpoint. All linear equations (2) checked.
629,118 narrow-band controls, including 2,666 high-
multiplier uniqueness controls in the T>214 domain.
13,976 literal restricted GCD tick checks, 63 independent
reverse enumerations of ambiguous endpoints. Largest
observed number of distinct candidates was 5, in the
K=60,T=127 relaxed control; not a universal bound.
Example in R=1e6,T=503,K=6: endpoint (1000780,502870),
d=4960, candidate arrivals (1000766,502855,p=823,a=3)
and (1000772,502857,r=617,b=4), both minus-side:
3*823-4*617=1. Actual legality of both preceding high
events is not asserted for this relaxed example.

Independent actual path controls: first 10,000 canonical
multiples-of-six roots in each slab, stop before first
twin event or at displacement 4T. 70,000 root/parameter
incidences, 1,374,876 ordinary events; 16,095 retained
actual compressed endpoint incidences within enumeration
domain, all included in the relaxed graph. 364 of those
incidences were at relaxed ambiguous endpoints; these
are not certified actual distinct-origin mergers. Counts
overlap by parameter choices and shared trajectories.
All assertions passed. The growing-cutoff sieve and
asymptotic ancestry budget in (4)-(5) are paper
deductions, not measured rates or kernel-checked facts.

No canonical Lean target or sibling branch changed.
No bound on full medium-dense traffic, favorable
unbounded reset supply, or twin-infinitude proof.
