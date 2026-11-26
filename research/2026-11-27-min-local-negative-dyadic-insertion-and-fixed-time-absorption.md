# Negative MIN: dyadic insertion, delayed repair, and the fixed-time absorption law

2026-11-27 JST. Continuation of 574a789a0efd07e16f3686161e259bcf77cdcffb.
This block develops the requested cutoff-expansion recursion, including
interruption of an existing path and repair after absorption. A wall-gap
argument provides uniform positive matching probabilities even for
budgets near twice the base cutoff. A delayed-repair inequality gives
a new conditional route to unbounded local moments. Exact local-profile
identities also relate the formal fixed-time gain law to the restricted
absorption law and give an unconditional logarithmic-scale upper bound.
On actual integer slabs the adaptive-profile sieve yields weighted
cutoff-increment bounds. The remaining near-square-root lower bound,
the positive formal absorption fraction, and twin infinitude are not
established. All deductions are paper-level, not Lean verification or
a claim of literature priority.

## 1. Formal canonical root law and conventions

For a finite alphabet of odd primes containing 3 and 5, use the
restricted negative MIN rule: the least (wait,prime) eligible event
wins. At a position a, the minus clock requires p|a+1 and n=0 mod2p;
the plus clock requires p|a-1 and n=p+2 mod2p. The jump decreases
a by g=p-1 and advances absolute time by its positive wait w.
The canonical root A=6j starts at n=3-A/2, height h=3.
The finite spatial walls of 0116e3e guarantee absorption into
a position with neither neighbor divisible by any allowed prime.
The mod-30 potential of 2021e5a applies to any such restricted
alphabet, since both 3 and 5 are included:

    W <= 9G/4+8, h=3+W-G/2.

Here G and W are the completed gain and elapsed waits. The event
barrier of 676c259 applies to the same restricted rules:
the preheight b of a completed event satisfies G_plus>=18b/35-10.
These facts are used for the purely formal residue extension as
well as actual physical roots.

For integer y>=5 let P_y be the odd primes <=y, G_y the full
restricted gain at absorption, and F_y(L)=Pr(G_y<=L).
Take the probability over a uniform canonical period, equivalently
independent uniform root residues A mod p for p>=5 in P_y,
independent uniform parity of A/2, and A mod3=0.
For nested cutoffs use the same low coordinates and independent
new coordinates. This is an exact finite CRT probability space.
It is not an approximation to the distribution in an arbitrary
actual interval of length R.

Write V(y)=prod_(5<=p<=y)(1-2/p). Use local moments mu_r(L)
from 8d83274 and 574a789, with Z_L=2 floor(9L/4+8)+7.
Their unconditional bound can be sharpened in notation to

    1 <= mu_1(L) <= 1/V(L+1)                    (1)

for L>=6, by the restriction/preemption identity of 574a789
at y=L+1, since its numerator is at most one.

## 2. Exact insertion decomposition for a doubled cutoff

Take Y=2y, L=2y-2. The same reasoning applies with any larger
Y when counting only zero/one specified added events, provided
the budget L stays below 2y. Every successful P_Y path uses
at most one EVENT with p>y, since each such event gains
at least y. A repeated new label is also impossible within
the budget. Do not assume that the added event occurs after
the original absorber: it may preempt an old event.

Fix the low root coordinates. For a successful restricted
path of gain G<=L, define B_q for an omitted q>y as follows.
For every waiting interval of this path inspect each tick
strictly before its selected firing, and the selected firing
tick itself if q is smaller than the selected prime. If q
could fire at that tick, record the required ROOT residue
A mod q, namely G_pre-1 for the minus clock or G_pre+1
for the plus clock. Eligibility of q as a height factor
is checked first: q divides 2b+1 at an even absolute tick
or 2b-5 at an odd absolute tick. Finally add both residues
G-1 and G+1 so that the terminal position is q-rough.
Take DISTINCT residues in B_q. With independently uniform
omitted root coordinates the exact matching-and-absorption
probability is

    Pi = prod_(omitted q)(1-|B_q|/q).             (2)

The tie rule is essential at the firing of a selected new
prime. For a zero-new path all omitted primes are larger
than every selected label and cannot win a tie.

Let Pi_0 be (2) on the successful P_y path with all primes
in (y,2y] omitted. For each p in (y,2y], and each root
coordinate rho mod p, run P_y union {p}. Let A_(p,rho)
mean this path absorbs within L and uses p exactly once.
Let Pi_(p,rho) be (2) on that path with all other added
primes omitted. Then the exact identity is

    F_(2y)(L)
      = E_low[1{G_y<=L} Pi_0]
        + sum_(y<p<=2y) (1/p) sum_(rho mod p)
                 E_low[1{A_(p,rho)} Pi_(p,rho)].              (3)

For necessity, delete all the unused new labels from an
actual successful path: its winners remain unchanged,
and its terminal position is rough for the retained labels.
For sufficiency, the forbidden sets prevent every earlier
preemption and every smaller-prime tie, and ensure absorption
at the same endpoint. Distinct terms are disjoint in the
full residue space, classified by the unique new label
actually used and its coordinate. This includes all cases
with arbitrarily long old-label prefixes and suffixes.
Formula (3) is not a closed recursion in the scalar CDF
F_y alone: it retains correlations with the low environment.

## 3. Wall gaps give a uniform matching lower bound

A useful improvement over bounding each B_q just by the
total displacement is to count holes skipped by the jumps.
Let the distinct completed source/arrival gains of a
candidate path be 0=G_0<G_1<...<G_m=G, with
g_i=G_i-G_(i-1) even and positive. Every forbidden root
coordinate in (2) is a reduction modulo q of a member of

    U={G_i-1,G_i+1: 0<=i<=m}.

In ordinary integer offsets, exactly

    |U|=G/2+2-sum_i max(0,g_i/2-2).              (4)

Indeed each increment g_i/2 in the half-gain index leaves
max(0,g_i/2-2) missing odd offsets between its two adjacent
two-element sets. The g_i=2 case has one overlapping
offset; the g_i=4 case has no gap and no overlap.

Use the spatial wall for P={3,5}, maximum half-gap M=9
as in 83647a1. Each contiguous run of these labels gains
at most 16. Write G_hi for total gain of all other labels,
whose individual gains are >=6. Since there are at most
G_hi/6 such events,

    G <= G_hi+16(G_hi/6+1),
    G_hi >= 3(G-16)/11.

For each g_i>=6 the hole term in (4) is >=g_i/6.
Consequently

    |B_q| <= |U| <= (5/11)G+30/11.              (5)

This is valid for arbitrary full event depth and any
allowed alphabet containing 3 and 5. For L=2y-2,
(5) gives |B_q|/q<=10/11+O(1/y) for q>y.
For a one-new-event path of label p>y its single jump
alone removes (p-1)/2-2 offsets, yielding the stronger

    |B_q| <= (G-(p-1))/2+4 <= y/2+O(1).         (6)

The total forbidden density also has a simple bound.
All path preheights are at most 3+W=O(y), so at a tick
the height factor integer has at most one prime divisor
>y for sufficiently large y. The W ticks can contribute
at most W distinct (q,residue) tests, even when a
selected prime is included in the tie check. Terminal
roughness contributes two per omitted prime. Thus for
Y=C y with fixed C>=2,

    lambda=sum_q |B_q|/q
       <= W/y+2 sum_(y<q<=Cy)1/q
       <= 9/2+o(1).                            (7)

Here the last reciprocal sum is O_C(1/log y).
For t in [0,b], -log(1-t)/t is increasing, with
limit 1 at zero. Combine (5) or (6) with (7).
For sufficiently large y, uniformly for the selected
candidate paths,

    Pi_0 >= exp(-13), Pi_(p,rho) >= exp(-7).    (8)

For example the limiting exponents on the right
of -log Pi are bounded respectively by
(9/2)*(11/10)*log 11 < 13 and 9 log 2 < 7.
The bounds also work with omitted primes up to 16y,
not just up to 2y. This is a new uniform lower bound
at gain budget almost twice the base cutoff; the
earlier conditional target-rough argument in 574a789
used a cutoff at least the entire budget.

Define J_y to be the second sum in (3) with the Pi
factors replaced by one. Then

    exp(-13)F_y(L)+exp(-7)J_y <= F_(2y)(L)
                              <= F_y(L)+J_y.     (9)

These constants do not imply a positive uniform
F_y(y) lower bound by iteration. A quantitative
bound on the loss and reabsorption distribution
is still required.

## 4. Short old paths and the repair kernel

Put s_y=floor(y/5), for y sufficiently large.
If G_y<=s_y, all preheights of the old absorbing
path are at most (35/18)(s_y+10). This is below
(y-1)/2 for sufficiently large y. Every earlier
tick in its waits is below the same maximum.
No omitted label >y can preempt that path before
absorption. Thus for the short old cohort, an
added p can first act only at its old absorber,
and only for the two residues rho=G_y+/-1 mod p.
The exact chance of no activation through any
fixed larger cutoff Y is V(Y)/V(y).

For each old short root choose p in (y,2y] with
probability proportional to 1/p, and one of
these two activating residues with equal weight.
Run the single-insertion restricted process
P_y union {p}. Define r_y to be the probability
that it absorbs within the budget 2y-2, with
the old root distribution conditioned on G_y<=s_y.
On success it necessarily uses the new p exactly
once. For Y=2y, define r_y^w to be the expectation
of the success indicator times its Pi_(p,rho),
where the other new primes are omitted. Then
exp(-7)r_y<=r_y^w<=r_y for sufficiently large y.
Writing S_y=sum_(y<p<=2y)1/p, the contribution
to F_(2y)(2y-2) of old short roots is exactly

    F_y(s_y) [ V(2y)/V(y)+2 S_y r_y^w ].        (10)

This follows from the disjoint decomposition (3).
It isolates a repair probability after activation,
including the budget cost of the new jump and the
entire subsequent old-label path. No independent
sampling of the old absorber and the repair path
is assumed.

There is a delay in using (10) to propagate *short*
cohorts: a repaired path gains at least y, whereas
the short budget at cutoff 2y is only 2y/5.
Thus a successful repair cannot rejoin the short
cohort immediately. Expand instead to cutoff 16y,
keeping the same one-insertion labels p<=2y and
budget 2y-2. They fit s_(16y) for large y, and (8)
ensures survival against ALL other added labels
up to 16y with weight >=exp(-7).
The zero-new short paths and these repaired paths
are disjoint. Therefore

    F_(16y)(s_(16y)) >=
        F_y(s_y) [ V(16y)/V(y)+2 exp(-7) S_y r_y ].
                                                               (11)

For y>=Z_(s_y), exact local mass transport gives
F_y(s_y)/V(y)=mu_1(s_y); see section 5.
Normalize (11):

    mu_1(s_(16y)) >= mu_1(s_y)
             [1+2 exp(-7) S_y r_y].            (12)

This uses V(y)/V(16y)>=1, so slightly weakens
the exact normalized inequality. On geometric
scales y_j=16^j y_0, the prime number theorem
gives S_(y_j) comparable to 1/j.
It follows that the condition

    sum_(j>=1) r_(y_j)/j = infinity             (13)

would imply mu_1(L)->infinity. The proof
is to multiply (12), use log(1+x)>=x/2
for small x, and monotonicity of mu_1(L).
If r_(y_j)>=c>0 eventually, it gives
mu_1(L)>> (log L)^delta for some delta>0.
This is weaker than proving saturation
mu_1(L)~1/V(L+1), but provides a distinct
conditional target for unbounded growth.
No analytic estimate sufficient for (13)
has been obtained. The finite samples below
suggest nontrivial repair, but cannot prove (13).
In particular (12) by itself does not establish
even a positive limit inferior of F_y(y).

## 5. Exact small-budget transfer between formal cutoffs

For every integer L>=6 and y>=Z_L, there is the
exact identity

    F_y(L)=V(y) mu_1(L).                         (14)

Proof: on the full residue period for P_y,
count the roots A absorbed with G<=L by their
endpoint a. Each endpoint is y-rough. Its
incoming mass with this gain cap is exactly
b_L(a) from 8d83274, because the height-local
rule before any such arrival uses primes <=Z_L.
All local successful paths match the restricted
rule and stop at a y-rough endpoint. Conversely
every such restricted path reaches a within
T_g=floor(9g/4+8) and all its clocks agree
with the local rule. Average b_L over the
endpoint residues in the same period. The
proportion of y-rough endpoints is V(y), and
conditional on roughness the low coordinates
are the product law used to define mu_1(L).
This proves (14) by finite mass conservation.
For L<6 the same reasoning with only the
zero offset gives the corresponding identity.

In particular for fixed L, enlarging y beyond
Z_L deletes endpoint residues but changes
neither the possible low-gain paths nor their
local coefficients. For cutoffs z,Y>=Z_L,

    F_Y(L)/F_z(L)=V(Y)/V(z).                    (15)

This can also be seen directly from the absence
of earlier omitted clocks before any bounded-gain
absorber. It is an exact relation, not a heuristic
assumption of independent histories at new scales.

## 6. Unconditional bound on the logarithmic gain scale

For fixed 0<alpha<1, let L=floor(y^alpha).
Then y>=Z_L for all large y. By (1),(14)
and Mertens' product estimate,

    F_y(y^alpha) <= V(y)/V(floor(y^alpha)+1)
                 = alpha^2+o(1).               (16)

Thus even the conjectural G_y/y -> 0 in
probability cannot imply that G_y<=y^alpha
with probability tending to one at any
fixed alpha<1. The broad logarithmic range
of gains is necessary. More generally, for
growing L=o(y) with log L=o(log y), the
same estimate shows F_y(L)->0.

Write X_y=log(1+G_y)/log y. By integrating the
tail probabilities on [0,1] and (16) (or Fatou),

    liminf E[min(X_y,1)] >= integral_0^1(1-t^2)dt
                            = 2/3.             (17)

No upper moment bound on the untruncated G_y
is required here. The result concerns the
formal uniform root environment, not actual
integer slab statistics.

Define the normalized local mass coefficient

    B(L)=V(L+1) mu_1(L) in [0,1].

For fixed alpha as above the exact formula (14)
gives F_y(y^alpha)= (alpha^2+o(1)) B(floor(y^alpha)).
Hence IF B(L)->sigma in [0,1], the limit
F_y(y^alpha)->sigma alpha^2 exists. In the
saturation case sigma=1, the logarithmic
gain variable converges in distribution
to the law with CDF t^2 on [0,1],
since the upper tail above y also vanishes
by section 7. This law is a consequence of
saturation, not evidence that saturation
has already been proved.

## 7. Equivalence of saturation, small restricted gains and formal mean gain

Let D_T be the completed gain by elapsed tick T
of the formal full MIN, with independent uniform
root coordinates for all odd primes (canonical
coordinate at 3, independent root parity).
Every finite horizon uses only primes <=2T+7
by height locality. Couple restricted processes
with the same coordinates. For integer L and
sufficiently large T, define

    y_+=2T+7,
    y_-=floor((T-9L/4-9)/2).

For 0<=L<=T/16 we have y_->=Z_L for large T.
The following inclusions are pathwise:

    {G_(y_+)<=L} subset {D_T<=L}
                       subset {G_(y_-)<=L}.     (18)

For the first: the restricted trajectory agrees
with full MIN through tick T; an absorption
with gain<=L occurs by 9L/4+8<T, and no allowed
prime fires later. For the second: if D_T<=L,
the time of the last completed event W satisfies
W<=9L/4+8. The current position has an idle
interval T-W>2y_-. Every eligible neighbor
factor p<=y_- would fire within 2p ticks of
that arrival, contradiction. Thus the endpoint
is y_--rough. Every completed label is <=L+1
and hence allowed by P_(y_-), and the restricted
rule has those exact winners. It absorbs at
the same position and gain by the last arrival.
This also covers a root with no events, using
W=0. The -9 in y_- avoids endpoint rounding
issues.

Combining (18) with (14), and noting that y_-
and y_+ are both within fixed constant multiples
of T, gives uniformly for this budget range

    Pr(D_T<=L)=(1+O(1/log T)) V(T) mu_1(L).     (19)

The ratio estimate uses the elementary reciprocal
prime bound in a constant-ratio band. It is a
formal finite-horizon law, with no asymptotic
assumption on mu_1. It holds also for small fixed
L. In particular the logarithmic-scale upper
bound (16) applies to D_T, with T replacing y.

These three formal statements are equivalent:

    (i)  B(L)=V(L+1)mu_1(L) -> 1;
    (ii) for every epsilon>0, F_y(epsilon y)->1;
    (iii) E[D_T]/T ->0.                         (20)

For (i)->(ii), apply (14) at L=floor(eta y)
with any fixed eta<min(epsilon,1/5).
The ratio V(y)/V(L+1)->1.
Conversely (ii) gives B(floor(y/5)) ->1
by (14), and the integer arguments cover
every sufficiently large integer. For
(i)->(iii), use (19) at L=floor(eta T)
for arbitrarily small positive eta<1/16,
and the deterministic cap D_T<=2T+6
from nonnegative height. For (iii)->(i),
Markov gives Pr(D_(16L)<=L)->1, so (19)
and the ratio V(16L)/V(L+1)->1 give (i).
This proves (20). In the saturation case,
the log-scale CDF in section 6 also follows
for D_T.

The formal probability statement in (iii)
is not the actual slab mean-gain estimate
required in d9f6049. Nevertheless (19)-(20)
connect the two proposed formal research
directions without extra modeling assumptions.

## 8. Actual integer cutoff increments with weighted local profiles

Return to the actual canonical slab A in [R,2R].
Write m_y(a,L) for the number of these roots
absorbed at a under restriction P_y with G<=L,
and S_r(y,L;R)=sum_a m_y(a,L)^r for fixed integer r>=1.
Assume L<=c_r log^2 R/loglog R with the small
constants of 574a789, and Z_L<=y<=C sqrt R,
y tending to infinity. For each possible endpoint
in [R-L,2R],

    m_y(a,L)=1{a is y-rough} b_L^slab(a),       (21)

where b_L^slab is the local profile with offsets
whose starting roots are in the slab. It is
bounded by b_L(a), and equals it away from the
boundary. This follows from exactly the same
locality proof as (14), without probabilities.
All successful paths are physical for large R:
elapsed arrival time is O(L), A-a<=L, and
absolute time remains negative.
In particular cutoff expansion never increases
these fixed-budget masses; they are deleted
only at endpoints that fail the new roughness
condition.

A deleted endpoint between y and 2y has
some prime q in (y,2y] dividing a-1 or a+1.
For each q and side, use the adaptive local
transcript upper sieve in 574a789, sections 2-6.
The extra condition selects one class modulo q
in the progression for the accepting transcript;
q>Z_L, so it is coprime to its small modulus
and positive pins. Require free-prime endpoint
roughness only up to Y0=min(y,R^xi), xi>0
a sufficiently small fixed number for the
block sieve's divisor support. For all large
R, Y0>=Z_L. The free factor is V(Y0)/V(Z_L)
and V(Y0)<< V(y), uniformly since y<=C sqrt R.
The sum of accepting weights over tuples and
low classes is V(Z_L)mu_r(L) by (5) of 574a789.
The medium-block weighted errors remain
negligible by (3),(6) there. Thus the upper
main term for each q is O(R mu_r(L)V(y)/q).
The summed absolute CRT remainder over all
q and sides, small classes, transcripts and
tuples is R^(1/2+6u+o(1)) with u=1/100,
as in section 4 of that note. It is negligible
compared with R mu_r(L)/log^3 y.
Summing the reciprocal q bound in the dyadic
band therefore yields

    0 <= S_r(y,L;R)-S_r(2y,L;R)
                  << R mu_r(L)/log^3 y.         (22)

The upper count can use b_L instead of the
boundary-truncated profile, so no boundary
subtraction is needed. For a final partial
doubling the same bound holds. This is a
weighted cutoff increment estimate for
all event depths within the indicated
polylogarithmic budget, without needing
an energy bound on the selected cohort.

Sum (22) along doubling steps from y0 to y1
within the range. With fixed budget L throughout,

    S_r(y1,L;R) >= S_r(y0,L;R) -
       O(R mu_r(L) [1/log^2 y0 -1/log^2 y1
                                      +1/log^3 y0]).           (23)

A lower bound of order R mu_1(L)/log^2 y0
at y0=R^alpha (small fixed alpha in the
lower-sieve range) implies preservation
of a positive fraction of the mass to
y0^(1+delta) for some sufficiently small
fixed delta>0. Constants do not show
that this goes beyond the known lower-sieve
range. At y0 comparable to sqrt R/log^B R
and y1 comparable to sqrt R, the total loss
is O(R mu_r(L) loglog R/log^3 R).
If a lower bound of order R mu_1(L)/log^2 R
were obtained at y0, then some actual
successful roots survive to cutoff above
sqrt(2R+1), where their endpoint is a twin
center. This is a weighted form of the
earlier semiprime-frontier transfer.
It still requires the same missing lower
bound near sqrt R.

The deterministic inclusions (18) apply also
to every actual slab root with T=o(R).
At T=ceil(8 sqrt(2R+1)), L<=T/16, both
cutoffs y_-,y_+ are above sqrt(2R+1) and
y_->=Z_L for sufficiently large R.
Any gain-budget absorber under either
restriction is a twin center, and by
locality its arrival prefix is the actual
one. Its two neighbor labels are of order
R, so it is idle through tick T. Consequently
all three sets in (18) coincide for the
actual roots in this parameter range.
This is not true of general formal
product-coordinate environments.
The equality illustrates that the
formal asymptotic (19) must not be
transferred to actual square-root horizons
without an additional finite-slab theorem.
No such theorem is established here.

## 9. Executed audits

A. research/min_local_negative_dyadic_insertion_repair_audit.mjs
   commit c94a0d7689556561888bc428a4e09f92f4eca65d
   blob 19b16fd131b2ac4989feaaf3864ed80af15f61c5

Executed in ECMAScript research runtime, fetched at the exact
remote commit and independently re-executed with identical output.
Reproduce with node. No separate Node or Lean invocation.

For y=5,7,9,10 enumerate both the old full periods and the
full periods at 2y. For each old root and each added prime
and residue, simulate the single-insertion rule to absorption
or budget stop. For accepted zero/one paths use integer counts
of the omitted residue assignments in (2). Compare the exact
sums (3) with complete enlarged-period enumeration.

    exact cutoff controls                 4
    old root classes                    220
    full root classes               3413480
    single-insertion trials            8820
    accepted insertions                 401

    y   full period    zero-new successes  one-new successes
     5       70                  47                 7
     7    10010                5667               706
     9   170170               82964             10203
    10  3233230             1446856            448664

All exact comparisons passed. The last case has 114728
one-new successes whose insertion preempts the old
absorption path, and 333936 insertions at the old absorber.
This is a finite illustration that both cases matter.

For larger cutoffs use fixed-seed product-coordinate
samples, sharing residues across cutoffs and replaying
forced insertions. The old/extended gain budget is
2y-2. The short cohort for this finite audit uses the
explicit sufficient event-barrier condition
35*(G+10)*2<18*(y-1), or G=0, not exactly floor(y/5).
This distinction matters at small y. Sample a forced
new p with weight approximately proportional to 1/p
(using a discrete 24-bit uniform sampler), then force
one of the two activating residues. The estimates
are numerical, not exact arithmetic expectations.

    sampled roots                     5376
    forced repair trials              1947
    budget repair successes           1027
    complete matching comparisons     4994
    short-path stability checks       1947
    no early preemption checks         316
    certificate evaluations           8569
    low-run wall checks              68628
    offset-union identities           8569
    forbidden prime checks         2437921

All assertions passed. The sample result is:

    y      n    F_y(2y-2)  F_2y(2y-2)    forced repair  weighted repair
      96  2048    .82813      .64258         .45800        .31088
     384  1536    .88867      .75195         .47610        .35269
    1536  1024    .94336      .81445         .50870        .39200
    6144   512    .97852      .89063         .65246        .52235
   24576   256    .96094      .89844         .72956        .59822

At y=24576, 159 roots pass the finite short test;
the forced insertion fits its budget before the
repair suffix for 153, and 116 absorb within
the whole budget. The weighted repair factor
averages the exact omitted-set product times
the success indicator over all 159 trials,
not only the successful ones. The actual
paired full sample has 219 zero-new successes
and 11 one-new successes. Only the sampled
finite values are reported; no uniform repair
probability follows. These data do not test
the delayed repair at cutoff 16y; (11) uses
the proven uniform certificate bound.

B. research/min_local_negative_fixed_time_absorption_sandwich_audit.mjs
   commit a763369c598073beb49f479fe450099ed1a2eb78
   blob 83be685aded75ae454244364f1f1e5018e71d104

Executed, fetched at the exact remote commit
and re-executed with identical output.
Use the exact height-local tick rule on
shared root coordinates; compare completed
gain at T with restricted absorption at the
two cutoffs in (18), for several budgets <=T/16.
On success compare both endpoint gain and
arrival elapsed time. Verify final roughness.
Use actual integer residues on a deterministic
sample of canonical roots for four slabs.
These physical controls use the same tick
implementation with actual residues, not an
independent next-event implementation.

    formal environments                 5088
    full formal ticks               18874368
    restricted formal ticks          4229346
    formal sandwich checks             13216
    physical roots                      2153
    physical tick computations      24758907
    physical sandwich checks            6459
    successful same-prefix checks       4395
    final roughness checks              4709

All assertions passed. Formal fixed-seed means:

     T      sample size    E_sample[D_T]/T
     256        2048          .676987
    1024        1536          .567445
    4096        1024          .445590
   16384         384          .324112
   65536          96          .368011

The last group is small and the ratios are
not monotone; no limiting mean estimate is
inferred. For physical T=ceil(8sqrt(2R+1)),
R=12000,48000,192000,1000000, the sampled
mean ratios are .15023,.18316,.14564,.11320.
For every tested physical budget the two
restricted successes and the full low-gain
successes coincide, in agreement with
section 8. These are finite deterministic
subsamples (step 97 in the canonical root
index), not independent full-slab estimates.
The full-slab result in d9f6049 is separate.
The script output contains one unused
counter absorptionComparisons=0; all actual
inclusion comparisons are recorded in the
sandwich counters above.

No new independent test of the asymptotic
sieve error in (22) was run; it uses the
previously audited adaptive block-sieve
argument of 574a789 with a dyadic extra
prime condition.

## 10. Remaining proof target

The one-insertion identity and wall-controlled
matching probabilities address the cutoff
recursion, including preemption and repair.
The delayed repair inequality gives a
specific sufficient condition (13) for
unbounded local mass; no sufficient lower
bound on r_y is proved. The unconditional
logarithmic gain constraint (16) and the
equivalences (20) connect the formal
absorption and fixed-time mean questions.
Neither saturation nor a positive constant
formal absorption fraction is established.
For actual slabs the new weighted increment
estimate (22) is valid within the enlarged
local gain budget, but the lower bound at
near-square-root cutoff is still missing.
The larger-budget actual fixed-horizon mean
route likewise lacks an asymptotic gain
saving. No twin-infinitude proof or Lean
verification, and no changes to the
canonical Lean targets or sibling branches.
