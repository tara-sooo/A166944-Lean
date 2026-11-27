# Negative MIN: logarithmic local-return counterexample and prime-insertion chain packing

2026-11-27 JST. Continuation of 63230e4bf6b2bffe4492963c69c75d887c78510f.
The previous note proposed three deterministic routes to small
descent concentration: a sublogarithmic worst-case local cap,
a truncated excess capacity, and a spatial excess packing density.
Here the first route is ruled out: C_5(K) >= c log K for all
sufficiently large K, even on canonical-root restricted histories.
The construction uses a fixed ten-tick low block after each of
m chosen large minus resets, CRT avoidance at its rough absorbers,
and the classical quantitative Linnik theorem to make K <= exp(O(m)).
The particular constructed histories have very low reward/gain
and a small formal root probability, so they do not rule out the
excess packing route. We also derive a prime-insertion packing
inequality retaining exact internal-prefix certificates, and a
stronger chain DP preserving the inserted prime's spatial pins.
No asymptotic excess-density upper bound, actual large-height
transfer, twin-infinitude proof or Lean verification is obtained.
Paper-level deductions; no literature priority assertion.

## 1. An exact recurrent small block

Use the negative MIN tick conventions of 326eb62 and
63230e4. At an even position a, absolute n, postheight
h=n+a/2, the next preheight is b=h+1. Its eligible
clock factor is 2b+1 at even n+1, or |2b-5| at odd
n+1; the spatial pin is a=-1 or +1 mod p respectively.
The smallest eligible p fires; otherwise idle.

Start with postheight h=0 and a=44 mod 60.
Then n=-a/2 is even. The following ten-tick
block is forced, irrespective of all primes >5:

    tick  preheight  clock factor  label (1=idle)  postheight
      1       1           3            1               1
      2       2           5            5               0
      3       1           3            3               0
      4       1           3            3               0
      5       1           3            1               1
      6       2           5            1               2
      7       3           1            1               3
      8       4           9            1               4
      9       5           5            5               3
     10       4           9            3               3

For verification, the successive gains just before
these ticks are 0,0,4,6,8,8,8,8,8,12.
All spatial pins and priorities are determined
by a mod 60 and the indicated clock parity.
No larger prime can enter any of these tick
factors. Total gain is 14, elapsed time 10.
The final position is 30 mod 60 with h=3,
so it is a canonical state and is 3,5-rough.

In the interior descent convention, the two
p=5 firings contribute the singleton heights
1 and 4 respectively. The p=3 firings give
empty intervals.

Now let a canonical state at position B=30 mod60
have exactly one eligible prime p among the
restricted primes through cutoff K, with
p=47 mod60 and p>15, on its minus side.
The first minus clock is at preheight
(p-1)/2: the spatial pin gives this residue
mod p, and B/2 and (p-1)/2 are both odd.
There is no earlier clock from another label.
The jump gives postheight 0 and position
B-p+1=44 mod60. Thus the ten-tick block applies,
ending at canonical position B-p-13, again
30 mod60, h=3. The complete reset macro has
gain p+13 and elapsed (p+13)/2. It includes
one large minus firing and five small firings.
It contributes one p=5 descent at EACH of
the fixed absolute heights 1 and 4.

## 2. CRT construction of m consecutive reset macros

Fix an integer m large, let L=2(m+1), and set

    M=60 product_(7<=q<=L, q prime) q.

We will choose distinct primes p_i>L, p_i>15,
i=0,...,m-1, with the following reduced
residue classes modulo M:

    p_i ==47 mod60,
    p_i ==-13 mod q for 7<=q<=L, q!=13,
    p_i == -2 mod13 if i even, +2 mod13 if i odd
                 (last condition only if 13<=L).

All specified classes are reduced: q=13 is
the only prime divisor of 13, and the two
alternating residues there are nonzero.
Define S_0=0, S_(i+1)=S_i+p_i+13. The proposed
macro starting positions are B_i=A-S_i,
i=0,...,m, with A=30 mod60.

At small q>=7, impose A=0 mod q. Then
B_i=0 mod q for q!=13, and B_i=0 or 2
mod13 according to the parity of i.
All these positions are q-rough; all B_i
are also 3,5-rough. At selected prime
p_i impose

    A == S_i-1 mod p_i.

This makes precisely the minus pin at
B_i provided the selected primes satisfy

    S_j-S_i != 0,-2 mod p_i
                   for every j!=i, 0<=j<=m.      (1)

For each other prime q<=K with q>L, choose
A mod q outside the set {S_j+/-1:0<=j<=m}.
At most 2(m+1)=L residues are forbidden,
strictly less than q. The constraints
are independent across primes. CRT
therefore produces an arithmetic
progression of roots A, all positive
and as large as desired. Choose A much
larger than S_m so the physical trajectory
has positive distance and negative
absolute clock throughout.

For i<m, the only eligible restricted
prime at B_i is its designated p_i,
and B_m is a restricted absorber.
The exact macro in section 1 runs at
each B_i. The two singleton descents
are repeated exactly m times at the
same heights, and total gain is S_m.
This is an actual canonical-root
trajectory of the restricted rule.
It also agrees with the full rule
through its last macro: before that
point preheights are at most
max_i((p_i-1)/2,5), so no prime >K
can enter any tick factor.
We do not claim that B_m is an
absorber of the full rule.

For fixed m one can choose p_i
in a sufficiently large common
fixed-ratio band by the ordinary
prime number theorem for fixed
arithmetic progressions. At
stage i, S_0,...,S_i are known.
Avoid primes dividing S_i-S_j
or S_i-S_j-2 for j<i. To protect
all earlier selected primes p_j,
avoid candidates p_i making
S_i+p_i+13-S_j equal to 0 or -2
mod p_j. In a band [Y,2Y] these
exclude O(m) candidates. The
condition for the new prime at
B_(i+1) is automatic:
S_(i+1)-S_i=13 mod p_i, neither
0 nor -2. Exclude earlier labels
themselves. This proves unbounded
C_5(K) qualitatively. A quantitative
selection is needed to rule out
C_5(K)=o(log K), not just boundedness.

## 3. Quantitative selection: the logarithmic lower bound

External standard input, checked 2026-11-27:
Terence Tao, 254A Notes 7, Linnik's theorem
on primes in arithmetic progressions,
22 February 2015, Theorem 2, Exercise 3,
and equations (24)-(25):
https://terrytao.wordpress.com/2015/02/22/254a-notes-7-linniks-theorem-on-primes-in-arithmetic-progressions/

The quantitative Linnik theorem and its
exceptional-zero lower bound imply, uniformly
for reduced classes r mod M and X>=M^D0,
for an absolute sufficiently large D0,

    psi(X;M,r) >> X/M^2                           (2)

for sufficiently large M. In detail,
the no-exception case gives X/phi(M);
in the exception case Exercise 3 gives
epsilon X/phi(M) with
epsilon >> M^(-1/2) log^(-O(1)) M.
The weaker (2) follows since phi(M)<=M.
This input handles the possible real
exceptional zero; a uniform ordinary
PNT for arbitrary growing moduli is
not assumed.

Choose a fixed D>max(D0,10), put
X=M^D and Y=sqrt X. The contributions
of primes <=Y and all higher prime
powers to psi are O(sqrt X log^2 X).
Since D>4 this is o(X/M^2).
Thus for either of the reduced
classes required above,

    #{Y<p<=X: p == r mod M}
                     >> X/(M^2 log X).           (3)

Choose the p_i in this BROADER band,
not necessarily in one dyadic interval.
The previous induction still works:
the two future-pin exclusions for each
earlier p_j>=Y remove at most
2(X/Y+1) integers, so the total is
O(m sqrt X). The past differences
S_i-S_j and S_i-S_j-2 are nonzero
positive integers of size <=m(X+13).
Each has O(1) prime divisors >=Y
because m=O(log M) by the Chebyshev
prime-product bounds; hence these
exclusions remove only O(m) candidates.
The earlier chosen primes cost m more.
For sufficiently large m, (3) dominates
all these exclusions, since D>4.
Thus all m distinct primes can be
chosen <=X=M^D. In particular by
the Chebyshev upper bound log M<<m,

    max p_i <= exp(C m)

for some absolute constant C.
For every sufficiently large K choose
m=floor(c log K) with a sufficiently
small fixed c>0 so that M^D<=K.
All additional q through K are
handled by the same CRT avoidance
in section 2; no monotonicity of
the true restricted cap in K is
assumed or required. We obtain

    C_5(K) >= c' log K                            (4)

for every sufficiently large K.
Since C_z(K)>=C_5(K) for fixed z>=5
and K>=z, the sublogarithmic local
cap criterion (4) in 63230e4 is
FALSE, even its liminf form.
This conclusion concerns worst-case
local-time caps. It is not a
counterexample to the mean-profile
or excess spatial packing conditions,
or to the desired high-clock toll
bound. The absolute heights of the
constructed repeated descents are
1 and 4, not the macroscopic sparse
high-clock heights. The use of
these examples in the unrestricted
maximum C_z(K) is legitimate because
that maximum ranges over all heights.

## 4. Why the counterexample does not obstruct density

For each constructed trajectory the
entire small p<=5 descent reward
is 2m. The truncated excess at cap
r is exactly 2(m-r)_+, while the
half-distance displacement is

    d_total=(1/2) sum_i(p_i+13)>=mY/2.

Consequently its reward/displacement
ratio is <=4/Y. The construction
gives logarithmic local maxima but
negligible spatial reward density.
It does not assert an upper bound
for the worst packed density
rho_(5,r)(K) over all trajectories.

The probability of this particular
family of distinct-prime macro words
is also small in the formal canonical
CRT law. For each fixed ordered word
the designated high pins have probability
prod_i(1/p_i); ignoring all other
constraints gives an upper bound.
In the quantitative construction each
p_i is in one of two prescribed
classes mod M in [Y,X].
The standard Brun-Titchmarsh bound
(as also stated in Tao Notes 7 Remark 4)
and partial summation give

    sum_(Y<p<=X,p=r mod M) 1/p <<_D 1/phi(M).

Indeed Y=M^(D/2), X=M^D, so
log(t/M) is comparable to log t
and the logarithmic integral
over the band is bounded.
Dropping the distinctness restriction
only in the sum over words,
the probability of the family is
at most (C_D/phi(M))^m. Since
log phi(M) >> m by the Chebyshev
lower bound and the elementary
totient product, this is

    exp(-Omega(m^2)).                            (5)

This is a bound only for the
specific prescribed-class, distinct-label
family, not for all trajectories with
large local time. A high-period
CRT transfer to actual slabs is
not assumed.

For a simpler actual-integer contrast,
consider two initial macros from
a canonical seed with their labels
p,r in a single band [Y,2Y], Y>15.
They must be distinct since after
the first macro the position is
-14 mod p, not +/-1. Their root pins
are A=-1 mod p and A=p+12 mod r.
On N canonical roots in a slab,
CRT gives per word <=N/(pr)+1
roots. The total probability is

    << (1+Y^2/N)/log^2 Y.

This in particular is O(1/log^2 R)
at Y comparable to sqrt R and N~R/6.
It bounds this exact initial template,
not a return to an adaptively selected
seed after an unrestricted history.

## 5. One-prime insertion and excess splitting

Return to the spatial packing
criterion of 63230e4. Let K>=z>=5
be prime (or the same odd-prime
alphabet), p the next prime,
Q=prod_(3<=q<=K) q,
s=(p-1)/2, s'=(p_+(p)-1)/2.
Let D_i(b) denote the z-small
interior descent profile of each
K-prefix within a (K union {p})-prefix,
split at its p firings. Write
E_m(D)=sum_b (D(b)-m)_+.

For a run with at least one p firing,
the first and last old pieces are
the two boundary pieces. All other
pieces are internal, between two
consecutive p firings. Since p>z
does not itself contribute to
the z-small reward, at each height

    (sum_i D_i-2m)_+
        <= (D_first-m)_+ + (D_last-m)_+
                              +sum_internal D_i. (6)

For a run without p firing,
E_(2m)<=E_m of its sole piece.
This splitting does not assume
the old pieces have disjoint
height supports. It simply caps
the two boundary pieces separately
and charges every internal
descent in full. This works for
m=0 as exact additivity.

For any relaxed packing of new
alphabet prefixes in a cell of
length Qp, splitting them gives
a relaxed packing of old
prefixes. Old starts are separated
by their prefix displacements
plus at least s: either an
inserted p event or a separator
of label >p. Every old prefix
lies in an old Q-cell by the
old spatial wall. Summing the
ordinary reward across the p
old cells gives

    rho_(z,0)(p)<=rho_(z,0)(K).                  (7)

This is genuine monotonicity
for the RELAXED packing rates,
for fixed z<=K, not for the
individual local maxima and not
for fixed positive truncation m.

For the positive excess, an
internal piece from post-p
target to the next p source
has old total gain 2d satisfying

    2d == sigma+1-tau mod p,

where sigma,tau in {-1,+1}
are the preceding and subsequent
p signs. Thus

    d mod p in {s,s+1,s+2},   d>=s.             (8)

In particular a repeated p
cannot be separated just by
a bounded-gain old block when
p is large. Use for every old
prefix option (x,d) the larger
of its generic E_m reward
and its total reward when
(8) permits an internal piece.
Let the resulting old-cell
packing rate be rho_cong.
Then by (6) and the split

    rho_(z,2m)(p)<=rho_cong<=rho_(z,0)(K).

This double-cap recurrence
alone does not close a
sublogarithmic m(K) sequence.

## 6. Exact internal certificate and chain DP

There is a stronger old-cell
option than (8). For each
old starting phase (x mod Q,
n0 mod 2Q), regard it as
a state immediately after
a p firing of sign sigma
fixed by clock parity.
Lift by CRT to the p pin
a=0 modp for minus or
a=2 modp for plus, and
the clock n=0 or p+2 mod2p.
The old event sequence is
known. At every visited
state compare the next
possible p wait computed
from these lifted residues
with the next old winner.
Because p is larger than
all old primes, it wins iff
its wait is strictly smaller.
The first winning p, if any,
determines the ONLY internal
old prefix for this starting
phase, its displacement d
and terminal sign tau.
If the old path absorbs
without a p winner there
is no internal prefix.
Every actual internal piece
has this certificate.

Define V_m(x,d) as the old
generic excess option from
63230e4 and J_(sigma,tau)(x,d)
as the maximum total small
reward among exactly certified
internal pieces with these
signs and displacement.
Omit nonexistent internal
options. Replacing the
congruence-only bonus with
the maximum certified total
reward gives a smaller
old-cell packing bound
rho_internal. It still
ignores the inserted prime's
spatial coordinate when
choosing the prefix starts
in different cells.

We can retain that coordinate
by a DP on the new Qp-cell,
without full enumeration of
its (Qp)*(2Qp) phase states.
Let H(x) be the relaxed
optimal accumulated reward
from freely chosen new run
starts in [0,x-1]. Let
B_sigma(x) be the relaxed
optimum starting at x
immediately after a p
event of sign sigma, with
later new runs also allowed.
Only x=0 mod p for minus
and x=1 mod p for plus
are allowed for B_sigma.
Work in ascending x.
All prefix options are
taken at x mod Q and
have d>=0; a p step
decreases x by s.

For any generic old option
(x,d) set y=x-d.
A run can end at y with
reward V_m(x mod Q,d),
leaving H(max(0,y-s'+1)).
A freely chosen new run
may instead make its first
p jump at y provided
2y=tau mod p. This
uses the same V_m
reward plus B_tau(y-s).
The forced post-p state
may choose its last piece
and end with the former
exit option, or choose
an internal certified option
J_(sigma,tau)(x mod Q,d)
and add B_tau(y-s).
Compute the maximum B_sigma
of its allowable choices.
Compute H(x+1) as the
maximum of H(x) and all
free-start exit or first-p
choices. All dependencies
are at smaller indices
since s,s'>0. Negative
indices below the cell
are assigned zero;
this is a boundary
relaxation. There is
no assumption that the
clock phases selected
for different pieces
match at their joins,
so this is still an
upper relaxation, not
an exact new phase
enumeration.

Let rho_chain=H(Qp)/(Qp).
Equation (6) and the
spatial p pins show

    rho_(z,2m)(p) <=rho_chain
                   <=rho_internal
                   <=rho_cong
                   <=rho_(z,0)(K).              (9)

For the middle comparison,
split any chain packing
into old pieces, drop
p pins and use the old-cell
certified bonus options.
This yields at most p
copies of the old
cell optimum. The chain
DP incorporates the larger
separator s' when a new
run ends, which the old
cell relaxation discarded.
It gives a computable
upper certificate at
the next prime with only
the OLD phase enumeration.
No asymptotic estimate of
the certified internal
reward density is obtained,
so (9) is not an induction
that proves rho->0.

## 7. Reproducible calculations

Both final scripts were executed in
the ECMAScript research runtime,
fetched from the exact remote
commits and re-executed with
matching outputs. Reproduce with
node. No separate Node or Lean
invocation.

A. research/min_local_negative_repeated_reset_counterexample_audit.mjs
   commit ff1a64617de5a9d2b5e2c80211d1f7d08fda5977
   blob 1835b4d77a05251791e5e304a8903893a29a5faf

Check the ten-tick block using actual
height factors, choose finite prime
lists by trial division and direct
congruence exclusion, check every
selected-prime spatial pin at every
macro boundary and small-q absorber
conditions. For K<=10000 construct
the entire root A by BigInt CRT
and independently replay every
restricted event. For larger K
check free coordinates through
10000; all remaining primes are
handled by the cardinality proof
in section 2, not by enumeration
or explicit construction of the
enormous integer A. Finite examples
use bands found by search; the
quantitative result (4) uses (2)-(3),
not an extrapolation of the
finite search.

    constructed word controls                 8
    selected prime checks                    46
    absorber pin controls                   420
    small-prime controls                    199
    free-coordinate controls               6591
    full BigInt CRT roots                    4
    independent full-root events            60

    m         max selected K     total gain
    1                    347            360
    2                    467            840
    3                   3347           8400
    4                   8807          31920
    6                1427567        7267260
    8               30944747      180720540
   10              904309547     7779151380
   12            14037689807   116454478140

At m=4 the explicit CRT root has
3774 decimal digits and all 24
restricted events match the
expected sequence. At m=12
there are 12 repeated p=5
descents at each of heights 1,4
by the macro certificate.
All checks passed.

B. research/min_local_negative_prime_insertion_excess_packing_audit.mjs
   commit 82fb6cd0920a819b0451fd52c857b143dbc8d6a3
   blob 4f00713c72bb4977cbcaab1dab45dd23b9d06b63

All old phases for K=5,7,11,
next primes 7,11,13 respectively.
Track every old prefix, exact
internal certificate from
post-p state, displacement
and sign congruences, generic
and internal options. Independently
replay combined alphabet after
CRT lift at deterministic
subsample of phase states.
Compute generic, congruence,
exact internal and chain
packing optima and verify
their ordered comparisons.

    old phase states                    2690550
    old prefix steps                    9069762
    exact internal prefixes              394828
    displacement congruence checks       394828
    independent combined replays           2701
    old-cell packing controls            193320
    new-cell chain packing controls       830616

At K=11,p=13 the exact
internal event occurs in
391249 of 2668050 phases
(14.66 percent); its old
half-distance displacement
is between 6 and 47.
There are 656 old spatial
classes with at least one
internal phase, out of 1155.
This is a uniform phase count,
not the distribution of
actual inherited p arrivals.

    K->p    z  old m   rho_cong   rho_internal   rho_chain
    5->7    5    1      .13333       .13333       .04762
    7->11   5    1      .13333       .11429       .05108
    7->11   7    1      .25714       .24762       .14286
   11->13   5    1      .13333       .12641       .05395
   11->13   7    1      .25368       .25195       .13134
   11->13   7    2      .25368       .25195       .11402

The column rho_chain bounds
the NEW rho_(z,2m)(p), not
rho_(z,m)(p). For example
the previous exact K=11
z=7 cap=2 packing rate is
31/1155=.02684, much smaller
than the chain upper .14286
for the 7->11 insertion.
The relaxation improvement is
real but still too loose to
claim contraction. No full
K=13 phase enumeration has
been performed.

## 8. Status and next target

The sublogarithmic worst-case cap
is now ruled out by (4), not just
suspected to be difficult. In
particular a proof strategy
requiring C_z(K)=o(log K)
cannot succeed. Large local
maxima can arise from repeated
high reset macros with tiny
normalized reward; (5) also
bounds the formal probability
of that specific family.
The remaining relevant
deterministic target is the
truncated excess spatial density,
or the weaker mean-profile
criterion of 891cdb3. The
chain bound (9) gives exact
internal compatibility and
an improved finite upper
relaxation for prime insertion.
It doubles the cap and has
not been shown to contract.
A future estimate must isolate
the density of long compatible
internal prefixes or seam
overlap rather than the
unrestricted local maximum.
This is not a proof of
small descent concentration
or full gain saving.
No twin-infinitude proof,
Lean verification, canonical
target, sibling branch, or
Context changes.
