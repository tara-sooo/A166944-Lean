# Local support at near-square-root crossing lengths

2026-11-26 JST. Continuation of 2ef49f9c668240e633188b62893a33f621aee053.
Paper extension of the pinned parent's local-label capacity proof and
support-gap lemma, plus executed finite diagnostics. No Lean verification,
novelty claim, or twin-infinitude proof.

## 1. Adaptive cofactor sieve

Use the prior MIN setup and non-twin local capacity C(I,p) from the
local-label-diversity note (pinned parent 5aef6a4). Let R grow,
1<<L<=log R (L may instead be a sufficiently large fixed constant),
D=ceil(sqrt(R)*L), and I contained in [R,2R) of length <=D.
The following constants are absolute for sufficiently large R,L.

For p<=sqrt(R)*sqrt(L), put N=D/p >=sqrt(L).
For a non-twin even source u, q(u)=min(lpf(u-1),lpf(u+1)).
Split C(I,p) into q<=sqrt(p)/2 and q>sqrt(p)/2. The first contributes
O((N+1)*sqrt(p))=O(D/sqrt(p)).
For the second, write the selected neighbor pm and the other pm+/-2.
Both m and pm+/-2 avoid odd prime factors <=sqrt(p)/2. Their two
forbidden roots mod every odd sieve prime ell<p are distinct.
Instead of the parent's cutoff floor(p^(1/20)), choose
z=floor(min(p,N)^(1/20)). For sufficiently large min(p,N), z is below
sqrt(p)/2 and p. The same explicit two-form Selberg sieve used in the
parent gives, for each sign and m interval length <=N+O(1),

    count << N/log^2 z + z^6.

This use of the inherited estimate is uniform in p because the two
local roots are distinct and p is coprime to all sieve moduli. Here
z^6<=N^(3/10), so the error is absorbed by N/log^2(2+min(p,N)).
Multiply by 2p. The low-q contribution is absorbed too, since
log^2(2+min(p,N)) << sqrt(p). Bounded min(p,N) is handled by
the trivial count after enlarging the constant. Thus

    C(I,p) << D/log^2(2+min(p,D/p))                  (1)

for p<=sqrt(R)*sqrt(L). This is a cofactor-interval-sensitive estimate,
not the old D/log^2 p estimate at the square-root scale.

For p>sqrt(R)*sqrt(L), use q<=sqrt(2R+1):

    C(I,p) << (D/p+1)*sqrt(R) << D/sqrt(L).          (2)

For a single actual non-twin path the total wait across ALL events
with these far-tail labels also satisfies O(D/sqrt(L)): each gain
except the final event telescopes into D and the number of such
events is <=D/(sqrt(R)*sqrt(L)-1)+1. Every wait is O(sqrt(R)).
This removes the tail without counting its distinct labels.

With T=ceil(log R) and L<=log R, (1)-(2) imply uniformly for all
p>=T that C(I,p)<<D/log^2 L. All of these conclusions include the
last event even if its arrival lies outside I.

## 2. Near-square-root support criterion

Let 0<delta<1 be fixed and K<=floor((1-delta)log_2 log R).
Use an actual consecutive non-twin segment in I with K distinct
labels. Repeat the parent gap scan in increasing p using T=ceil(log R);
stop at the first p>=T with p>TQ, where Q=2 times the product of
included labels. The same recursion Q_i<=T Q_(i-1)^2 gives
log Q=o(log R) uniformly, since 2^K log(2T)=o(log R).
If all labels are included, W<=3Q by the primorial wall.
Otherwise, small runs contribute <=3Q(D/(p-1)+2)=O(D/T+Q).
The K or fewer tail labels each have capacity O(D/log^2 L).
Consequently

    W/D << 1/T + Q/D + K/log^2 L.                  (3)

The constant in the last term is absolute. Taking
L=exp((log log R)^beta) for any fixed 1/2<beta<1 makes the
right side o(1) uniformly. So the previous unbounded-subsequence
criterion with the SAME K_R now works with D=ceil(sqrt(X)*L)
at R=X. The envelope lower bound W>=D/2-3 gives the contradiction.
For beta=3/4 this is a substantially shorter window than X^(3/4).

More generally the conclusion works whenever K<=K_R and
K/log^2 L ->0. Even the little-o condition can be replaced by
a sufficiently small absolute bound on K/log^2 L, because (3)
has absolute constants and the other terms vanish. In particular
there exists an absolute A>0 such that for L=exp(A sqrt(log log R))
the same K_R is sufficient. No effective numerical A is claimed.

For every fixed positive integer K, there exists a fixed L_K>0
such that a path with at most K labels cannot be a non-twin crossing
of D=ceil(L_K sqrt(X)) for all sufficiently large X. Choose L_K
so the last term in (3) is <1/4 and use Q=polylog(R).
Thus fixed support requires only a constant multiple of sqrt(X),
not a growing power of X. This is still a sufficient condition on
an unbounded sequence, not a proof of its existence.

For comparison, the elementary event-count criterion follows
from W<=2N sqrt(2X+1) and W>=D/2-3, giving N=Omega(L) on a
non-twin crossing. The support criterion permits arbitrarily many
repetitions of the same labels and is not merely that count bound.

## 3. Refined significant-label criterion in the shorter window

Let 0<epsilon<3/8 be fixed, and use L=exp((log log X)^beta),
1/2<beta<1. For clarity use a new small-label cutoff X^(1/8)
(previous paper used X^(1/4) at the longer D). Call a low label
frequent if used more than X^(1/8) times. Let F count these distinct
frequent low labels, H_mid count distinct significant labels in
[X^(1/8), X^(1/2-epsilon)], and H_near count distinct significant
labels in (X^(1/2-epsilon),sqrt(X)*sqrt(L)]. A significant label
has at least one event with w>=alpha*(p-1), for a fixed 0<alpha<1/2.
No support restriction on the far tail.

The following conditions along an unbounded reset sequence suffice
for twin infinitude:

    F <= floor((1-delta)log_2 log X),
    H_mid=o(log^2 X),
    H_near=o(log^2 L).

Proof: under the non-twin hypothesis, infrequent low wait is
O(X^(3/8))=o(D), with O(X^(1/4)) interruptions. All labels >=X^(1/8)
give O(D/X^(1/8)+1) interruptions. Apply the same gap scan to frequent
low labels; included runs cost <=3Q per run. The extra interruptions
cost O(Q*(X^(1/4)+D/X^(1/8)+1))=o(D), because Q=X^o(1).
Remaining frequent low labels above the gap cost
O(D*F/log^2 L)=o(D) by (1)-(2); their interruptions cost O(D/T+Q).

For mid labels both p and D/p are >=X^min(1/8,epsilon); (1) gives
O_epsilon(D/log^2 X) per label. For near labels the capacity is
O(D/log^2 L). Hence all significant mid and near labels together
cost o(D). Their insignificant counterparts cost <=alpha D+O(sqrt X)
by gain telescoping and the final wait bound. All far-tail events
cost O(D/sqrt L)=o(D) without label restriction. Sum:
W<=alpha D+o(D), incompatible with W>=D/2-3. The same argument
allows explicit sufficiently small constants in place of the little-o
conditions. The finite-twin hypothesis ensures every sufficiently
large reset remains non-twin, so the asserted sequence suffices.

The distinction between medium and square-root-scale labels matters:
only the narrow high range loses the log^2 X sieve saving. This
extends the previous sufficient condition without demanding few
distinct medium labels or controlling very large labels at all.

## 4. Executed diagnostics

Source: research/min_local_near_sqrt_audit.mjs,
commit 3ffd167a595040803919905c34c5d759c7e0ad8a,
blob 2eb6e644f082e03c27f1702f74cd187ed1912231.
Run node research/min_local_near_sqrt_audit.mjs 1000000.
Executed as ECMAScript in the research runtime, then fetched at
the exact commit and re-executed. No Node process or Lean invoked.

Four widths for every root in the same three inclusive slabs:
power=ceil(X^.75), near=ceil(sqrt(X)*exp((log log X)^.75)),
log=ceil(sqrt(X)*log X), sqrt=ceil(sqrt X). All final events included.
For each mode 101667 roots; 28930 individual literal GCD tick
controls across the modes; 3112 ambient interval-label capacity
sums (finite normalized ratios only, not a proof of asymptotics).
Envelope, first clock, non-twin wait bound, and non-twin exit
wait lower bound checks all passed.

    slab            roots    no-twin power/near/log/sqrt    minimum K of near no-twin
    10000..20000     1667      0 / 67 / 0 / 866              11
    100000..200000  16667      0 / 152 / 6 / 7076            12
    500000..1000000 83333      0 / 369 / 0 / 31304           21

For the near mode: 2,867,008 events total (24853+369599+2472556).
Unlike the longer-window audit, 588 near crossings are genuinely
non-twin throughout their visited pre-offsets. The minimum support
among those is 11,12,21 in the respective slabs. For the bare sqrt
mode, minimum support among non-twin crossings is 1 in every slab;
this is a finite counterexample to an unrestricted assertion that
even one label is enough at D=ceil(sqrt X). It is not a counterexample
to the sufficiently large constant L_K criterion.

With delta=.1, near-mode non-twin STARTS satisfying old cardinality
criterion: 57,1209,4722; all reach a twin before exit in these samples.
Diagnostic relaxed counts using the NEW X^(1/8) low threshold and
<=3 significant labels across ALL high scales: 426,2811,16432.
These counts do not test the exact asymptotic split H_mid/H_near
hypothesis, and are not estimates of natural densities.

At R=10000,100000,500000, near ambient D=617,2233,5397.
Maximum C*log^2(2+min(p,D/p))/D in T<=p<=sqrt(R)*sqrt(L)
was 6.113,5.531,5.365. Far-tail max C*sqrt(L)/D was
0.854,0.681,0.721. These finite ratios do not establish a universal
constant or an effective threshold.

## 5. Remaining problem

Previous reset-chain CRT construction still has O(log X) gain for
its chosen lifts. Near-square-root length reduces the gap but does
not bridge it. The new fixed-K criterion suggests searching for
short exact reset words with one or more labels of order sqrt(X),
possibly many repetitions of a small support, and bounded interval
CRT screening. Under finite twins any such crossing needs total
support diversity or significant near-label diversity as above.
A growing-scale existence argument is still missing. No canonical
Lean files or other branches changed.
