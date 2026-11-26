# Record-free crossing criterion and elementary deficit bounds

2026-11-26 JST. Independent branch from primorial-neighborhood at
4e4c38c5a406f3b7e33b0fc7fb99256823d3f17a. Paper deductions and executed
finite audit; no Lean verification, novelty claim, or proof of twin infinitude.
The approach drops first-record classification as a requirement.

## 1. Arbitrary reset and a record-free target

For every positive multiple X of 6 start the ordinary uncut offset MIN at
(u,v)=(X,X/2+3). Thus d=2v-u=6. The exact next event (w,p) is the
lexicographically first positive wait and odd prime label over p|u-1 with
v+w=0 mod 2p and p|u+1 with v+w=p+2 mod 2p.
Set U=u+p-1, V=v+w. The envelope u/2<=v<=u+1 is inherited:
at an even firing the positive defect 2V-u+1 is divisible by p, and at
an odd firing the odd defect 2V-u-5 is either positive or has absolute
value <=3 (in the latter case p=3); these give U<=2V.
A plus-side clock is active at u+3, which is strictly after v, so
V<=u+3<=U+1. Offsets strictly increase.

Let N(X) be the number of events through the first U>=2X. It is always
finite, even with no assumptions about twin primes. If none of the
pre-offsets is a twin center, a composite neighbor supplies an odd
prime divisor <=sqrt(u+1); its competing clock gives
w<=2sqrt(u+1)<=2sqrt(2v+1). Thus Phi(v)=sqrt(2v+1) increases by <2
at each event, since Phi(v+w)^2<=Phi(v)^2+4Phi(v).
At exit 2v>=u>=2X, so

    2N(X)>sqrt(2X+1)-sqrt(X+7).

Consequently infinitely many multiples of 6 with N(X)<=sqrt(X)/5
imply infinitely many twin pairs (the inequality contradicts twin-free
crossing for X>=10000). Conversely if X>=6 is itself a twin center,
the plus clock at X+3 wins over the minus clock 2(X-1), so N(X)=1.
Therefore the following are equivalent to twin infinitude:

    liminf_(X->infty,6|X) N(X)/sqrt(X) < (sqrt(2)-1)/2;
    liminf_(X->infty,6|X) N(X)/sqrt(X) = 0.

The same argument for a fixed crossing factor a>1 gives the lower bound
(sqrt(aX+1)-sqrt(X+7))/2 for a twin-free crossing to u>=aX.
The equivalence for a=2 is a shorter sufficient-condition proof, not
an estimate showing that any unbounded sequence of short crossings exists.
No primality restriction on the reset and no first-record classification
are needed. No claim that arbitrary seeds lie on the distinguished ray.

## 2. Elementary global deficit bound without any finite table

For each event write E=delta d-4 delta u=2w-5(p-1).
The bound w<=2p gives E<=5-p. The only positive case is p=3,w=6
with E=2 (all rewards are even). It has a short forced compensation:

- If p=3 is plus-side, then after firing u'=1 mod 3 and v'=5 mod 6.
  The very next tick has minus-side label 3, so E=-8.
- If p=3 is minus-side, then u'=0 mod 3, v'=0 mod 6.
  The next p is >=5, and its E is negative unless p=5,w=10.
  In that exceptional zero-reward case the next state has u''=1 mod 3,
  v''=4 mod 6, so the minus-3 clock forces a wait <=2.
  The next E<=-6 irrespective of the selected label.

These compensating blocks contain no further positive event and are
disjoint. A prefix may end before the last compensation, costing at most 2.
Summing E gives d<=8+4G, where G=u-X. This proof applies to all
envelope-valid deficit-6 resets X even >=6, not only canonical rays.
Using the earlier non-twin doubling necessary condition
d>=u-2sqrt(u-1)-2 gives 3G>=X-2sqrt(X+G-1)-10.
A non-doubling first label p>X/2+1 needs 3p<=u+1, hence G>X/2.
Thus for all sufficiently large X, G<=cX for fixed c<1/3 is sufficient
for a genuine twin first record. This improves the previous table-free
fraction 3/10 without an exhaustive calculation.

## 3. Tiny finite certificate

Retain only A={3,5,7}, Q=210, and reward
E=4 delta d-15 delta u=8w-19(p-1). For p>=11, E<=19-3p<=-14.
A restricted A-path cannot strictly cross a multiple of Q: if u<J
and p divides u+-1, the positive even distance J-u is >=p-1.
At J no A-label is eligible.

For even 0<=u<=Q, v mod Q, let F be the maximal nonnegative prefix
reward of the restricted A-only path, allowing an empty prefix.
F=0 when no event exists; otherwise
F(u,v)=max(0,E+F(u+p-1,(v+w) mod Q)).
The recurrence is acyclic in u. Every actual consecutive A-run is a
prefix of this restricted path (larger labels can preempt, not change
an A-selected event). The independently checked table yields
B=max F=14 and I=max F over X=0 mod12 reset residues=6.
The reset residues repeat under X->X+420.
Therefore an initial A-run contributes <=6, and each larger-label
event plus following A-run contributes <=-14+14=0.

    4(d-6)-15G<=6   for X=0 mod12.

This means d<=15G/4+15/2. The earlier false-double inequality implies
(11/4)G>=X-2sqrt(X+G-1)-19/2; the asymptotic sufficient fraction is
any fixed c<4/11. For example G<=X/3 is sufficient for X>=1000
(the necessary inequality would give X/12<=2sqrt(4X/3-1)+19/2,
false at 1000 and increasingly false thereafter).
Non-doubling first records again require G>X/2.
This certificate uses (106)(210)=22260 states, versus the inherited
450930480-state 18/5 certificate, with a slightly weaker threshold.
The record-free target in section 1 requires neither certificate.

## 4. New quantitative localization: avoid estimating whole merger basins

Suppose a reset X reaches its first twin center y after j events.
All j prior pre-offsets are non-twin; by the same potential argument
(including the j=0 case separately),

    y <= X+6+4j sqrt(X+7)+4j^2.

Thus for seeds X in [R,2R] that have short crossings N(X)<=k,
where k<=sqrt(R)/10 and R sufficiently large, a twin is encountered
before exit and j<k. Each particular first twin y can receive only
seeds in [y-L,y], L=6+4k sqrt(2R+7)+4k^2.
This is a geometric bound on origins, regardless of how many times
paths merge. Since X is a multiple of 6, at most floor(L/6)+1
such origins can reach one y. If M seeds in [R,2R] have short crossings,
the number of distinct twin centers in [R,2R+L] is at least
M/(floor(L/6)+1). In particular a fixed positive fraction of short
crossings with k=o(sqrt R) forces Omega(sqrt R/k) distinct twin centers
in that enlarged slab. A mean bound E[N]=o(sqrt R) implies a diverging
number of distinct twins there by Markov with k=o(sqrt R)
(for instance k=ceil(sqrt(E[N]*sqrt R))).
This is an elementary alternative to an exact global basin-size bound
for deducing many twins from short crossing counts. It is conditional:
it supplies no independent upper bound on the crossing-count mean.

## 5. Executed reproducible audit

Source research/min_simple_crossing_audit.py at
488fcaf3b92ffa7c2dde53704785381f180c9115, Git blob
f247c8d000a00cda96d34ffd8d0e82f6e25b40fe (matches executed local source).
Stdlib only. Run:
    python research/min_simple_crossing_audit.py 1000000

The small table was computed using modular clocks and every recurrence
entry checked against literal GCD ticks (separate event-selection oracle).
Result: 22260 states, B=14, I=6. A scan of every positive multiple of 6
up to 1000000 (166666 seeds), running to its own 2X exit:
4455612 events; zero crossings without a visited twin center; zero
violations of the envelope, elementary deficit bound, small certificate
on X=0 mod12, or non-twin per-event potential checks. Maximum observed
first-twin index 245 at X=701304. Selected dyadic seed slabs:

    slab inclusive lower/exclusive upper, count, mean N, max N, N<=sqrt(X)/5
    [65536,131072)     10923  19.7762  114  10485
    [131072,262144)    21845  24.7335  195  21330
    [262144,524288)    43691  26.4123  212  43414
    [524288,1000000]   79285  29.7841  246  79156

The last slab is truncated; samples are overlapping/merging
deterministic trajectories, not independent random trials. The shortest
crossing among non-twin starting seeds was 2 in these slabs. The
twin-free exit implication did not receive a negative-case trajectory
in this range. No asymptotic upper bound follows from the finite scan.

## 6. Remaining research target

Try proving even a positive fraction of short crossings on unbounded
slabs, or construct a deterministic unbounded subsequence with short
crossing counts. The geometric origin bound removes the need to prove
small global merger basins *after* short crossings are established.
The hard step is proving a short-crossing supply, not sharpening the
false-record certificate. A bounded fixed event count is not a viable
generic bound (see inherited all-reset-reachability). No Lean run or
claim of solving twin infinitude.
