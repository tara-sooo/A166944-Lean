# Reset gain, explicit square-root certificates, and semiprime tubes

2026-11-26 JST. Continuation of 4c96ced58d6901a1aaa03697bf6c12d7d4136b8a.
Paper deductions using exact ordinary MIN clocks and the inherited
envelope; no asymptotic sieve is needed in sections 1--4.
Executed finite diagnostics. No Lean verification, novelty claim,
or proof of twin infinitude.

## 1. Exact reset-preserving events

Call an event special if its source u is divisible by 12, v=u/2+3,
p=1 mod 12 and w=(p-1)/2. The arrival is again divisible by 12 with
deficit 2v-u=6. At a special source v is odd, w is even, so the
firing is necessarily odd and p divides u+1. Conversely, for a
prime p=1 mod 12 dividing u+1, its candidate odd-clock wait is
(p-1)/2 (whether or not it wins). This follows from
(u+1)/p=1 mod 4 and the clock n=p+2 mod 2p.

**Non-twin label cap.** At every non-twin special event p<=sqrt(u+1).
Suppose p>sqrt(u+1), write u+1=pm with 1<=m<p and m=1 mod 12.
If m=1, then p=u+1 and w=u/2, incompatible with the other
neighbor's composite-factor clock w<=2 sqrt(u-1) for u>=24;
u=12 is a twin center. If m>1 is prime, its short odd clock
wait (m-1)/2 wins. If m is composite it has a prime factor
q<=sqrt(m)<sqrt(p) and a clock within 2q ticks. For p>=37,
2 sqrt(p)<(p-1)/2. The only smaller prime 1 mod 12 is 13
and then 1<=m<13 with m=1 mod 12 forces m=1. Contradiction.
The cap does not assume that the special event is the first event
of the orbit, or that other preceding events are special.

**Reuse spacing.** Any two special sources x<y with the same
label p satisfy x=y=-1 mod p and x=y=0 mod 12. Hence y-x
is a positive multiple of 12p. This holds across intervening
arbitrary ordinary MIN events. In a half-open interval of width D,
there are at most D/(12p)+1 such events with label p on one path.

## 2. Explicit mixed-path crossing certificate

Start at a reset X divisible by 12, and stop at the first arrival
U>=X+D, including that final event. Assume every source is non-twin.
Let P be the distinct labels of SPECIAL events only, K=|P|,
and B the sum of gains (p-1) of all other events. All pre-offsets
are in [X,X+D). By section 1,

    G_special <= sum_(p in P) (p-1)*(D/(12p)+1)
              <= K D/12 + K sqrt(X+D+1).

Since total gain is at least D,

    (12-K)D - 12B <= 12K sqrt(X+D+1).                  (1)

Thus any actual crossing violating (1) contains a twin center.
This is an explicit finite sufficient condition, with no unknown
sieve constants, no restriction on the number or labels of the
other events, and no assumptions about merger mass. The other
events' actual gain matters; their wait and frequency need not
be controlled. For a fixed K0<=11, rho>=0 with K0/12+rho<1,
and fixed C>K0/(1-K0/12-rho), let D=ceil(C sqrt X).
If K<=K0 and B<=rho D along an unbounded sequence of resets,
(1) fails for all sufficiently large members and implies twin
infinitude. For example K0=2, rho=1/4, C=4 works asymptotically.
The unbounded supply is open.

When every event is special, take rho=0: the sufficient constant
is C>12K0/(12-K0), K0<=11. For K0=1 or 2 one can sharpen:
adjacent repeats are impossible since gain p-1<12p.
A word on two labels must alternate, and a triple p,r,p requires
p+r-2 divisible by 12p, hence r>=11p+2. Four alternating events
would also require p>=11r+2, impossible. A non-twin all-special
crossing on two labels therefore has at most three events.
Two events contribute <=2 sqrt(X+D+1); a three-event word
p,r,p contributes <=(13/11) sqrt(X+D+1).
So C>2 suffices for K0=2 and C>1 for K0=1.
More generally if the K labels of an all-special word are in
[a,b] and (K-1)b<11a, a first repeated label p would require
at least 11p+1 gain after its first event, whereas at most K-1
other distinct labels intervene. Hence no repeats; a non-twin
crossing then has total gain <=K sqrt(X+D+1).

## 3. Exact near-scale special-event factor test

Let p=1 mod 12 be a proper prime divisor of u+1 at a reset,
and assume (p-1)^3>64(u+1). If its short clock wins, every odd
prime factor of either neighbor is >=(p-1)/4 (each competing
clock fires in <=2q ticks). Three factors counted with
multiplicity would exceed u+1. Thus u+1=pm with m prime,
m=1 mod 12 and m>=p by the cap; u-1 is prime or semiprime.

In this domain the special event with label p wins if and only if:

* u+1=pm with p<=m and m prime, m=1 mod 12; and
* either u-1 is prime, or u-1=rs with r,s primes,
  r=1 mod 4, s=3 mod 4, r>p+6 and 3s>p+6.

Proof of sufficiency and the sharp inequalities: the cofactor m
has the same short-clock type, so its wait is not smaller.
For u=0 mod 12, a minus-side prime q=1 mod 4 has candidate
wait (q-7)/2 for q>=13; a prime q=3 mod 4 has wait (3q-7)/2.
In the semiprime case the factors have opposite classes modulo 4.
The candidate inequalities above make r>=13, and s>=7
(small cases cannot meet 3s>p+6 under the stated p domain;
q=3 never divides u-1). The two minus clock waits must strictly
exceed (p-1)/2: the firing parity differs, so they cannot tie.
A small r=5 would instead have wait 9, but the necessary
roughness bound and (p-1)^3>64(u+1) exclude it in a winning
case. More explicitly, the domain with p proper forces
u+1>=5p, hence p>=37, and if p=37 the inequality fails
for any composite neighbor containing 5 that could compete
because w=18>10. For any p>=37, w>10, excluding 5.
If u-1 is prime it is 3 mod 4 and its long clock is later
than p's short clock. These comparisons exhaust the candidates.
No assumption of primality beyond the explicitly stated factors.
The domain includes p>=eta sqrt(u) for every fixed eta>0
and sufficiently large u.

If two consecutive special events both meet this large-label
domain, write the successive plus neighbors as pm and rn.
The offset displacement p-1 gives

    p(m+1)-rn=1.                                    (2)

Here p,m,r,n are prime and all 1 mod 12; r!=p by reuse spacing.
For fixed p,r, equation (2) fixes m=p^(-1)-1 mod r, and
m=1 mod 12. Thus all integer roots u=pm-1 for this pair occupy
one class modulo 12pr. In a slab [R,2R) with p,r>=eta sqrt(R),
there are at most 1+R/(12pr)=O_eta(1) candidates. One must still
test cofactor primality and the opposite-neighbor comparisons.
This is a bounded-scale parametrization, not an assertion
that such prime quadruples exist infinitely often.

## 4. Balanced semiprime tube obstruction

Suppose p,m,r,n from (2) all lie within B of an integer h>0.
Write them as h plus errors of absolute value <=B. Since
r+n-p-m is divisible by 12,

    rn-pm = h*(r+n-p-m) + error, |error|<=2B^2.

On the other hand rn-pm=p-1=h+(p-h)-1.
The distance of h to the nearest multiple of 12h is h, so

    h <= 2B^2+B+1.                                  (3)

In particular two consecutive near-square special events
cannot both have their four factors in a common band of
width o(sqrt(h)) about h~sqrt(u). The excluded scale in
the prime factors is o(u^(1/4)), not o(sqrt(u)).
This rules out an especially balanced candidate construction,
but not arbitrary semiprime pairs.

More generally take fixed positive integers a,b with 12 not
dividing a, and suppose p,r are within B of ah, m,n within
B of bh. The same expansion has linear coefficient
b(r-p)+a(n-m) divisible by 12. The distance of ah to 12h Z
is >=h, so (3) still holds. Thus a fixed rational aspect tube
of width o(sqrt(h)) cannot support two consecutive events.
No claim for a moving tube center or wide ratio band.

## 5. Executed finite audits

Source 1: research/min_local_reset_band_audit.mjs,
commit e7b29704841a511c10f7e9bd3cc5432d9956e6e8,
blob a37adc8d27baadbd62c16d8d9835f255c8ac6ca1.
Run: node research/min_local_reset_band_audit.mjs 2000000.
Executed as ECMAScript in the research runtime and re-executed
after fetching the exact committed source. No Node process or
Lean process invoked here.

All 166666 positive multiples of 12 up to 2,000,000:
20769 first special events, of which 13269 non-twin;
415 non-twin first special events with p>=sqrt(X)/2.
26345 proper large candidate labels satisfying the section 3
threshold checked against actual modular first-clock selection:
485 match the factor test, 25860 fail it, no discrepancies.
Of the 485, 370 have a prime opposite neighbor and 115 a
semiprime opposite neighbor. All 26345 source/candidate pairs
are non-twin. 126 literal GCD tick controls.
For every root, follow consecutive NON-TWIN special events
until the first non-special event, twin center, or doubling.
13881 total prefix event incidences, 7 repeated-label pairs,
all satisfy the cap and spacing. Prefix length histogram
0:153397, 1:12683, 2:562, 3:22, 4:2.
Example length four: X=798420, labels 13,241,61,13,
gain 324, support 3. Largest observed gain/sqrt(X) in these
prefixes 1.376644466 at X=1284120, labels 829,733,
gain 1560. The latter is the only adjacent pair in the
strict section 3 large domain found in this prefix scan:
829*1549=1284121, 733*1753=1284949, satisfying (2).
It is genuinely non-twin at both sources. These observed
maxima are not uniform bounds. Repeat spacing can be much
larger than the minimum 12p.

Source 2: research/min_local_mixed_reset_audit.mjs,
commit 38574e275443dad6adcab57ade2e0066987a03e9,
blob 3b9be0cd683b7d71458512ec652432b1198e5356.
Run: node research/min_local_mixed_reset_audit.mjs 1000000.
Executed and re-executed as above. All 83333 roots divisible
by 12, for C=4,8,12, using the ordinary full MIN with all
special/non-special events and final event included.
Qualification is the strict reverse of (1), K<=11,
implemented by checking positivity and squaring the inequality.

    C  event incidences  no-twin exits  qualified  qualified non-twin start
    4       2115555            4722          7749            3627
    8       2221369             323          8297            4176
    12      2226188               4          8313            4194

All 5049 non-twin exits satisfy (1); no qualified non-twin exit.
3184,3714,3732 qualified non-twin starts respectively have
positive non-special gain (mixed paths). Many favorable paths
qualify because their final event is already a twin event;
the finite diagnostic does not supply an independent construction.
Example X=396, C=4, D=80, labels 5,3,31,433,
first three non-special events give B=36, and the last event
starts at u=432 with v=219, a twin center and special source.
All envelope, gain, repeated-reset and special non-twin cap
checks passed. Counts across C overlap, not independent samples.

## 6. Remaining direction

The finite CRT construction of arbitrary reset chains remains
only logarithmic-scale for its chosen large lifts. Equation (2)
and the explicit competing-clock test now characterize a
bounded-scale pair of large special events using small cofactors
and a single modular inverse. Search for chains in broader
aspect bands or mixed paths returning to deficit 6, and use (1)
to quantify the allowed non-special gain. A proof of unbounded
supply meeting (1)'s strict reverse, or the previous wider support
conditions, is still absent. No canonical Lean target or sibling
branch was changed.
