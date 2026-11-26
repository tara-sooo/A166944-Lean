# Primorial compression, rough flux localization and a third logarithmic saving

2026-11-26 JST. Continuation of 6c74a04ee4860ea95e34eab81c59a9b5d0e537bc.
Paper deductions and executed finite audit, not Lean verified. Twin infinitude remains open.

## 1. Compress all small-label runs

Keep the common-boundary setup: R large integer, M=R/12+O(1) seeds
X in [R,3R/2], 6|X, reset (X,X/2+3), stop at first U>=2R.
Write B(u) for offset traffic, F_p(u) for mass selecting label p,
q(u)=min(lpf(u-1),lpf(u+1)), K for twin-free exits. All pre-offsets
are even and <2R. The physical gain of each whole path is <3R
since U<=2u<4R at the final event and X>=R.

For z>=3 let P=2 product of odd primes <=z. A p<=z event from u
cannot strictly cross a multiple J of P: J-u is positive even,
congruent to either 1 or -1 mod p, hence >=p-1. At J no such label
is eligible. Therefore any consecutive run of p<=z events gains
at most P in offset, and its sum of waits is <=3P, since
w<=2p<=3(p-1). A partial terminal run satisfies the same bound.
This uses no phase or merger estimates.

For a twin-free path let J_z count events p>z. Its time demand is
at least R/4-3 by the envelope, and each larger event waits at most
2sqrt(2R+1), as in the preceding note. Consequently

    R/4-3 <= 3P(J_z+1)+2sqrt(2R+1) J_z.

Whenever P=o(sqrt R), this implies
J_z >= (1/(8sqrt 2)-o(1))sqrt R. In particular z may tend to infinity
with R, e.g. choose P<=R^(1/4) by the elementary Chebyshev bound on
the product of primes. The number of events p>100sqrt R is at most
3R/(100sqrt R-1), by total gain. Thus every twin-free path has
at least c sqrt R events with z<p<=100sqrt R for large R, where
c>0 is absolute. If J_mid denotes total origin-weighted traffic
in that label band, K<<J_mid/sqrt R. In particular
J_mid=o(R^(3/2)) along an unbounded sequence suffices for twin
infinitude. This ignores all small-label events, even if numerous,
and also all very large labels. No bound of this order on J_mid
is proved.

## 2. Stronger arithmetic supply via a two-form sieve

For any fixed a>0, on even non-twin R<=u<2R define

    H_a=sum q(u)^a.

The preceding elementary semiprime argument gave
H_a << R^(1+a/2)/log^2 R. The additional condition that BOTH
neighbors avoid factors less than q(u) gives a further log:

    H_a <<_a R^(1+a/2)/log^3 R.

Proof. Put Y=2R+1. The part q<=Y^(1/3) contributes
O(Y^(1+a/3)), negligible. For the rest select a composite
neighbor n=pk, p=lpf(n)>=q>Y^(1/3), so k is prime, p<=k<=Y/p,
and the other neighbor is pk+/-2. Both k and pk+/-2 have no
odd prime factor below q.

Partition q into dyadic ranges [T,2T) with T=sqrt(Y)/2^(j+1),
j>=0 (include the endpoint sqrt(Y) in the first band),
retaining q>Y^(1/3). All such T>=Y^(1/3)/2. For fixed prime
p in [T,sqrt(Y)], use the explicit two-form Selberg upper sieve
in research/2026-11-26-min-primorial-record-displacement-and-supply.md
section 3. Its proof works for interval length N=floor(Y/p),
cutoff D=floor(T^(1/10)), p>D: two distinct forbidden residues
mod each odd sieve prime, main term O(N/log^2 T), error O(D^6).
Indeed N>=sqrt(Y) and D^6<=Y^(3/10), so the error is absorbed.
All constants are uniform, and log T is comparable to log Y.
The count of possible k for each sign is O(Y/(p log^2 Y)).
Summing over p, Chebyshev on each dyadic prime band gives
sum_(T<=p<=sqrt(Y))1/p << (j+1)/log Y (the first band and
its endpoint included). Hence the number of offsets in the
q band is O(Y(j+1)/log^3 Y). Multiplying by (2T)^a and summing
the convergent series sum_(j>=0)(j+1)2^(-aj) proves the claim.
Composite neighbor choice and sign can only overcount by summing.
No twin-prime asymptotic or lower sieve is assumed. This is a
paper bound, not a numerical fit. It uses the two-form sieve;
the earlier log^2 elementary proof remains available.

## 3. Weighted and localized traffic targets

With E=sum_u B(u)^2, Bmax=max_u B(u), the preceding clock-demand
inequalities and improved H_1,H_2 now yield

    K/M << sqrt(E)/(R log^(3/2) R),
    K/M << Bmax/(sqrt R log^3 R).

Either E=o(R^2 log^3 R) or Bmax=o(sqrt R log^3 R)
along unbounded R suffices. Also define the weighted energy
E1=sum_(non-twin u) q(u) B(u)^2. Weighted Cauchy-Schwarz
gives (sum_non-twin B q)^2 <= E1 H_1, so

    K/M << sqrt(E1)/(R^(5/4) log^(3/2) R).

Thus E1=o(R^(5/2) log^3 R) is sufficient; it permits much more
traffic at small q than at large q. For all these inequalities,
restricting B to origins that eventually have twin-free exits
is valid but not a usable bound without controlling those origins.

A different localization uses the compression in section 1 to
charge each small run to the following event p>z, or a final
terminal allowance 3P. Assume P=o(R), set L=300P, and let J_I
be total traffic of non-twin events z<p<=L. A twin-free origin
has demand R/4-3, bounded above by 3P plus the sum of
2q+3P over its events p>z. For p>L and q<p/100,

    2q+3P < 3p/100 <= (9/200)(p-1).

Summing such inefficient events costs less than 27R/200
per origin, since total gain <3R. They can be absorbed into
the demand lower bound, leaving at least R/10 for sufficiently
large R. The remaining events are intermediate (z<p<=L), costing
<=603P per event, or efficient large (p>L and q>=p/100>3P),
costing <=3q. Summing over K origins, then enlarging to all
origins on non-twin pre-offsets, yields

    K R/10 <= 603P J_I + 3 sum_(non-twin u, q>3P) B(u)q(u).

This proves a two-part sufficient condition:
P J_I=o(R^2) and sum_(non-twin q>3P) Bq=o(R^2) on the same
unbounded sequence. The latter can use E restricted to q>3P
and H_2 above. No uniform bound on small-q traffic itself is
needed; very large inefficient labels need no traffic bound
at all. Both remaining bounds are open. This localization is
not a proof of short crossings.

## 4. Exact offset-only comparator

As a separate experiment, consider the deterministic arithmetic
map u -> u+q(u)-1 with no clock phase. It is NOT asserted to be
a MIN trajectory or to dominate MIN. At a non-twin offset its
gain is <=sqrt(2R+1)-1; under finite twins it takes Omega(sqrt R)
events per common-boundary crossing. Hence an unbounded sequence
of short crossings would also suffice for twin infinitude in this
model. Its offset flow recurrence is simpler:
B(u)=seed injection + sum B(x) over x=u-p+1 where p divides
u or u+2 and q(x)=p. The same primorial compression applies,
but no asymptotic traffic bound has been established for it.

## 5. Executed audit

Source research/min_simple_rough_flux_audit.py at
118328f542405ac0536534fbeffdef64acbf28dd, Git blob
3f1e6b6e0b259a68566cbb842a9a29a6e6a37b13, matches executed local source.
Stdlib and inherited min_simple_crossing_audit.py. Run:
    python research/min_simple_rough_flux_audit.py 1000 10000 100000 1000000

Exact MIN graph counts agree with the preceding audit. All cut
fluxes (on the common slab after injection), small-label edge
barriers, mass-weighted pending small-run wait bounds for z=7,
total small-run charge, and weighted Cauchy-Schwarz checks passed.
All seeds hit a twin, so no twin-free demand case observed.
Paper asymptotic bounds are not certified by these finite checks.

    R        M     non-twin E1    high-label event visits p>7
    1000     84          23674         232
    10000    834       2754862        4482
    100000   8334    145222686       63499
    1000000  83334  7560987149      977543

At R=1000000, non-twin q>=256:
6704 ambient even offsets (1.3408% of all 500000 even offsets),
77114 origin-event visits (3.00697% of non-twin visits),
weighted Bq=43029500; total non-twin Bq=77952797.
Exact bin values for q>=256:
    q lower   ambient count   visits    Bq         Bmax
    256       3408            40805     15235227   387
    512       2708            32462     23612036   360
    1024       588             3847      4182237   324
Sum Bq=43029500, i.e. 55.19943% of the non-twin weighted traffic.
Rare high-q events account for much of the weighted clock upper
bound, not necessarily of actual wait; this is a finite observation.

Offset-only greedy comparator, same seeds and exit:
    R        total visits    E         Bmax   twin hits
    1000           512       4280         19     84
    10000        12168       345566       65    834
    100000      166981       12724785    323   8334
    1000000    2542802       402106708   804  83334

Each greedy seed hits a twin in these ranges. No dominance or
asymptotic implication from the observed agreement is claimed.
The next open step is an upper bound on the true moderate-label
traffic or localized high-q energy, retaining actual clock choices.
