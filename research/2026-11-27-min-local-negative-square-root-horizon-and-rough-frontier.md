# Negative MIN: square-root horizon and rough-frontier excess

2026-11-27 JST. Continuation of 4649be4e2ec418f4f89e914632234642179ac81b.
Independently check the user's supplied square-root and near-square-root
research proposal. Derive an endpoint-mass criterion with a weaker energy
requirement, a common-height first-passage description of the successful
cohort, and short-horizon physical-key capacity bounds for both high
wait and high gain. Paper deductions and finite audit; no new lower
bound on near-square-root rough centers and no Lean verification.

## 1. Square-root horizon

For canonical A in [R,2R], 6|A, take elapsed horizon T=o(R).
By nonnegative height, G_T<=2T+6, so for large R all distances
stay above A/2 and the negative-clock cutoff does not intervene.
Let a_T=A-G_T, W_T be completed waits, I_T=T-W_T.
The universal mod-30 bound (2021e5a) gives W_T<=9G_T/4+8.
Put S=sqrt(2R+1). At a non-twin endpoint I_T<next wait<=2S.
Thus G_T >= (4/9)(T-2S-8) whenever the endpoint is not a twin.
A twin reached in this horizon remains stationary through the
horizon: its preceding plus clock is 3-a, and the next minus
clock is zero; arrival is >=3-A/2>3-a. Therefore:
* If sqrt(R)=o(T) and T=o(R), liminf G_T/T<4/9 on
  unbounded roots implies twin infinitude.
* If T=ceil(c S), fixed c>2, the threshold is
  (4/9)(1-2/c); for c=8 it is 1/3.
Both sufficient conditions also follow from twin infinitude
when one is free to choose unbounded slabs containing twin
canonical roots, since their G_T=0. An average saving suffices
for existence but is not necessary for twin infinitude.
For c=8 an average strictly below 1/3 implies a positive
proportion of twin endpoints (same idle-mass argument as 4649be4).
A single-root square-root witness is simpler than this average.

## 2. Non-twin rough frontier upper bound

Let B>0 be fixed and K=floor(sqrt R/(log R)^B).
Define rough centers a even in [R-O(sqrt R),2R] by
P^-(a-1), P^-(a+1)>K. These centers are multiples of six
for large R. If an endpoint has I_T>2K, it is rough.
Indeed every odd prime <=K dividing either neighbor would
have fired in at most 2K ticks.

Since K^3>2R+1 for large R, both neighbors have at most
two prime factors counted with multiplicity. Every non-twin
rough center has one composite side qr, q<=r primes, with
K<q<=S, and the other side qr+/-2 is K-rough.
This includes squares and the case both sides are composite.
For fixed q and choice of side, the parameter r ranges over
an interval contained in [1,(2R+1)/q] of length O(R/q).
Sift r and qr+/-2 by odd primes up to z=(R/q)^epsilon,
with fixed sufficiently small epsilon>0. Then z<K, z<q,
and r>=q>z. For each odd prime ell<=z the two prohibited
residues are distinct since ell does not divide 2q.
The uniform two-dimensional upper sieve gives
O(R/(q log^2 R)) values. For instance use the standard
fundamental lemma already referenced in 74a6796 at level
sqrt(R/q), CRT remainder <=2^omega(d), summed remainder
O(sqrt(R/q) log(R/q)) absorbed in the main upper bound.
The argument does not assume qr+/-2 is prime.

By Chebyshev prime counting and dyadic subdivision of (K,S],
sum 1/q=O_B(loglog R/log R). Summing the above bounds
over q and sides yields

    # non-twin rough centers <= O_B(R loglog R/log^3 R). (1)

No lower sieve at cutoff K is asserted. In particular a
lower bound of order R/log^(5/2) R for distinct rough
endpoints is more than sufficient, but not necessary.
Any lower bound omega(R loglog R/log^3 R) suffices.
The same order with an unspecified implicit positive
constant is insufficient without comparing constants.

The analogous count for general polynomial K=R^theta
with 1/3<theta<1/2 is O_theta(R/log^2 R), not a log
saving. The shrinking relative log-width near sqrt R
is the source of the gain in (1).

## 3. Improve the successful-cohort energy target

For any selected set of roots with I_T>2K, write N_s
for its size, m_a for endpoint multiplicity and
C_s=sum m_a^2. Then distinct endpoint count D_s>=N_s^2/C_s.
By (1), under no twins in the endpoint interval,

    C_s/N_s >>_B N_s log^3 R/(R loglog R).         (2)

The user's suggested pair N_s>>R/log^2 R,
C_s/N_s=o(log R/loglog R) is sufficient. But if one
obtains N_s>>R instead, the permitted energy is much
larger:

    C_s/N_s=o(log^3 R/loglog R).                   (3)

In particular O(log^2 R) energy per successful root
suffices in that case.

To connect the gain goal to this stronger mass scale,
take T=4K and fix 0<g<2/9. Any root with G_T<=gT
has I_T>=T-(9/4)gT-8>2K for large R.
If E G_T/T <= g-epsilon for some fixed epsilon>0,
Markov gives at least epsilon/g of the roots with
G_T<=gT. Apply (3) only to that low-gain subset, not
to the whole cohort. Equivalently any constant mean
saving below 2/9 at T=4K, plus the selected energy
bound (3), suffices for twin infinitude. The mean
saving itself at sub-square-root time does not imply
twin infinitude without a further constraint.

There is also a direct displacement cap avoiding
energy: if selected successful roots have G_T<=L,
each endpoint a can be reached only by distinct roots
A in [a,a+L], spaced six apart. Thus

    m_a<=floor(L/6)+1,
    N_s(non-twin)<=O_B((L+1)R loglog R/log^3 R).    (4)

For example, with N_s>>R/log^2 R and L=o(log R/loglog R),
no energy estimate is necessary. If N_s>>R one may
allow L=o(log^3 R/loglog R). These are conditional
criteria, not demonstrated small-gain populations.

## 4. Common-height section for selected idle mass

Endpoint equality at different elapsed retirements
need not generally imply actual coalescence before
retirement. For the low-gain cohort in section 3,
there is a useful exact common section.

Write actual height h=a/2+n and note that a root's
last arrival has height 3+W_T-G_T/2, whereas its
retirement has height 3+T-G_T/2. For all roots with
G_T<=L, W_T<=9L/4+8. Set the integer
H=floor(3+T-L/2). If T>11L/4+9, then H exceeds
every height prior to or at the last arrival:
before that arrival the elapsed time is <=W_T
and height<=3+W_T; this is strictly below H.
All roots reach H during their final idle segment
because their retirement height is >=H.
This applies to L=floor(gT), g<2/9, at T=4K.
The first hitting of H occurs at the absolute time

    n=H-a_T/2.

Thus two selected roots with the same endpoint a_T
actually share the same physical state at their
first H crossing, while both are still in their own
horizons. They have coalesced by that time, and the
selected endpoint energy equals first-passage energy
at this height section. One can study this energy
without continuing all roots to the very late common
terminal time of 4649be4. At this section every
selected endpoint is rough by the full idle inequality;
first height crossing alone need not imply roughness.

## 5. Diagonal short-horizon capacity and high gain

Every physical firing key (a,n) completed within
some root's own T horizon lies in

    R-2T-6 <= a <= 2R,
    1 <= a/2+n <= T+3.

The second condition is on the height BEFORE the
jump, by h=3+t-G_previous/2. The height-local clock
formula of 0116e3e bounds its label by 2T+7.
Thus for fixed p and side e, a lies in one even
class mod 2p (O(R/p) positions for T=o(R)).
For each such a, n lies in one class mod 2p AND
in an interval of length T+2, so there are
O(1+T/p)=O(T/p) possible clocks, since p<=2T+7.

This is sharper than the previous rectangular
space-time count with time length O(R): the
possible keys lie in a diagonal strip of width T.
For T->infinity and T<=R^(3/5), the total
unweighted gain capacity of distinct high keys is

    B_Y=sum_(keys p>=Y)(p-1)
        << R T sum_(Y<=p<=2T+7) 1/p.             (5)

The sum is over primes. If Y=T/(log T)^D for
fixed D>0, Chebyshev and dyadic summation give

    B_Y <<_D RT loglog T/log T.                   (6)

This bound needs no wait efficiency or roughness.
For each key let m_e be the number of roots that
complete it in their own horizons. Define C_share
as the number of ordered pairs of slab roots that
share at least one completed physical key, including
all diagonal pairs. This is a localized pair count,
not the full final cohort energy. It is at most the
full energy, and any such pair differs in initial
distance by <=2T+6. For each pair the sum of gains
over their shared keys is <=2T+6. Therefore

    sum_e (p_e-1)m_e^2 <= (2T+6) C_share.

Cauchy-Schwarz applied to (5) gives

    E G_(p>=Y) <<_D T sqrt(
         (C_share/N) loglog T/log T).            (7)

For the high gain at keys of multiplicity <=M
there is the independent lighter-mass bound

    E G_(p>=Y,m_e<=M)
          <<_D T M loglog T/log T.               (8)

In particular if C_share/N=o(log T/loglog T)
then the entire top band contributes o(T) gain.
Likewise the light-mass component contributes o(T)
under that condition on M, even if other keys have
huge multiplicities. This is a gain bound, unlike
the earlier efficient high-wait estimate.

The analogous short-horizon improvement of the
efficient high-wait estimate of 4649be4 follows
by replacing the time count O(R/p) by O(T/p).
For Y->infinity, delta=1/log^2 Y, inefficient
incidences w<delta(p-1) cost O(NT/log^2 Y)
in total. Efficient keys have the same necessary
roughness as before, with p<=2T+7 and
p<=1+2sqrt(2R+1)/delta because all completed
sources are non-twin (any twin reached is absorbing).
The spatial count O(R/(p log^2 p)) is uniform
by the same two-dimensional upper sieve.
Their unweighted wait capacity is O(RT/log^2 Y).
For efficient wait sum L_e and capacity b_e,
sum L_e^2/b_e<=T C_share, as follows by counting
ordered pairs and the total shared waiting of
the first root (at most T). Thus

    E W_(p>=Y)
       << T/log^2 Y + T sqrt(C_share/N)/log Y.

The light-key version is O(T(M+1)/log^2 Y).
These are unconditional component inequalities
at the actual short horizon. They do not bound
total gain below the square-root threshold; in
particular lower labels, heavy keys and the
generation of successful idle endpoints remain
the missing parts.

## 6. Executed audit

research/min_local_negative_sqrt_horizon_audit.mjs
commit 7b059feca37d102f204d8a1d66462167d7f84f4d,
blob ab01633224cfcf0861ecac53fea52af6e21517ea.
Executed as ECMAScript, then exact remote readback
and reexecution with identical output. No separate
Node or Lean invocation. Five slabs, B=1/2,
K=floor(sqrt(R)/sqrt(log R)), T=4K.
All A=6j in [R,2R]. Enumerate rough centers and
semiprime exceptions in [R-2T-6,2R] with exact
factorization, verify direct idle implication,
displacement and energy inequalities, shared
idle intervals for G<=floor(2T/9), physical key
strip and fixed-label capacity, and finite high
gain Cauchy inequalities. Also compute larger
T'=ceil(8sqrt(2R+1)) square-root witnesses.

    roots                       288671
    completed event checks     5899880
    rough center incidences      25130
    semiprime factor checks      14843
    fixed-label capacities        1442
    shared idle interval checks 13537
    selected root checks         96088
    high gain Cauchy controls       15

All assertions passed. The selected-cohort audit
checks actual common idle intervals; the specific
first-H section follows analytically above, rather
than from a separate first-hitting simulation.
The C_share asymptotic is a deduction, not a
measurement of C_share in the audit.

    R         K    idle roots  distinct  C_s/N_s   low-gain idle roots  low-gain C_s/N_s
    12000     35       954         191      7.83          535                 3.88
    48000     66      3939         583     12.76         2217                 5.79
    192000   125     16786        1832     20.48         9450                 8.96
    480000   191     45466        3984     27.83        25970                12.20
    1000000  269     98756        7608     33.21        57916                15.14

The selected subset here uses G<=floor(2T/9)
and independently I>2K, including the finite
additive-constant effect. At R=1000000 it has
7286 distinct endpoints, while the whole
containing rough frontier has 6383 non-twin
centers. Hence that finite slab alone passes
the endpoint excess test by exact counts.
The mean G_T/T at T=4K is .61999 for this slab;
the mean G_T'/T' at the larger square-root
horizon is .10800. These data do not give
unbounded sequences. The successful populations
can include already known actual twins.

## 7. Recommendation and remaining target

Replace linear horizon as primary goal by
T=ceil(8sqrt(2R+1)) or T/sqrt R->infinity slowly.
The near-square-root rough frontier is a second
route, with a joint gain/selected first-height
energy target at T=4K. The non-twin frontier
upper bound is proved at paper level using
standard upper sieve; the required lower bound
on distinct rough endpoints is not obtained.
The old lower sieve for fixed words still
cannot simply reach K near sqrt R. The short
diagonal capacity and selected energy describe
what needs controlling but do not establish the
needed mean gain or successful mass asymptotics.
No proof of twin infinitude, Lean verification,
or changes to canonical Lean targets/sibling branches.
