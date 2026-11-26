# Negative MIN: short-relay pair CRT and polynomial support obstruction

2026-11-26 JST. Continuation of 91032193ccbc06c8c14c4de528c31f1729dc9994.
Compress low-label relays between high events. The spatial CRT of
two consecutive distinct high labels is stronger than an individual
rough-source sieve when the high support is small. Derive exact
time accounting with unrestricted long-relay exceptions, and a
polynomial support requirement for a separated low/high alphabet.
Paper deductions and executed finite diagnostics. No Lean
verification or twin-infinitude proof.

## 1. Two high labels separated by a relay

Use the forward orientation of negative MIN in the remaining
distance a=-u, so a decreases by p-1 on a selected odd prime p.
The results also apply to an inverse branch read forward.
Consider a contiguous block of actual completed events whose
sources lie in an interval I of length D contained in [R,2R).
All sources are assumed non-twin centers, so their minimum
eligible prime q(a)<=sqrt(2R+1), and their actual wait obeys

    w<=2 min(p,q(a))<=2 min(p,sqrt(2R+1)).

This holds for the first event even if the block starts partway
through a wait. Any final stationary tail is accounted separately.

Mark all events with label p>=T, T>=5, and let L be the number
of distinct marked labels in the block. Two consecutive marked
sources a,c, labels p,r, have

    c=a-p+1-E,
    a=e mod p, c=f mod r, e,f in {-1,+1},

where E>=0 is the even total gain of the intervening unmarked
relay. The signs indicate which neighbor is divisible by the
label. Thus

    a=e mod p,
    a=p-1+E+f mod r.                              (1)

If r=p then E=e+1-f mod p. The integer e+1-f belongs to
{-1,1,3}; for odd p>=5 and nonnegative even E, the smallest
possible E in any of these classes is at least p-1.
Hence any relay with E<=B<T-1 must join distinct high labels.
No clock-phase independence or bound on the number of relay
events is required.

For fixed ordered labels p!=r, fixed signs, and fixed E,
(1) puts a in ONE even residue class modulo 2pr. The count
of such sources in I is at most D/(2pr)+1 (or the integer
bound floor((D-1)/(2pr))+1 for integer interval length D).
Sources on a single monotone path are distinct. The first
high event of every pair with these data has total wait at
most

    2 min(p,sqrt(2R+1)) (D/(2pr)+1)
       <= D/r+2 sqrt(2R+1).                        (2)

The second high event need not have a rough source; the
spatial CRT is enough.

## 2. Exact decomposition with a variable relay cutoff

Let G_relay be the sum of the gains of all relays BETWEEN
consecutive marked events (exclude the initial and final
unmarked runs). Let W_low be the sum of waits of unmarked
events. Assign the first high event in each consecutive
marked pair to either W_short (E<=B) or W_long (E>B).
The last marked event has wait W_last, taken as zero if
there is no marked event. The exact event-wait decomposition is

    W = W_low+W_short+W_long+W_last.

Put M=floor(B/2)+1 and S=sqrt(2R+1). Summing (2) over
the M possible even gains, four sign choices and L(L-1)
ordered distinct pairs gives

    W_short <= 4M L(L-1)(D/T+2S).                  (3)

More precisely the same bound with the sum over p!=r of
D min(p,S)/(pr)+2 min(p,S) can be used, instead of the
uniform D/T+2S. For a fixed p and variable r, the main
term involves the harmonic sum of the actual high support.

Every long relay has integer gain at least B+1 if B is
an integer, so their number is at most G_relay/(B+1).
The preceding high wait is <=2S. Thus

    W_long <= 2S G_relay/(B+1),
    W_last <=2S.                                  (4)

Together these give the unrestricted block estimate

    W <= W_low+4M L(L-1)(D/T+2S)
                 +2S G_relay/(B+1)+2S.            (5)

The estimate is useful only if the unmarked waits and long
relays are controlled. In particular with T polynomial and
B small, the coefficient S/(B+1) can be large. Do not infer
that the short-pair saving alone controls the entire path.

## 3. Separated alphabet: polynomial diversity instead of logarithmic

Suppose all selected labels below T belong to a specified
finite set A0 of odd primes, and put

    Q0=2 prod_(p in A0)p.

Every maximal A0-only run has physical gain <Q0 (including
the possible final event of a run). This follows from the
decreasing-distance primorial wall: a jump cannot strictly
cross the preceding multiple of Q0, and at the wall none
of those labels is eligible. The actual waits in such a
run are <=3 times its gain, so they total <=3Q0.
This applies even in the full unrestricted system when
the observed run contains only A0 labels; no assumption
about omitted competing clocks is needed.

If Q0<T-1, every between-mark relay is short for B=Q0.
If h is the number of high events, monotonicity gives
h<=D/(T-1)+1, counting the possible last event whose
arrival lies outside I. Thus

    W_low<=3Q0(h+1)<=3Q0(D/(T-1)+2).

Combine with (3)-(4), with M=floor(Q0/2)+1:

    W <= 3Q0(D/(T-1)+2)
       +4(floor(Q0/2)+1)L(L-1)(D/T+2S)+2S.         (6)

Take D=R and T=R^theta for fixed 0<theta<=1/2.
Assume Q0=o(T), and W>=eta R for fixed eta>0.
Then the first term is o(R) and the last is o(R).
Since D/T+2S=O(R/T), (6) forces

    L(L-1) >>_eta T/(Q0+1).

In particular

    L >>_eta sqrt(T/(Q0+1)).                        (7)

For fixed A0, the necessary number of distinct high labels
is Omega(R^(theta/2)), and for Q0=R^o(1) it is at least
R^(theta/2-o(1)). This is a polynomial-scale support
requirement, substantially stronger than the earlier
logarithmic per-label capacity, but ONLY under the
separated-alphabet hypothesis. The new strength comes
from a product modulus pr, not from an upper sieve.

For a shorter slab D>>sqrt R, the same argument with
W>=eta D, Q0=o(T), and Q0=o(D) gives

    (Q0+1)L(L-1) >>_eta min(T,D/sqrt R).             (8)

All statements concern one actual path. They do not bound
ensemble origin multiplicity. Under finite twins the
non-twin source assumption is automatic at sufficiently
large offsets, but the separated-support condition and a
long block in the relevant slab have NOT been established.

## 4. Four-form sieve survives a short relay

If the first and second marked sources a,c are both z-rough,
p>z, a=pm+e, then the four forms

    m, pm+2e, p(m-1)+e-E, p(m-1)+e-E+2

have no odd prime factor <=z. The last two are c-1,c+1.
Conversely, since p>z, their roughness is equivalent to the
roughness of a and c. For p>=5 and E>=0 all pairwise
determinants of the forms are nonzero: the roots
correspond to offsets 0, -2e/p, (p-e+E)/p,
(p-e+E-2)/p, and p+E>=5 excludes overlap.
Their bad-prime product is polynomial in R when a,c
lie in [R,2R), by p,E=O(R). At odd l<=z the forbidden
classes of a are

    -1,1,p+E-2,p+E (mod l).

In particular for z>=3 the total macro displacement
p-1+E is divisible by 6, even if p itself is 5 mod 6.
The same dimension-four upper sieve argument of
9103219 gives, for z>=R^epsilon and fixed p,E,

    C_macro(R,z;p,E)
        <<_epsilon R (loglog R/log R)^4,

uniformly for E>=0 with positive endpoints in the slab.
Here the weight is the first wait 2 min(p,q(a)), and
sources are non-twin. For p<=R^(3/4) use the four
forms on an interval of length R/p; for p>R^(3/4)
use the elementary source count and q(a)<=S as before.
Summing over E<=B gives the bound with a factor
floor(B/2)+1, not a bound uniform in all relay sizes.
This extends the paired rough capacity to short relays.
It is separate from (3), which requires the next
marked label but does not require either endpoint
to be polynomially rough. No asymptotic sieve claim
was numerically or formally verified in this turn.

## 5. Executed diagnostic

Source research/min_local_negative_short_relay_pair_audit.mjs,
commit 584c398fd722464e22d41fedd5e0dc670744ed62,
blob cb3502f07234313912f29270b5f0801826a2514a.
Executed as ECMAScript in the research runtime, fetched at
the exact commit and re-executed with identical output.
Reproduce using
node research/min_local_negative_short_relay_pair_audit.mjs
No separate Node or Lean invocation.

Four ordinary canonical controls, sparse seeds in slabs
R=10000,30000,100000,180000, T=17,31,53,101,
B=10,14,24,48 respectively. Trim at noncompleted final
negative-time waits and any twin source. Three additional
finite-support restrictions with A0={3,5}, {3,5,7}, {3,5}
and explicit high sets. In those controls only contiguous
blocks agreeing event-for-event with the unrestricted
winner and wait and having non-twin sources are tested
against the unrestricted bounds. This avoids applying
the unrestricted minimum-factor wait bound to an arbitrary
restricted map.

    roots (ordinary)                 1619
    events (ordinary)               39444
    roots (restriction controls)    23334
    events (restriction controls)   37298
    total tested contiguous blocks  15489
    consecutive high pairs           2329
    short relays                     1232
    long relays                      1097
    equal consecutive high labels      22
    equal labels with short relay       0
    exact short-pair CRT checks       1232
    fixed-key capacity checks         1232
    bounded-low-support wall checks  13937
    rough-endpoint macro form checks  1033

All assertions passed. The fixed-key capacity checks
explicitly group observed source counts by p,r,E,e,f,
check their CRT spacing bound and total wait, then check
(3)-(5) for each block. The wall controls verify
W_low<=3Q0(h+1) and the gain bound. Only the last finite
restriction control has Q0<T-1 with B=Q0 (Q0=30,T=101);
the other two have B<Q0 and cannot certify the general
no-long-relay conclusion from Q0 alone. All sampled
restriction relays happen to be short. The rough-macro
checks verify the forward four-form implication at z=7,
not an asymptotic count. No numerical evidence for
the separated-support hypothesis on all long trajectories
is claimed.

## 6. Remaining target

The spatial pair argument gives a stronger conditional
support obstruction than a per-label sieve, including
mixed endpoints and bounded relays. It does not bound
the actual high support of a hypothetical long canonical
reverse branch. To use it for twin infinitude one needs
a mechanism forcing a sufficiently sparse high support
and small intermediate relay cost, or a way to control
the long-relay and low-wait terms in (5) without those
hypotheses. No general extinction theorem or unbounded
zero-phase last-label theorem. No proof of twin infinitude
or Lean verification; no changes to canonical Lean targets
or sibling branches.
