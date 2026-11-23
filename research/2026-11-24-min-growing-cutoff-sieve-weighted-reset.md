# MIN growing-cutoff theorem, a uniform two-form sieve, and a weighted reset transfer

Date: 2026-11-24 JST. Branch: research/min-growing-cutoff-sieve-2026-11-24, based on Issue #3 at f210f10459cc4a9cd6e6f7e5ff84665a63da3cfe.

Status distinction:
- The finite low-only event arithmetic is encoded in research/min_growing_cutoff.lean. Kernel/CI status is tracked separately.
- The analytic sieve application below is a paper proof using Kevin Ford's published upper-bound sieve, not a Lean theorem.
- The weighted lift in Section 4 is a new paper corollary from two existing bounds. It is unconditional relative to the established deterministic MIN-wheel definitions and standard sieve theorems.
- The full source-weighted repeat bound R_y/(XB) < 9/224 remains open. No proof of twin-prime infinitude is claimed.

## 1. Exact finite reduction and the 9/224 threshold

Take X=2^k divisible by 4, odd M in [X,2X), s=M+2, C(s)=2M-2,
K(M)=floor((7M-1)/4), B=ceil(sqrt(7X)). Select at each first
parity-GCD nonunit event the smallest prime p<=B dividing the raw
parity-GCD, and update the even horizon C by p-1.

Let L=2 product_(3<=p<=y, p prime) p <= sqrt(B), with y maximal, so
L=o(B), y tends to infinity, and all low selected primes divide L.

At any even C0 let J be the least multiple of L that is at least C0.
Then J is even and C0<=J<C0+L. If p|L and p|C-1 or p|C+1,
the even-multiple barrier gives C+(p-1)<=J. Thus during any consecutive
LOW-only run, C never passes J and its total gain is <L.

For each selected p, the frozen prime clock has gap at most 2p.
Because p>=3, 2p<=3(p-1). Hence the elapsed time to the last
low-only event in such a run is <3L. The Lean file formalizes the
divisibility barrier, an inductively defined low-only trace, the
time/growth potential, and this <3L conclusion. The first-hit
prime-clock inequality is an explicit field of the trace.

If a source has H_y(M) selections p>y and its terminal is not a twin
pair, its total travel satisfies

  K(M)-s <= (H_y(M)+1) (2B+3L).                        (1)

The extra 2B in each block covers the wait to the next high-prime
event, or the final no-event tail. A terminal frozen for at least
2B steps would have both C-1,C+1 prime (because both are <B^2 and
any composite has a selected prime clock within 2B).

The exact dyadic travel sum is

  sum_(M odd in [X,2X)) (K(M)-s) = 9X^2/16 - 5X/4.   (2)

Let N_p(M) count selected occurrences, H_y=sum_M sum_(p>y) N_p(M),
F_y=sum_M sum_(p>y) 1_{N_p(M)>=1}, and
R_y=sum_M sum_(p>y) (N_p(M)-1)_+.
Then H_y=F_y+R_y, and F_y<=(X/2)pi(B)=o(XB).

From (1),(2), absence of a twin terminal implies

  9X^2-20X <= 16(2B+3L)(R_y+F_y+X/2).             (3)

Since B^2/X->7 and L/B->0, (3) forces

  liminf R_y/(XB) >= 9/224

on any unbounded sequence of twin-free dyadic windows. Conversely,

  liminf_(dyadic X) R_y/(XB) < 9/224

is sufficient for infinitely many twin primes, with the exact
finite-X certificate supplied by the reverse strict inequality of
(3). Each successful terminal yields a pair with smaller member at
least 2X-3, so increasing X forces distinct pairs.

The Lean arithmetic theorem finite_twin_of_budget records the exact
finite strict threshold, with the no-twin implication (3) as an
explicit premise. The no-twin premise has not yet been connected to
a fully formal MIN-wheel dynamics in Lean. Nor has the PNT/liminf
asymptotic step been Lean-checked.

## 2. A uniform two-linear-form sieve for the first top-band prime

First fix LOW7={3,5,7}. From each reset time n in an interval
I=[X+3,K(2X-1)] (length O(X)), start at

  C0(n) = 2n - delta(n), delta=0 at even n and 6 at odd n.

Consider reset times whose FIRST selected high prime p>=11 is in
[B/2,B]. For B sufficiently large, p>=37. The Issue #3
first-high-delay identity gives the first p-event time t with

  t-n >= (p-7)/2.

The finite LOW7-MIN ghost has exhausted its low events by elapsed
time 56. Thus the last low event to t contains a fixed-C quiet
interval of length at least (p-119)/2. Every small prime ell dividing
(C-1)(C+1) fires within 2ell steps. Consequently both neighbors
are free of prime divisors ell < (p-119)/4. For the sieve choose

  z = B^(1/100).

For sufficiently large B, z<(p-119)/4, so every ell in [11,z]
is excluded from (C-1)(C+1). It is unnecessary to prove that the
cofactor m below is prime to apply the sieve.

For r=n mod 210, the LOW7-only ghost has a deterministic final
gain E_r, with E_r <=32 (reset-origin slice), so

  C = 2n - delta(r) + E_r.

Fix p, r and side sigma∈{-1,+1} at the first high event.
The divisibility condition

  p | 2n - delta(r) + E_r + sigma

with n=r (mod 210) picks ONE residue of n modulo 210p
because gcd(210,p)=1. Write

  n = n0 + 210p j,
  m = (2n - delta(r) + E_r + sigma)/p = m0+420j.

The other neighbor is

  pm - 2sigma.

For every prime ell in [11,z], ell does not divide 420 or p, so
the two forms

  f1(j)=m0+420j,
  f2(j)=p(m0+420j)-2sigma

each exclude one residue modulo ell. These roots are DISTINCT:
f2-p*f1=-2sigma and ell is odd >=11. More strongly, the
two-form determinant is

  420*(p*m0-2sigma) - 420p*m0 = -840sigma,

which is independent of the moving prime p. All the local
singular factors are therefore uniform in p and r.

Let N be the number of possible consecutive j in I. Here
N ~ |I|/(210p), with N comparable to B, uniformly for
p∈[B/2,B]. For a squarefree d composed of primes [11,z],
the number of forbidden CRT classes is exactly 2^omega(d).
The residue count is

  A_d = N 2^omega(d)/d + O(2^omega(d)).

Kevin Ford, Sieve Methods (Spring 2023), Theorem 2.4, applies
with sieve density g(ell)=2/ell and dimension kappa=2. The
excluded primes <=7 cause only a universal constant in the
Euler product. Mertens gives

  V(z)=prod_(11<=ell<=z) (1-2/ell) << (log z)^(-2).

The total remainder is

  sum_(d<=z) |r_d| << sum_(d<=z)2^omega(d) << z log(2z).

Since N comparable to B and z=B^(1/100), this remainder is
o(N/(log B)^2). Therefore for FIXED (p,r,sigma),

  #{j satisfying all necessary roughness conditions}
       << X/(p(log B)^2).

Summing over the 210 residues, two signs, and all primes
p in [B/2,B], the elementary prime-counting upper bound gives

  sum_(B/2<=p<=B, p prime) 1/p << 1/log B,

hence

  T_top(X) :=
   #{n in I: first selected p>=11 lies in [B/2,B]}
     << X/(log B)^3.                               (4)

This is an unconditional paper theorem derived from the existing
LOW7-MIN finite ghost and first-high-delay lemma. The sieve
error bound and uniformity are written explicitly here; no
unproved distributional independence is used.

Reference: Kevin Ford, Sieve Methods (2023), §2.1 Theorem 2.4
and §2.2 upper-bound sieve, https://ford126.web.illinois.edu/sieve2023.pdf

For the growing cutoff y, replace 210 by L, 420 by 2L, and
n mod 210 by n mod L. The first p>=B/2 occurs after all
low-only events once B is large, because its clock delay is
>= (p-7)/2 >> 3L. For ell>y, ell<z, the two forms again exclude
two distinct residues modulo ell; for ell<=y, their value is
fixed along j. The product over y<ell<=z is

  << (log(2y)/log B)^2.

Since L<=sqrt B, the per-class j interval has length
comparable to X/(Lp) >= c sqrt B, while the same
O(z log z) remainder is negligible. Summation over L classes
and top p yields

  T_top,y(X) << X (log(2y))^2 / (log B)^3.        (5)

Using the prime number theorem for the primorial,
y=O(log B), so log(2y)=O(log log B).

## 3. New deterministic transfer from reset times to actual source weights

Let A_X be the set of distinct FIRST high selected reset atoms
v(n)=(n,2n) for even n and (n,2n-6) for odd n, reached by
canonical original MIN-wheel sources M before K(M). Put

  w_v = #{M: first high reset is v},
  S = sum_v w_v <= X/2.

All sources M_i feeding one v=(n,C_v) have partial gains

  G_i = C_v-(2M_i-2) >= 0.

For odd M_i in increasing order, G_i-G_(i+1)>=4. For
k=w_v sources this gives

  sum_(i=1)^k G_i >= 2k(k-1).

The first-reset fibres are disjoint, hence

  sum_v w_v^2 <= S + E_X/2,                     (6)

where E_X is the total partial growth to each source's first
high reset. Because each reset time rho<=K(M) and
C_rho<=2rho<=2K(M),

  G_i <= 2K(M_i)-(2M_i-2)
      <= (3M_i+3)/2
      < 3X+2,

and thus E_X < (X/2)(3X+2). Consequently

  sum_v w_v^2 <= (3/4)X^2 + O(X).               (7)

This estimate is unconditional and requires no control of Hpre.

Let T_X be the subset of reached reset atoms whose FIRST
subsequent selected high prime belongs to [B/2,B], when
the wheel is continued to the COMMON maximum Kmax.
As T_X lies among all possible reset-time starts,

  |T_X| <= T_top(X) << X/(log B)^3.

Cauchy-Schwarz applied to (6),(7) gives the new
SOURCE-WEIGHTED consequence

  sum_(v in T_X) w_v
    <= sqrt(|T_X| * sum_v w_v^2)
    << X^(3/2) / (log B)^(3/2)
    << X B / (log B)^(3/2) = o(XB).              (8)

This resolves the coalescence-weight problem for the
FIRST top-band high prime after an actual first reset.
The growing-cutoff version from (5) similarly yields

  sum_(v in T_X,y) w_v
    << X B log(2y)/(log B)^(3/2)
    = o(XB),                                    (9)

since log y=O(log log B). For each source this counts at
most ONE specified first-top event after its first reset,
not the full number of top-band events or all q returns.

Equation (8) is new in this public research branch:
the earlier unweighted first-top count and the existing
fibre L2 inequality were previously recorded separately.
Equation (9) is the natural growing-cutoff extension.

## 4. Zero, one, or multiple intermediate high primes in p-returns

Suppose a selected high prime p is selected again. Let m
intermediate selected high primes be q_1,...,q_m, and let E
be growth from low-only blocks in between.

After the first selected p, its clock cannot activate again
until the horizon gains at least p-1. Every low-only block
gains < L, so m=0 is impossible for p>L.

For m=1, there are two low-only blocks, so 0<=E<2L, and
the exact MIN return congruence (from Issue #3) is

  p | q-1+E-c,    c in {-1,+1,+3}.

Thus q is congruent to one of a bounded set of offsets
modulo p. If p∈[B/2,B] and p >> L, q<=B, then q lies
within O(L) of p or 2p. This restricts LABEL combinations,
but it does not bound the weight of actual sources with
a long prehistory reaching the same high event.

The m>=2 class remains the main obstruction. In
particular the existing exact canonical example M=97,289,
p=197 repeating after high donors 101,83,11 and low
gain 8, has total return gain 200=197+3.
No near-pair-only argument covers it.

The newly established (8),(9) are therefore a STRICTLY
LOCAL transfer: unweighted top-band first high events
after actual resets can be charged with total original
source mass o(XB). Source-weighted later high events and
all repeat owners R_y are not bounded.

## 5. Implementation and validation boundaries

- research/min_growing_cutoff.lean contains a standalone Lean
  deterministic LOW path invariant, a first/repeat split,
  a finite orbit-sum lemma and the exact strict threshold.
- .github/workflows/min-growing-cutoff.yml checks it against
  the pinned project Lean toolchain when CI runs.
- The full canonical MIN clock semantics, the exact dyadic
  travel identity, the standard sieve theorem, fibre-energy
  inequality and the asymptotic 9/224 implication are NOT
  yet present as an end-to-end Lean derivation.
- None of the arguments above proves the OPEN estimate
  liminf R_y/(XB)<9/224.


## 6. Source-weighted finite audit of the partial top-band estimate

The reproducible checker is [`min_weighted_first_top_audit.py`](min_weighted_first_top_audit.py).
For each canonical odd source, it reconstructs the actual smallest-selected-prime
parity clock and tracks the first reached high reset; on small X it crosschecks
the next clock event against a literal integer-by-integer gcd oracle.
For each possible reset time it independently scans the future first high
prime up to common Kmax. It checks the exact 9X²-20X travel identity,
H_y=F_y+R_y, the deterministic fibre energy
2(sum w²-S)≤E, and weighted Cauchy.

All reported counts are finite results. In these samples the growing-cutoff
selector y is still 3, L=6; in particular the repeat breakdown here
includes selected prime labels p>3, unlike previous fixed LOW7 scans.

| X | all reset times with first top | reached first-top atoms | source-weighted first top | first-reset sum w² | R_y, m=0 | R_y, m=1 | R_y, m≥2 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 256 | 29 | 0 | 0 | 143 | 1 | 134 | 186 |
| 1024 | 295 | 15 | 24 | 961 | 29 | 289 | 343 |
| 4096 | 580 | 26 | 54 | 5148 | 252 | 2681 | 5236 |
| 16384 | 1808 | 80 | 175 | 23017 | 1138 | 13262 | 33405 |
| 65536 | 5142 | 261 | 661 | 113988 | 5568 | 63683 | 179091 |

The last three repeat columns measure the number m of *intermediate
selected labels p>y* between consecutive selections of the same prime.
In the X=65536 window, m≥2 contributes 179091 of 248342 repeats,
about 72.1%. This numerically localizes the remaining multi-donor
issue without proving an asymptotic estimate.

Reproduce from the repository root:

```sh
python3 research/min_weighted_first_top_audit.py 256 1024 4096 16384 65536
```

The finite checks were run successfully in the session producing this note.
The manuscript's two-form upper-bound sieve and all claims in
sections 2–4 are paper-level; the Lean module isolates only the deterministic
local event inequalities and finite budget implication.
