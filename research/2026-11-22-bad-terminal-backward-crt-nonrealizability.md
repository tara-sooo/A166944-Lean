# A166944 — exact backward gcd sieve for BAD terminal candidates

2026-11-22 JST. **Status:** an exact elementary reverse-transition characterization, two short certificates excluding previously surviving locally BAD terminal configurations, and an infinite CRT-lifted family of analogous exclusions. Independent Python integer audit PASS. **No global Cap B proof, no twin-prime infinitude proof, no new Lean kernel compilation.**

This is a direct continuation of [the full-prefix CRT and terminal twin-input local witnesses](2026-11-22-full-history-clock-crt-and-twin-input-cutoff-sieve.md), [the terminal BAD first-hit dichotomy](2026-11-22-terminal-cutoff-factor-short-crossing-dichotomy.md), [the forward budgeted first-hit wheel](2026-11-22-budgeted-first-hit-crt-anti-resonance.md), and [the canonical GOOD genealogy limitations](2026-11-22-record-genealogy-quiet-parent-high-reuse.md).

Unlike the attempted global R_M recycling upper bound, the new method tests whether a prescribed BAD cutoff horizon can have ANY exact past at all. It does not assume a reset-only backbone, a 12-wheel phase, factor reuse density, or knowing the genuine canonical prefix.

## 1. Exact one-step inverse gcd theorem (PAPER)

Write the original parity-gcd recurrence for n>=3:

    C_pre=D(n-1),  e=d(n),  C_post=D(n)=C_pre+e-1,

    e=gcd(n,C_pre-1)       n even,
      gcd(n-2,C_pre+1)     n odd.

All horizon states after n>=2 are even, and e is odd. Given n and an EVEN proposed post-horizon C>=2, let

    u=n mod 2; A=n-2*u; B=C+2*u.

The complete list of predecessor pairs (C_pre,e) in the original gcd recurrence, with C_pre even>=2, is EXACTLY

    BOXED: e is positive odd, e | gcd(A,B),
           C_pre=C-e+1>=2,
           gcd(A/e, B/e-1)=1.                           (1)

Proof: in both parity cases, the gcd defining e is

    e=gcd(A,B-e).

If e divides A,B, then gcd(A,B-e)=e*gcd(A/e,B/e-1). Thus (1) is necessary and sufficient; there are no omitted increments. Conversely, if a forward step with odd e produces C, its defining gcd forces both divisibility conditions and the coprimality condition.

This is a finite list because every e divides the explicitly known gcd(A,B). The reverse map is MULTIVALUED; it is NOT correct to assert e=gcd(A,B).

For any terminal pair (K,C), define S_0={C} and recursively

    S_j = union_{h in S_(j-1)}
          {h-e+1 : e satisfies (1) at n=K-j+1 with post=h}. (2)

There is a valid gcd prehistory of length L ending at C if and only if S_L is nonempty, subject to any separately required starting-state bounds. In particular

    BOXED: S_L=empty ==> NO original parity-gcd history
           of length L can end at (K,C).                (3)

This backward obstruction is **unconditional** on the canonical input M, prime-valued endpoints, and earlier behavior: emptiness alone rules out the last L steps of EVERY purported trajectory ending at that state. It is thus usable as a sound BAD-specific exclusion certificate when C±1 are not twin primes.

## 2. Two earlier locally BAD twin-input witnesses are impossible after only 8 or 6 reverse steps

The preceding full-history note supplied TWO explicit artificial terminal assignments that satisfied the original exact gcd at K and K+1, canonical horizon size bounds, and genuine input twin-primality M-2,M. It did NOT assert their full prehistories were realizable.

**Witness A:**

    M=101119,  M-2=101117 (both prime);
    K=176958,  proposed C=D(K)=236004;
    e(K)=3 from C_pre=236002;
    e(K+1)=11 from the proposed post-horizon C=236004.

Reverse horizon-set sizes |S_j|, j=0..8, with NO forced choice of e(K):

    (1,2,2,3,2,2,2,1,0).

At the final obstruction, n=176951, the only remaining candidate post-horizon is h=236000. Then

    A=n-2=176949, B=h+2=236002;
    gcd(A,B)=1 but gcd(A,B-1)=3.

The only possible e dividing gcd(A,B) would be e=1, but the actual gcd required by e=1 is 3. So there is no predecessor. Hence the proposed C at K is impossible for EVERY history spanning the preceding eight indices.

**Witness B:**

    M=100549,  M-2=100547 (both prime);
    K=175960,  proposed C=D(K)=241340;
    e(K)=5 from C_pre=241336;
    e(K+1)=3 from C=241340.

The complete unforced reverse-set counts for j=0..6 are

    (1,2,2,3,2,1,0).

The last candidate at n=175955 has h=241340, and

    A=175953, B=241342;
    gcd(A,B)=1 but gcd(A,B-1)=3.

Again the only candidate e=1 is impossible. Therefore NO original history of length six reaches this terminal state. These are genuine two-step *local* gcd configurations but not realizable cutoff histories.

**Positive controls:** exact direct canonical replays for synthetic M=13,43,305 (including actual small BAD examples) have their TRUE post-horizons in EVERY reverse layer all the way back to canonical s=M+2; true synthetic GOOD examples M=307,101119,100549 also remain in every checked reverse layer. Thus the sieve does not merely label all BAD horizons impossible.

## 3. Infinite affine CRT lifts retaining local BAD hits AND the inverse contradiction

Let (M0,K0,C0) be either witness above, and set for arbitrary integer t>=0

    M(t)=M0+840*t,
    K(t)=K0+1470*t=floor((7*M(t)-1)/4),
    C(t)=C0+2100*t.                                  (4)

The parity of K stays even, and the canonical bounds 2M(t)-2<=C(t)<=2K(t) persist. The terminal local gcd values are obtained from linear pairs

    e(K)=gcd(K,C-e(K)),
    e(K+1)=gcd(K-1,C+1).

The first e(K) identity is the *backward* formula specialized to the known chosen post-event increment.

**Affine determinant periodicity lemma (PAPER).** For fixed integer slopes beta=1470, delta=2100, and positive affine forms

    A(t)=a+beta*t, B(t)=b+delta*t,

the gcd g(t)=gcd(A(t),B(t)) divides the constant determinant

    Delta=delta*a-beta*b.

If Delta!=0 and Q is a multiple of |Delta|, then

    g(t0+kQ)=g(t0) for every integer k>=0.

Indeed g(t)=gcd(A(t),B(t),Delta), and the first two arguments are unchanged modulo Delta. Likewise, for every prescribed e>0 the gcd

    gcd(A(t),B(t)-e)

divides Delta+beta*e, and is periodic when Q is a multiple of |Delta+beta*e|.

Build the finite reverse tree at t=0 to depth L=8 or6. Choose Q to be the least common multiple of:
- the two nonzero determinants of the prescribed exact last two local gcds;
- for EVERY reachable reverse-tree node in depths 0..L-1, its nonzero determinant Delta for (A,B);
- for EVERY odd divisor e of gcd(A,B) at each such node, its nonzero determinant Delta+beta*e, whether or not e is a valid predecessor;
- the primes 3,5,7,11,13,17,19,23,29,31.

All determinants in these two exact finite trees were computed and verified nonzero. By induction the entire inverse tree for any t=kQ is just the original reverse tree translated by 2100*kQ in horizon. In particular the last layer STILL is empty for every k>=0, while both prescribed local gcd hits remain exact.

The companion program calculates such explicit positive periods:

    Witness A: Q has 477 bits (144 decimal digits), reverse contradiction at L=8.
    Witness B: Q has 325 bits (98 decimal digits), reverse contradiction at L=6.

These are INFINITE families of increasingly large, locally valid BAD cutoff assignments **PROVABLY excluded by the short exact reverse gcd history**. The input residues M(t) mod q for q<=31 remain identical to those of the actual twin-prime base M0, so no prime q<=31 divides M(t) or M(t)-2; HOWEVER **full twin-primality of the lifted M(t) is not asserted**.

Checks at k=1,2,5 verified exact terminal local gcds, fixed small-prime admissibility, complete translation of all inverse-tree layers, and the empty final layer with huge integer inputs. The infinite statement follows from the determinant congruence argument, not from finite sampling.

## 4. Why this directly addresses the BAD-specific gap, and what remains

The earlier approach tried to derive a universal R_M recycling upper bound, but there are GOOD artificial trajectories with very high R. The present **BAD-specific inverse sieve** does not constrain GOOD paths at all. It can reject a proposed BAD terminal state from only 6–8 known indices even where:
- the input M-2,M is an ACTUAL pair of primes;
- the very last one/two gcd steps are locally correct;
- canonical horizon and travel bounds hold;
- the coarse earlier global potential budget test does not rule out the proposal.

It removes two previously surviving concrete BAD-local obstacles as GLOBAL full-prefix candidates, and eliminates infinite affine lifts of those obstacles. But it does NOT prove that every sufficiently large canonical BAD terminal state has an empty inverse tree of bounded or growing depth. Actual BAD examples at small M have genuine inverse paths, and in general the inverse tree can branch or stay nonempty for many indices.

**Next precise target:** for a hypothetically attained canonical BAD M with C=D(K), find a universal finite-depth reverse obstruction OR derive a complete canonical-start inconsistency when propagating (2) back to s=M+2, using two-sided prime-input admissibility, current Lean potential W bounds, and exact backward transition gcd. Such a theorem is still the missing global Cap B statement; it has not been proved here.

Independent reproducible auditor: [bad_terminal_reverse_crt_audit.py](bad_terminal_reverse_crt_audit.py). It checks 15,930 exact forward/inverse steps, authentic versus synthetic positive controls, the two full inverse-tree empty-state certificates, and affine-lifted cases. Paper plus executable code are saved with GitHub remote readback. No new Lean kernel check.
