# Canonical MIN: every-other high-prefix certificate and a direct p,q,p bridge

Date: 2026-11-24 JST.
Base: PR #8 / `research/canonical-p-return-recharge-2026-11-24` at `236738e1e66a8e3b11ab8f45cc355db90890d81b`.
Scope: two-step sampled-prefix formalization and source-weighted correlation roadmap, NOT a proof of infinitely many twin primes.

## 1. Actual MIN data and the new exact finite implication

Keep the exact canonical MIN clock, per-source stopping point `K(M)`, and first-hit/least-prime tie-breaking of `research/canonical_min_prefix.lean`.
For dyadic X=4u, B>=sqrt(7X), odd sources X<=M<2X, define
`L=lowModulus(B,y)`, `P=|{p: y<p<=B, p prime}|` and the actual high word `w_M`.

Define `s_M` by keeping positions 1,3,5,... of `w_M` and stopping after at most 2P retained labels. Let

    D_odd(X) = sum_{M odd, X<=M<2X} (|s_M|-number of distinct labels in s_M).

The existing exact non-twin clock budget implies

    not-Twin(M) => K(M)-(M+2) <= (|w_M|+1)*(2B+3L).

Therefore, under the explicit arithmetic checks

    7X <= B^2, 4P*(2B+3L) < 3X/4-2,

every non-twin source has |w_M|>=4P, hence |s_M|=2P and at least P repeated sampled labels. Consequently

    D_odd(X) < (X/2)*P  =>  some terminal gives twin primes.

The file `research/canonical_min_odd_sample.lean` proves precisely this finite result, with an unbounded-window conditional corollary. It also instantiates the existing `split_count` lemma for odd-sample words. Compared to the old third-position/6P window, this uses 4P high selections, which relaxes the clock length prerequisite by a factor 2/3. The **deficit hypothesis is still open**.

For y chosen so 2*prod_{3<=p<=y}p <= sqrt B, P~B/log B, L<=sqrt B, and 4P*(2B+3L)=o(X), so the arithmetic clock condition holds for all sufficiently large dyadic X. This asymptotic step has NOT been kernel-formalized.

## 2. PR #8 p,q,p is now literally a sampled collision

If the actual HIGH(y) word begins `p,q,p,...` and P>0, then

    sampleOdd(P, HIGH(y) word) begins p,p.

Thus the sampled repetition count is >=1 for that very same original source M.
`everyOther_pqp`, `sampleOdd_pqp`, and
`first_three_high_pqp_implies_odd_repeat` formalize this statement.

Important cutoff distinction: PR #8's nontrivial (N_Q(X)) estimate counts the
first three HIGH11 selected primes (LOW7={3,5,7}, y=7).
For *y=7*, the p,q,p class in that estimate agrees exactly with the
first collision class in the new sample. For the moving cutoff y>7, the
first three HIGH(y) labels form a **different** class; PR #8's bound
cannot be re-used unchanged, although the list-theoretic collision
implication holds for all y.

PR #8's paper proof for p>=Q>=840 gives

    N_Q(X) << B log(2B) + X/Q + XB/Q^2,

and at Q~B/log B, using prime counting in the p sum,

    N_Q(X) << B log B = o(X).

This is a real source-counted bound for one early first-position pattern.
Yet ONE fixed position pair contributes at most X/2, already o(XP)
since P tends to infinity. Therefore this early-pattern theorem alone
does not yield a nontrivial global D_odd asymptotic estimate.
The real objective is an aggregate over all sampled position pairs.

## 3. The precise missing source-weighted pair correlation theorem

Take W=4P, a=ceil(sqrt(log B)) and write n_{M,p} for the
multiplicity of label p in s_M. The existing split proof yields

    D_odd(X) <= (X/2)*pi_{(y,W]} * a + A_odd(X) + C_odd(X),

where
    A_odd(X)=sum_{M,y<p<=W} (n_{M,p}-1-a)_+,
    C_odd(X)=sum_{M,W<p<=B} binom(n_{M,p},2).

Prime counting gives `(X/2)*pi(W)*a=o(XP)`.
A sufficient pair of *new analytical goals*, on the same unbounded
dyadic windows, is

    A_odd(X)=o(XP),  C_odd(X)=o(XP).

The full large-prime count can be written **exactly** in positional
language. Number the sampled positions i=1,...,2P, and let

    V_{ij}^{>W}(X)
      = #{original sources M: positions i,j exist, i<j,
           s_M[i]=s_M[j]=p for some p>W}.

Then the exact combinatorial identity is

    C_odd(X)=sum_{1<=i<j<=2P} V_{ij}^{>W}(X).          (CORR)

This is an identity of counted pairs, not an independence hypothesis.
The target is a source-weighted sum over ALL the indices in (CORR).
A convenient sufficient uniform target, stronger than necessary, is
`V_{ij}^{>W}(X)=o(X/P)` uniformly in i<j. It does not yet follow
from the first-p,q,p theorem. The statement (CORR) and asymptotic
uniform target are mathematical research formulations; Lean currently
formalizes the label-frequency split, not the position-pair identity.

### Algebraic information available for each coincident pair

For large X, W=4P exceeds L (because L<=sqrt B and P~B/log B).
For p>W in two sampled positions, their high-event indices differ by
at least 2. Between them is at least one other selected high label
q!=p: adjacent repeated selected p hits would require at least p-1
of low-only growth, contradicting the low-barrier bound <L.

Write b_r for the selected multiplicity of each intervening high
label r, and E_low for all intervening low-only increments. With
endpoint signs sigma_i,sigma_j in {-1,1}, the exact necessary
condition is

    p | (p-1) + E_low + sum_r b_r*(r-1) + sigma_j-sigma_i.

Pick q!=p present between endpoints. Because the intervening high
segment lies inside the first 4P high events,

    1<=b_q<4P<p.

Thus b_q is invertible modulo prime p. If every other component of
the actual intervening history is fixed, the condition constrains
q to ONE residue class modulo p. What is missing is a uniform count
of ORIGINAL M giving those adaptive histories, with multiplicity
preserved across state coalescence. Summing residue classes over
unconstrained histories loses all the hoped-for saving.

On the small-label side, a candidate stronger tail estimate is

    sum_{M,y<p<=W} (n_{M,p}-1)^2 << X*pi(W)*log B,

which would imply A_odd(X)=o(XP). This moment is also OPEN.
Combining an honest source-weighted pair-correlation bound with a
small-label return tail would complete the analytic implication.

## 4. Finite oracle and the difference between sample schemes

Run from project root:

    python3 research/min_odd_sample_audit.py 256 1024 4096 16384 65536

This computes the MIN path for EACH original M, retaining its own K(M),
and crosschecks the small windows against literal parity GCD.
For each source it also asserts that the first-three-HIGH(y) p,q,p
pattern agrees with the first pair of the odd sample, both for y=7
and for growing y.

Independent local replay of exactly the same prime-clock recurrence:

| X | B | growing y | D_odd | old D_thirds | first LOW7 p,q,p | first HIGH(y) p,q,p | odd small moment | odd large pairs |
|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| 256 | 43 | 3 | 129 | 31 | 17 | 16 | 207 | 0 |
| 1024 | 85 | 3 | 251 | 77 | 28 | 51 | 485 | 0 |
| 4096 | 170 | 3 | 3252 | 1322 | 126 | 281 | 9826 | 0 |
| 16384 | 339 | 3 | 19181 | 8559 | 474 | 1138 | 65163 | 0 |
| 65536 | 678 | 3 | 99396 | 46875 | 1865 | 4613 | 380258 | 0 |

The two sampling schemes are not directly ordered in general;
the displayed tests have a larger D_odd. The long-history condition
4P*(2B+3L) < 3X/4-2 does not hold at these sample scales.
Neither the finite data nor the p,q,p bound establishes the global
moment estimate or twin-prime infinitude.
