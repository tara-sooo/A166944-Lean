# Lag primorial barriers, sharper deficit certificate, and arbitrarily deep local false ancestry

2026-11-26 JST. Continuation of 40a1d064263a8d4715f99d339ac470bbb5c09c60, research/2026-11-26-min-primorial-all-reset-reachability.md. Paper proofs and finite arithmetic checks; no Lean verification, external novelty claim, or proof of twin infinitude.

## 1. A finite small-label certificate for the global reset deficit

Use the universal offset MIN with initial (X,v0)=(12k,6k+3), k>=1, d0=6 and arbitrary r=X/2+1, not necessarily prime. For each event define the integer reward

    E=13 delta d-48 delta u=26w-61(p-1).

For p>=13, w<=2p gives E<=61-9p<=-56. In a maximal run with all labels in A={3,5,7,11}, the actual events are a prefix of the A-only first-clock MIN: a larger label may preempt the next A-event but cannot alter an already selected A-event. Let Q=2*product A=2310. Clocks depend only on u,v modulo Q. No A-event can strictly cross an even multiple of Q: at distance h=J-u, if p|u±1 then h is a positive even integer congruent to ±1 mod p, hence h>=p-1. At u=J no A-label can fire. Thus every restricted run stays in a single interval between successive Q-walls and has a finite number of events.

The exact integer certificate is the maximum prefix reward function F(u,v), for u even in [0,Q], v in [0,Q-1]. If no p in A divides a neighbor then F=0. Otherwise determine the lexicographically minimum (w,p) among the eligible A-clocks, with w=((s-v-1) mod 2p)+1, s=0 for minus, s=p+2 for plus. The recursion is

    F(u,v)=max(0,26w-61(p-1)+F(u+p-1,(v+w) mod Q)).

The first argument strictly increases, never above Q, so descending u computes the entire table. Evaluation at all 2,670,360 entries gives

    max F=56,
    max_{0<=k<Q/6} F(12k mod Q,(6k+3) mod Q)=24.

The second maximum covers all reset residues since the displayed state repeats under k->k+Q/6. The audit computes the table with vectorized integer operations and independently checks every entry against the scalar clock recurrence. Maximum witness at (u,v)=(118,121) has (p,w,E)=(3,5,8),(7,14,-2),(5,10,16),(3,6,34), total 56; reset witness k=8 has (5,9,-10),(3,6,34), total 24. The arbitrary-state certificate need not restrict the time envelope; this larger residue domain is safe for an upper bound. Witnesses are modular restricted runs, not claimed reachable full MIN words.

Partition any finite real reset prefix into initial small-label run and subsequent large-label singleton followed by a small-label run (possibly empty). Initial reward <=24, every subsequent block <=-56+56=0. Hence the unconditional, computer-assisted finite-certificate inequality is

    13(d-6)-48G<=24,
    d<=102/13+(48/13)G.

The symbolic reduction is independent of the numerical audit of actual rays. The two finite table maxima are the only computed facts used in this inequality; the source reproduces and independently checks them. No Lean proof yet.

## 2. Improved displacement criterion

At a non-twin doubling u=X+G, prior classification requires d>=u-2sqrt(u-1)-2. Thus

    35G>=13X-26sqrt(X+G-1)-128.

For G<=X/3 and X>=720, this is impossible: it would require (4/39)X<=2sqrt(4X/3-1)+128/13. The difference is positive at 720 and strictly increasing thereafter (differentiate or compare the square roots by rationalization). A non-doubling first record p>r has G>=X/2+8. Therefore for every integer r=1 mod6, r>=361,

    G(r)<=X/3 ==> the first selected label >r is a twin record.

More generally the sufficient asymptotic displacement fraction can be any fixed number below 13/35, versus the previous 3/10. For an unbounded family of arbitrary reset seeds this would imply unbounded twin centers, without a prior-twin hypothesis. The necessary upper bound on G(r) is still missing.

## 3. Exact lag map and dual primorial barrier

Write L=u+3-v, so L>=2 by the universal time envelope. At an event with time n=v+w<=u+3 put s=u+3-n=L-w>=0. For a fixed selected p the first clock is the largest s<L in its clock class. If p|u+1 (plus), u is even, u+3=p+2 mod 2p, hence s=0 mod 2p. If p|u-1 (minus), u+3=p+4 mod 2p, so s=p+4 mod 2p (for p=3 the representative is 1). Thus the exact selected-event lag update is

    s=max{j: j<L, j>=0, j=0 (plus) or p+4 (minus) mod 2p},
    L'=s+p-1.

The maximum exists for the actually selected p. Consequently L'>=p-1 and L-L'=w-(p-1)<=p+1<=L'+2, so L'<L can never reduce the lag by more than a factor 2 up to an additive constant: L'>=(L-2)/2.

Dual barrier: let J be a nonnegative even multiple of p. If L>=J+2, then L'>=J+2. For J=0 this follows from p>=3. For J>0, in the plus case the candidate s=J lies below L, hence L'>=J+p-1>=J+2. In the minus case p>=5 the candidate s=J-p+4>=0 is below L and gives L'>=J+3; for p=3 use s=J+1 to get the same. This argument applies to the selected label only and needs no assumptions about other clocks.

For any finite consecutive block with distinct label set A, P=product A, put J=2P*floor((L_start-2)/(2P)). Every selected label divides J/2, and the barrier gives L_end>=J+2. Therefore

    L_start-L_end < 2P.

Unlike the old horizon barrier, this controls the phase coordinate directly. The old horizon barrier and the new lag barrier jointly constrain both directions over a finite-alphabet block. In particular a drop by D>0 requires product of the distinct labels >D/2, even if many labels repeat.

Multiscale consequence: for a non-twin doubling reached from reset X at u<=A0 X (fixed A0), L_start=X/2 and L_end<=sqrt(A0 X)+4. Choose levels H_j=(X/2)/4^j with H_j/4>sqrt(A0 X)+4, let t_j be the first index with L<H_j. They are strictly increasing for H_j large since L' >= (L-2)/2; at t_j the lag is >=H_j/2-1. Each disjoint segment from t_j to t_{j+1} has lag drop >H_j/4-1 and hence its distinct-label product exceeds H_j/8-1/2. There are Omega(log X) such segments and log H_j >= (1/2)log X-O(1). Consequently the sum, over these disjoint segments, of log of the products of their distinct labels is Omega((log X)^2). If labels within the segments are bounded by B, each needs at least log(H_j/8-1/2)/log B distinct labels. This is a support/phase constraint, not stronger than the square-root event toll as an event-count inequality. It also does not exclude paths using large alphabets.

## 4. Fixed-depth reverse ancestry cannot exclude all false doubles

The exact reverse recursion from the previous note remains useful, but no finite fixed number of legal predecessor tests, absent the reset-origin requirement, can eliminate all false-double candidates. The following constructive statement proves this for arbitrary prescribed depth m>=1, even imposing the universal time envelope on the whole path.

Choose odd primes p_i>=7, i=1,...,m, recursively, such that p_i>E_{i-1}+3 and p_i=1 mod 4 Q0 product_{j<i} p_j, where E_i=sum_{j<=i}(p_j-1), E_0=0, and Q0 is the product of odd primes <=2(m+1). Dirichlet applies at every finite step. Set L=3+2 product_i p_i. Seek a constant-lag path from offsets u_i=U+E_i and times v_i=u_i+3-L, U even and sufficiently large. The intended i-th event has label p_i on the minus side and wait p_i-1, so its poststate has the same lag L.

Impose U+E_{i-1}=1 mod p_i. At an earlier plateau, the residue of that offset modulo p_i is 1 minus a positive even gain difference between 6 and p_i-4, not ±1. At every later plateau it is 0 mod p_i by the nested label congruences. Hence the selected primes are eligible only at their intended stage. For each unselected odd prime q<=L+4 exclude the residues U+E_j=±1 mod q for all 0<=j<=m. If q<=2(m+1), all E_j are divisible by q, so U=0 mod q works. Otherwise at most 2(m+1)<q residues are excluded. Set U even. Finally choose a fresh odd prime q_*>L+4 and impose U+E_m-1=0 mod q_*.

All congruences combine by CRT. They give a reduced residue class for U+E_m+1: the selected primes see U+E_m=0, other small primes were excluded, the extra q_* sees U+E_m+1=2, and the integer is odd. Apply Dirichlet to this ONE upper neighbor to obtain arbitrarily large U with U+E_m+1 prime. For U large, all prescribed pre-neighbor divisors are proper and U+E_m-1 is composite.

For each intended event the absolute time n=v_{i-1}+p_i-1 is even, divisible by p_i (since L=3 mod2p_i and u_{i-1}=1 mod p_i), and is its first clock because 0<p_i-1<2p_i. Its relative s=L-(p_i-1)>0. Every unselected prime <=L+4 is excluded at this plateau. Larger primes cannot compete before this tick: their nonnegative plus-clock s values are 0 or >=2q, and minus-clock values are >=q+4. Neither can lie in the positive s interval of the prescribed wait. This verifies actual uncut least-first-clock selection, including tie handling. All states satisfy u/2<=v<=u+1 for U sufficiently large.

At the terminal state u=U+E_m every lower-neighbor prime factor exceeds L+4, and the upper neighbor is prime. The plus clock at u+3 wins, giving u'=2u and d'=6 despite u-1 composite. Thus this is a false doubling with at least m genuine predecessor events satisfying all local rules and the envelope. All m predecessor states are non-twin and have near-maximal d=u+6-2L. These paths start at a high-deficit local state, NOT at a deficit-6 reset, so they do not refute the all-reset conjecture. They prove that any fixed-depth local ancestry condition shared by all envelope-valid legal paths cannot settle that conjecture. Global origin constraints or growing ancestry depth are essential.

## 5. Executed diagnostics

Source research/min_primorial_lag_barrier_audit.py, commit 548efacf93635c52639b0e76848e9d360a22fdaa, remote blob f6af4e93ededaee133fdfc5c79dd831dbf116069 matches the locally executed source. Uses NumPy, SymPy and sibling record-supply audit. Run:

    python research/min_primorial_lag_barrier_audit.py 100000

- All 2,670,360 small-label certificate entries and all scalar recurrence comparisons passed. Maxima and witnesses as in section 1.
- Lag maps and barriers checked at p<100, several periods; symbolic proof in section 3 is unrestricted.
- Reverse enumeration for u<=100000 of every false-double candidate in the time envelope (u=0 mod6, u+1 prime, u-1 composite, u-q-1<=v<=u+1): 108238 candidates, 80654 have no legal predecessor in the envelope with offset >=12. A total of 1,802,265 reverse nodes checked, no reset origin reached. Maximum depth 66 at (59232,59172), one chain begins (58640,58541) and ends (59226,59163)->(59230,59170)->(59232,59172). Full forward clock replay of its 66 edges passed. This is a finite diagnostic, not a global exclusion.
- Constant-lag CRT local examples: labels (7), L=17, final u=374962308, u-1=23*16302709 composite, u+1=374962309 prime (exact under 64-bit deterministic primality testing). Labels (7,13), L=185, forced factor 191, final upper neighbor has 76 digits and passes SymPy's probable-prime test; no primality certificate for that example. Both had literal integer GCD replay of all ticks including terminal firing. The arbitrary-m theorem relies on Dirichlet, not the probable-prime example.

## 6. Next mathematical target

The new finite-certificate bound enlarges the sufficient displacement range and the lag barrier quantifies the prime support required to approach the high-deficit boundary. The construction in section 4 demonstrates that merely increasing a fixed local reverse-ancestry depth cannot prove exclusion; it is necessary to control the full path from low deficit or a depth growing with scale. The main missing step remains an upper bound on G(r) for an unbounded sequence of arbitrary integer resets, or a different unconditional mechanism producing infinitely many rough offsets/twin visits. No such bound has been obtained.
