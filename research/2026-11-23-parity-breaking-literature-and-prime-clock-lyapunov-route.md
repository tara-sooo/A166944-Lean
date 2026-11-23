# Twin-prime-first broad literature audit and a finite-clock Lyapunov route

Date: 2026-11-23 JST. Target: **infinitely many twin primes**, independently of the stronger A166944 record assertion. This note records a research attempt and a new, exact, replayable *finite* certificate. It is **not** a proof of twin-prime infinitude or of an unbounded prime-clock estimate. New finite certificates are integer checked by the separately committed Python verifier, not yet Lean checked; the existing 22,050-state LOW7 certificate in draft PR #5 was independently kernel-checked by successful GitHub Actions run 45130164879. Main is untouched.

## 1. New proposed route: prove a universal amortized prime-clock travel bound

For finite odd prime alphabet S, P=product(S), define the infinite-horizon squarefree parity-GCD event clock for state (t,C), C even:

* if p|C−1: even p clock at n ≡ 0 (mod 2p);
* if p|C+1: odd p clock at n ≡ p+2 (mod 2p);
* take the first positive clock gap g; all tied primes form d=product(tied primes); update (t,C) -> (t+g,C+d−1);
* if no clock is active, stop.

This is a deterministic graph on 2P² residue states, (t mod 2P, C/2 mod P). Let tau_S(v) be **total clock travel to the sink**, interpreted as infinity if an actual cycle is encountered. The following is an **OPEN, strong conjectural target**:

    exists universal A>0, for all finite odd prime sets S, all states v:
           tau_S(v) <= A * sum_{p in S} p.         (UNIFORM-CLOCK)

It is not assumed in the previous LOW7 results. It could FAIL for large alphabets; small tests are not an asymptotic proof.

### Exact new implication to twins (elementary PAPER proof)

Take dyadic X, every odd M in [X,2X), B=ceil sqrt(7X), S=odd primes <=B, t=M+2,C=2M−2, K=floor((7M−1)/4). Then K−t>=3X/4−2, B²=7X+O(sqrt X), and the standard terminal squarefree-wheel certificate says K−S_last>=2B ensures terminal C−1,C+1 are twin primes (using C<=2K). Prime number theorem gives

    sum_{3<=p<=B} p = (1/2+o(1))*B²/log B = o(X).

UNIFORM-CLOCK implies tau_B=O(X/log X)=o(X), so all such canonical starts have their last event before K−2B, and hence all produce a twin-prime pair. Since output C>=2M−2, pairs are unbounded as X grows. The even WEAKER uniform target limsup_B sup_v tau_B(v)/B² < 3/28 would suffice for S={3<=p<=B}, with B restricted to the dyadic cutoff sequence; o(B²) is easier to state. No such uniform estimate has been proved.

The route replaces the adaptive *source-selected repeated-q* estimate by **one bound on an absorbing deterministic finite-prime clock**. Crucially, the theorem must control the number of replenishments/renews, not just the next-event gap: the gap is already <=2B whenever any prime is active.

### Symbolic base cases

For two primes 5<=p<q, the earlier paper lemma says the q prime fires at most once: between two q hits only one p hit could occur, with growth p−1<q−1. The p events before/after q number at most two. Thus at most **three** events, and tau_{p,q}<=6q<=6(p+q). If S={3,q} with q>=7, a pure-3 segment has at most two 3 hits and gains <=4, insufficient to reactivate q (needs >=q−1>=6). Thus at most **five** events and tau_{3,q}<=10q. For S={3,5}, exhaustive 450-state verification gives maximum 6 events and finite time. These are special cases, not an induction for many primes.

## 2. Exact finite full-graph checks

Replay with research/prime_clock_automaton_exhaustive.cpp, strict compiler flags -std=c++17 -O3 -Wall -Wextra -Werror. The graph's stored full-time value satisfies tau(v)=g(v)+tau(next(v)) and stops at a sink.

| Alphabet | #states | directed cycles | max events | max time | max clipped growth |
|:--|--:|--:|--:|--:|--:|
| 3,5,7 | 22,050 | 0 | 9 | 56 | 106 |
| 5,7,11 | 296,450 | 0 | 6 | 70 | 384 |
| 3,5,7,11 | 2,668,050 | 0 | 22 | 133 | 1,156 |
| 3,5,11,13 | 9,202,050 | 0 | 18 | 97 | 2,146 |
| 3,7,11,13 | 18,036,018 | 0 | 13 | 116 | 3,004 |

For larger first-prime alphabets, reproducible **nonexhaustive** CRT-residue simulated-annealing stress tests (research/prime_clock_adversarial_search.cpp, seed 20261123, 50k mutations for B<=97 and 45k for larger bands) found these finite achieved times: B=19:285, 31:641, 47:1288, 67:2056, 97:3772, 127:4922, 149:5171, 211:9262, 251:11422. For B=251 (53 primes) sum primes=6079, achieved max ratio tau/sum p=1.879. For B=31 ratio 4.057. These are **lower bounds on the unknown worst-state travel**, not upper bounds, and no general cycle-freeness assertion follows. Each probed trajectory stopped within the script's 30,000-event guard.

## 3. A concrete new structural finding: SINGLE-prime additive potentials are impossible already at LOW7, PAIRWISE interactions work

For S={3,5,7} the exact graph has 22,050 states and 18,900 live edges. Define the p-local state (t mod 2p, C/2 mod p), and a putative additive potential

    V(t,C)=f_3(v_3)+f_5(v_5)+f_7(v_7).

To prove finite elapsed travel one would require V(v)-V(next(v))>=g(v) for every live edge.

**NEW exact negative finite certificate (integer arithmetic):** The committed file research/low7_local_dual.b85 encodes **133 distinct graph edges with positive integer weights** w_e such that, for EACH p in {3,5,7}, the weighted incoming and outgoing frequencies of EVERY p-local state agree. Consequently, for ANY real-valued functions f_p, sum_e w_e(V(next(e))-V(start(e)))=0. But integer-verifying the same 133 edges yields

    sum_e w_e*g(e) = 1,240,352,399,315,487,570 >0.

Summing the desired decreases produces contradiction. Thus no scalar *separable* p-local Lyapunov potential can have all required decreases, even though the global LOW7 graph terminates. This is a rigorous **finite** combinatorial no-go under exact displayed state definition (not a general theorem for all alphabets).

**NEW exact positive finite certificate:** The file research/low7_pairwise_potential.b85 contains 3,782 nonnegative integers giving

    V(t,C) = f_{3,5}(v_{3,5}) + f_{3,7}(v_{3,7}) + f_{5,7}(v_{5,7}),
    0 <= V <= 268

where each pair state uses (t mod 2pq, C/2 mod pq). The script research/prime_clock_potential_certs.py recomputes the exact 18,900 original clock transitions and checks in pure integer arithmetic that V(v)-V(next(v)) >= g(v) for ALL live edges. It also verifies the 133-edge local circulation and independently reconstructs the optimal full-graph time bound56, growth106 and max9 events. No solver, floating arithmetic or third-party dependencies are required for replay. The pairwise potential was found numerically using SciPy HiGHS and then converted to an integer array; only the integer certificate is used in validation. The bound268 is deliberately weaker than the optimal56.

**Interpretation:** an approach that adds independent one-prime cost functions cannot work even for LOW7. A non-additive **cross-prime correction** is mathematically necessary at this finite scale. The successful pairwise certificate is a finite prototype of an interacting prime-clock Lyapunov function. It does **not** imply an O(sum p) bound for arbitrary S: summing O(pq) contributions for ALL prime pairs could itself exceed the needed budget.

## 4. Literature cross-check; what may actually transfer

**Friedlander and Iwaniec, "Asymptotic sieve for primes" (1998, https://arxiv.org/abs/math/9811186):** a Type II bilinear input breaks classical sieve parity for prime extraction. The required shifted-prime bilinear estimates are not supplied by this theorem. Potential application here is to bound cross-prime *coupling terms*, not to assume parity has already disappeared.

**Tao, "Notes on the Bombieri asymptotic sieve" (2016, https://terrytao.wordpress.com/2016/07/17/notes-on-the-bombieri-asymptotic-sieve/):** even Elliott–Halberstam-type inputs leave an unknown parity scalar. Under GEH, the twin-prime asymptotic is equivalent to a rough-restricted Möbius two-point correlation at the x/log²x scale. An ordinary unweighted two-point cancellation theorem cannot simply replace that restricted estimate.

**Li–Liu, "Theorem (1+1.9) on the Goldbach Conjecture" (2026, https://arxiv.org/abs/2606.05224), Theorem 1.2:** obtain an unconditional (1−1.75) Chen-type result for infinitely many primes p with p+2=rq, r either 1 or prime and r<=q^{0.75}. The theorem does not select infinitely many r=1; it is a genuine near-twin advance, not the twin-prime theorem.

**OpenAI, "Ordinary two-point correlations of multiplicative functions" (Sep 2026, https://github.com/openai/math/blob/main/lean/docs/007.md):** announces ordinary fixed-form Liouville 2-point cancellation O(x/log^c x), c>0, with Lean formalization. This alone is weaker than the needed x/log²x restricted correlation and the moving rough cutoff. Its independent-prime coordinate conditioning, inverse/spectral arguments may inspire methods, but uniformity in the source-selected q-clock path must be separately established.

**OpenAI, "A quadratic bound for Jacobsthal's function" (Sep 2026, https://github.com/openai/math/blob/main/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf):** proves h(k) << k²/(log log(3k))² for **one prescribed residue class per prime**, via a decreasing-prime tree, an inverse theorem for modular rational alignment, variance and **stopped prime bins** (Sections 3, 7–10). A frozen prime-clock plateau also has at most one ACTIVE next-hit residue class per p; however, an event changes the active classes, so h(k) bounds neither their number of renewals nor tau_S. The transferable proposal is instead the paper's **inverse-concentration or low-effective-size stopping dichotomy** adapted to the moving prime-clock phase data. This is the strongest structural technique found for the new route.

**Ziller–Morack, "A short note on the computation of the generalised Jacobsthal function for paired progressions" (2017, https://arxiv.org/abs/1706.03668):** paired-residue Jacobsthal conjectural <p²−p bound suffices for prime pairs; computed only up to prime73. Distinguish its TWO forbidden residue classes per p from the proven ONE-class Jacobsthal theorem. Related independent research on dimension-two twin slots (https://github.com/solveathome/twin-primes) reports a DHR sieve exponent4.26645, too large for a quadratic twin-prime certificate. The adaptive wheel is NOT simply a solution of this paired fixed-covering problem.

**Helfgott–Radziwill/Pilatte expansion and parity** (https://www.ias.edu/video/expansion-divisibility-and-parity): graph expansion controls multiplicative correlations and may supply spectral diagnostics for aligned prime-clock recharges; no currently verified theorem covers the changing, source-conditioned clock words. **Pascadi (2026), "Non-Abelian Amplification and Bilinear Forms with Kloosterman Sums"** (https://link.springer.com/article/10.1007/s00039-026-00746-0): improved Type II estimates for special bilinear arithmetic kernels, not an automatic estimate on this GCD dynamical system. An explicit kernel decomposition would be necessary.

**Recent bounded gaps:** https://teorth.github.io/optimizationproblems/constants/88a.html records a 2026 claimed/verified-at-stated-scope upper bound H_1<=186, with nontrivial formalization caveats. Even GEH-based Maynard/Polymath bounds stop at >2 for parity reasons. This does not supply the requested infinite twin proof.

## 5. A sharpened mathematical program (UNPROVED)

The research bet is not "Fourier randomness of q"; the previous exact coalescence witness X524288 q1201 has 31 starts merged into ONE (q,t,C,next t) key, so independence would be spurious. The new strategy is **interaction-limited deterministic transport**:

1. For each S, construct a *possibly pairwise plus exceptional-cluster* potential
       V_S(v)=sum_{p<q} F_{pq}(v_{pq})+E_S(v),
   where F_{pq} are nonnegative pairwise clock/renewal corrections and E_S captures exceptional clustered reactivations.
2. Prove the TRUE one-step Bellman inequality V_S(v)-V_S(next(v))>=g(v) for every applicable state, and the global bound sup_v V_S(v)=o(B²), ideally O(sum_{p<=B}p). Simple singleton additivity is EXACTLY obstructed by the 133-edge dual.
3. Adapt the 2026 Jacobsthal **inverse-alignment/stopped-bin** mechanism to show that the mass of genuinely aligned prime-pair interactions can be charged to a *bounded effective number of owner primes*, rather than the full O(pi(B)²) set of pairs. A concrete missing estimate is
       sup_v [sum of uncharged pairwise recharge contributions along path] <= C sum_{p∈S}p.
   Its proof is THE analytic/combinatorial gap, not supplied by finite certificates or existing one-class Jacobsthal.
4. Stress-test for state-cycle counterexamples and superlinear ratios as B increases. For increasing S, test whether pairwise-only potentials remain feasible; if not, characterize exactly which triple interactions are necessary, then either pay for them through an inverse theorem or use average source-weighted alternatives.

If this plan's global amortized potential inequality is proved, §1 establishes the infinitude of twin primes immediately. The present checkpoint establishes the precise theorem to target, the necessity of prime interactions, and a first exact integer pairwise prototype; **the unbounded-X step is still open**.

## 6. Reproducibility

```sh
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/prime_clock_automaton_exhaustive.cpp -o /tmp/clock
/tmp/clock 3 5 7
/tmp/clock 3 5 7 11
/tmp/clock 3 7 11 13

g++ -std=c++17 -O3 -Wall -Wextra -Werror research/prime_clock_adversarial_search.cpp -o /tmp/clock_search
/tmp/clock_search 31 50000
/tmp/clock_search 251 45000

python3 research/prime_clock_potential_certs.py
```

Verification classes: finite full-graph enumerations = computational with exhaustive small-alphabet coverage; 133-edge impossibility and 3-pair positive potential = **exact integer finite proofs** runnable from committed files; symbolic 2-prime and implication-to-twins = paper deductions; h(k) and near-twin sieve theorems = literature claims; global clock budget and effective-owner interaction bound = OPEN; no fresh Lean kernel theorem in this note. Working branch research/issue-3-cross-prime-correlation; no main modification.
