# Hypothetical infinite MIN worlds VII: deep-state inverse resonance and bounded reverse branching

2026-11-26 JST. Independent continuation of [00f533d](https://github.com/tara-sooo/A166944-Lean/commit/00f533d998b0cc87f48850b95476e41583e68539). Sources: [III clock capacity](https://github.com/tara-sooo/A166944-Lean/blob/ae36ba7e6002e69244233f89fbd810c04a68bbea/research/infinite-orbit/phase_graph.md), [IV low relays](https://github.com/tara-sooo/A166944-Lean/blob/73a01303cbc6c0bc73fa053a1e4e3a6e3525f21a/research/infinite-orbit/low_relay.md), [V entry sieve](https://github.com/tara-sooo/A166944-Lean/blob/6ba4e704c501e32dc06ab2eab3acfe02a4ed3052/research/infinite-orbit/entry_cost.md), [VI recovery ledger](https://github.com/tara-sooo/A166944-Lean/blob/00f533d998b0cc87f48850b95476e41583e68539/research/infinite-orbit/recovery_budget.md). Sibling preflight direct [6433547 uncapped flat run](https://github.com/tara-sooo/A166944-Lean/blob/64335472d06ac37b03076a7f59c5cb17e854c131/research/2026-11-26-min-direct-uncapped-flat-run-and-variation-supply.md), unified [06a9542 medium baseline](https://github.com/tara-sooo/A166944-Lean/blob/06a9542c0017adac88ca496d892b3bb1c79d09bd/research/2026-11-26-min-unified-medium-baseline-reset.md). This note targets genuine deep ordinary deficits d=Theta(X), without assuming small variation or small adjusted multipliers. Paper deductions and finite tests, not Lean verification or novelty claim.

## 1. Exact inverse of a high post-state

Fix a physical window [X,lambda X), lambda>1, and an integer band T<=p<=B with T>=eta sqrt X for fixed eta>0, B=floor sqrt(lambda X+1). Pre-states satisfy the necessary canonical envelope H/2<=t<=3H+3; this includes arbitrary intermediate states satisfying that envelope, not necessarily reached by canonical roots. Given a proposed POST state (J,n), set
    s=n mod2, A=J+2s, C=n-2s, K0=gcd(A,C).
For an incoming actual selected event of label p, H=J-p+1, its side is fixed by arrival parity s. Therefore
    H=1-2s mod p, J=-2s mod p, n=2s mod p.
Thus p divides K0, and in particular there is no freedom to choose the opposite arrival side for the SAME post-state. Conversely, enumerate all prime divisors p of K0 in [T,B]. For each, recover H=J-p+1; reject H outside the window, p²>H+1, or a failed side/factor condition. The parity and divisibility already enforce the selected clock n=0 mod2p (s=0) or n=p+2 mod2p (s=1).

At arrival n, for each other eligible q on side a, let b_q be the positive representative of n-clock_a(q) mod2q, with residue zero represented by 2q. Reject a smaller q tied at n. Otherwise define W_n=min(2p,min b_q), including all competitors. This differs from III's phase-free maximum W(H,p): it is the EXACT maximum wait at this particular arrival. For long events (w>=p-2) the complete possible pre-time interval is t=n-w with
    max(p-2,n-(3H+3)) <= w <= min(W_n,n-H/2).           (1)
The endpoints are integers. Reject an empty interval. Every surviving w gives exactly that selected event by the previous-clock characterization, and every incoming long high event appears. For arbitrary high waits replace p-2 by 1. This is exact inversion of the local MIN rule and envelope, not ancestry. For each label the pre-time interval is contiguous and has at most p+3 integer points in the long case. In particular different starting times may merge even when the incoming label is unique.

Since A=O_lambda(X) and T³>>X, at most TWO distinct primes >=T divide A. Thus each high post-state has at most two possible incoming high labels, irrespective of its multiplier or ordinary deficit. This does not bound the number of pre-times by two.

## 2. Two-label collision forces a quadratic deficit and a rational resonance

Suppose two distinct incoming high labels p,r at the SAME post-state are actually feasible in (1), or feasible with unrestricted high wait. Then
    A=a p r, C=c p r, a>0, a even, c integer,
    J=a p r-2s, n=c p r+2s.                            (2)
The canonical envelope and the wait bound imply J<=lambda X+B, n<=3lambda X+3+2B. Hence a,c range over fixed finite sets depending only on lambda,eta; c>0 for sufficiently large X. Also c mod2=s. The corrected slope (n-2s)/(J+2s)=c/a is one of finitely many rationals. In particular the two-label collision states lie on finitely many exact affine lines in the (J,n) plane, with bounded denominator independent of X.

More significantly,
    d'=2n-J=(2c-a)pr+6s,
    h_p=(d'-6s)/(2p)=(c-a/2)r,
    h_r=(d'-6s)/(2r)=(c-a/2)p.                       (3)
For a positive adjusted nonreset (d'-6s>0) the integer c-a/2>=1. Thus
    d'-6s>=2pr>=2T², h_p>=r>=T, h_r>=p>=T.
This is a necessary genuinely macroscopic deficit for direct DIFFERENT-label high merging. It also applies to short nonreset high events. It excludes such collisions below the quadratic scale without a variation cap or a prime-cofactor hypothesis. A reset (adjusted coordinate zero) is a different case; (3) then has c=a/2, h_p=h_r=0, and does not imply a deep deficit. For long high events with T>=11 a positive nonreset is automatic. Equal-label merges and earlier source multiplicities are not excluded at shallow deficits.

An equivalent screening condition for any post-state: if K0<T², or the reduced corrected slope denominator A/K0 exceeds (lambda X+B+2)/T², at most one high label is possible. The integer factorization and (1) decide even the exceptional slope lines; lying on one is not sufficient for a collision.

## 3. Sparse long-high collision states, including short physical windows

Assume now both incoming events are long. By III/V, each selected composite neighbor is semiprime at sufficiently large X, since every prime factor of either neighbor is >=(p-1)/2 for the first event and >=(r-1)/2 for the second. For e=1-2s, their pre-horizons from (2) are
    H_p=p(ar-1)+e,
    H_r=r(ap-1)+e.
Consequently ar-1 and ap-1 must both be prime. With fixed a from the bounded set, p and r each satisfy two nonproportional prime forms z,az-1. The dimension-two translated upper Selberg sieve used in V and the direct prime-line results gives O_(lambda,eta)(sqrt X/log² X) possible p and separately r. The two forms have nonzero determinant -1; only primes dividing fixed a and the small exceptional primes need be omitted. The required primes have size Theta(sqrt X), above the sieve cutoff. Counting independently is an upper bound; no independence of actual trajectories is assumed. Sum over bounded a,c,s:
    # distinct possible two-label long-high post-states
        <<_(lambda,eta) X/log^4 X.                    (4)
The opposite-neighbor roughness and exact arrival constraints can only reduce this upper count. The result is on physical states, not tagged sources.

There is a uniform localization. Restrict J to ANY interval of length D contained in the post-horizon range, with X^(1/2+epsilon)<=D<=O(X) for fixed epsilon>0. At fixed a,p,s the product condition restricts r to a translated interval of length D/(ap)=Theta(D/sqrt X), padded if needed by a constant multiple. Its logarithm is comparable to log X from below, and a fixed small power sieve cutoff is below the candidate primes. The same two-form upper bound for r is O_(lambda,eta,epsilon)(D/(sqrt X log² X)). Sum over p and bounded a,c,s to obtain
    # distinct possible two-label long-high post-states with J in interval
        <<_(lambda,eta,epsilon) D/log^4 X.            (5)
In particular this holds in the unified X/polylog physical lifetime range; it is uniform in the translate. This is not a bound on all high post-states, equal-label collisions, or their total multiplicities. A single state can receive arbitrarily many previously merged tags as far as this counting argument is concerned. Nor is (4) small enough by itself to prevent a single square-root-scale ray from crossing a macroscopic window.

## 4. Exact compressed reverse graph with bounded branching

Retain the IV low relay cutoff R fixed, exact maximum displacement M_R and the finite table of (E,b) pairs for the terminal restricted low-only transducer. Denote the set of distinct pairs by L_R^off. E<=M_R, b<=3E, including (0,0). Require T>2R+2, so a long high event cannot start with an eligible low factor. The graph vertices are actual feasible high POST states in the window, and an edge is the actual sequence of zero or more low events followed by a long high event. Low steps must finish the restricted relay before the next long high. Full competition must be checked on every step. Both high events have pre-horizons in the same window; no external boundary entry is silently included.

Given target (J,n), invert its last high using (1) to get at most two labels p and a contiguous pre-time interval for each. For each p recover H=J-p+1. For each (E,b) in L_R^off, the candidate prior high post horizon is J0=H-E. For each possible prior side s0, its label r must be a prime divisor of J0+2s0, so there are at most two candidates r>=T. Its time n0 belongs to the translated pre-time interval [n-w_max-b,n-w_min-b] and must be a side-s0 clock modulo 2r. The interval has length at most 2p<=2B, so there are at most 1+floor(B/T) such time candidates. This enumerates all possible prior high post states. For each candidate:
1. Check the prior post-state has feasible incoming r by (1).
2. Follow actual full MIN low steps from (J0,n0), checking low-only relay ends at exactly (H,n0+b).
3. Check the actual next event is the specified long p at n.
Deduplicate by prior physical post-state. Every retained predecessor gives an actual compressed edge and every such edge is enumerated. Thus the reversed compressed graph has in-degree at most
    D_R^rev = 8 |L_R^off| (1+floor(B/T)),             (6)
a constant in X for fixed R,lambda,eta. The factor 8 accounts for 2 current labels, 2 prior sides, and 2 possible prior labels per side. Different histories may share a state; no claim that the graph is globally injective. The bound uses the finite relay displacement/time set, NOT the entire O(sqrt X) possible starting times of the current high. For growing R retain the exact dependence on the size of the offset set. It is not bounded uniformly in R.

For any target, at most (D_R^rev)^j distinct earlier high post states are j compressed edges away. Now consider original canonical odd roots entering this long-high/low-only graph at their FIRST designated long-high event, after arbitrary earlier labels but gain E<=D0. From V, if D0=o(sqrt X), every such first post-state is unit-stratum and its incoming triple (H,p,s) is uniquely determined. The number of canonical root horizons H0=0 mod4 in [H-D0,H] is <=floor(D0/4)+1. Each root determines its first event uniquely. Consequently the total number of DISTINCT original sources that can reach the target through at most k high events INCLUDING their first designated entry, with only these low relays between, is at most
    (floor(D0/4)+1) sum_(j=0)^(k-1) (D_R^rev)^j.      (7)
For exact k replace the sum by its last term. This is a genuine bound on source multiplicity in the specified history class, without assuming the final deficit is shallow, independence, or uniqueness of phase before the first high. For polylog D0 and k=o(log X), fixed R and band constants, this is X^o(1), and therefore cannot itself create a polynomially large cohort X^a (a fixed positive). More generally a target of multiplicity >=X^a in this class requires k>=Omega(log X) if D0=X^o(1), unless the fixed reverse branching constant is 1, when the bound is even smaller. Such depth is not excluded by the previous uncapped capacity results. Neither arbitrary earlier medium/bad-high excursions after entry nor longer histories are bounded by (7). In particular the full unified mass can enter a high state from other history classes and the collision count (4) cannot replace exact tagged accounting.

## 5. Finite diagnostics

Final [deep_inverse_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/faec2b787914c04d8b57b28e55c3e4cd6b7d247b/research/infinite-orbit/deep_inverse_audit.mjs), blob 272a36f64bc8e7e81a7ddc531ff678e821619e41, exact remote readback. Run node research/infinite-orbit/deep_inverse_audit.mjs. Actual ECMAScript execution in available runtime, not separate Node. Initial write succeeded but the first readback action returned INVALID_ARGUMENT; the remote file was subsequently fetched and rerun, then refined and verified exactly. Final assertions pass.

Exhaustive local high arrival scan of [X,4X), T=ceil(sqrt X/2), B=floor sqrt(4X+1), no endpoint-safety restriction. At each eligible label enumerate ALL possible n for some pre-time in the canonical envelope and test the exact backward gaps. These counts are feasible (H,p,n) incidences, not canonical source roots or all pre-time incidences.
| X | candidate arrivals | feasible incidences | d'>=X/4 | distinct two-label collision states |
|---:|---:|---:|---:|---:|
|4096|712513|49887|48987|7|
|16384|5552849|278585|273223|19|
|65536|39069637|1520794|1490914|14|
45,334,999 arrival candidates, 1,849,266 feasible incidences, all checked the high gcd constraint and <=2 possible high divisors. 40 two-label collision state incidences in the three windows (all have d'>=X/4), 12 distinct (unordered p,r,a) incidences; all 40 satisfy both prime-cofactor tests. Maximum incoming distinct labels 2. This is a complete local enumeration at these scales, not an asymptotic test of (4) or (5). Representative deep collision at X=65536:
    J=90652, n=90652, s=0, p=131 or r=173,
    a=4, c=4, d'=90652, h_p=346, h_r=262,
    selected cofactors 691 and 523.
For p the pre-H=90522 with feasible waits [129,262]; for r the pre-H=90480 with waits [171,346]. In particular choosing lower waits gives pre-times 90523 and 90481, and either actual MIN event arrives at the same post state (90652,90652). These states are not asserted to have canonical ancestry. Both positive multipliers are macroscopic in the square-root scale.

R=7 low-relay table gives 400 distinct (E,b) offsets. 1,854 sampled feasible arrivals cross-checked by exact inverse and independent literal tick gcd. Exact compressed predecessor sets at these targets checked (110 returned predecessor incidences). Additionally 482 actual forward high-low-high pairs sampled and included in the exact reverse sets; 663 successful reverse candidate checks (may include duplicated predecessor identities). Largest observed reverse set size 3, not a proof that the uniform constant can be replaced by 3. Code checks (6).

Separate canonical scan from ALL H0=0 mod4 in [X,4X), full actual MIN until stop or exit (cap3000 not reached). Count tags separately from physical high post states:
| X | roots | actual events | good tag visits | physical good states | maximum tag multiplicity | states with distinct pre-times of same incoming label |
|---:|---:|---:|---:|---:|---:|---:|
|4096|3072|42726|1564|161|46|76|
|16384|12288|229666|4933|361|115|214|
|65536|49152|1131473|19693|974|214|606|
64,512 original canonical roots, 1,403,865 events, 26,190 good tag visits, 176 upper exits, 64,336 actual twin stops, zero unresolved. No distinct-label collision among these canonical good post states; no good visit with d'>=X/4. First-good state maximum multiplicities 37,115,213, without restricting pre-entry gain or ancestry labels. These finite data clearly show why inverse LABEL uniqueness cannot imply small SOURCE multiplicity. They do not exercise the finite-twin hypothesis or contradict (7), which has a shallow entry gain and restricted intervening history. No Lean kernel execution.

## 6. Residual high-deficit world

The deep positive-drift survivor of VI is not ruled out. However different-label direct merging is confined to quadratic adjusted deficits, exact rational corrected slopes and sparse semiprime collision states; even in the deep regime a fixed-low-relay high graph admits bounded reverse branching. A hypothetical model attempting to build large shared cohorts solely from shallow high entries with short mixed histories must either use logarithmically many high steps or introduce additional kinds of intervening events/earlier concentration. This gives a precise local-to-tagged constraint, not a contradiction with the newest unified medium-scale baseline. Next: extend the reverse graph to actual medium or bad-high interruptions with charged gain, and compare depth-dependent source capacity with the weighted common-core resource ledger; explore inverse phase at nonconstant large multipliers. All-constraint infinite survivor, uniform uncapped mixed-run bound and finite-twin contradiction remain open.
