# Compressed reverse frontiers with growing depth, prime-origin leaves, and physical anchor capacities

2026-11-25 JST. Continuation of 558a464aa7a710a45d8af90371088ddfa7be3747 on the user-selected branch. A uniform arithmetic bound on the number of partial reverse history classes, allowing a growing number of very large labels and arbitrarily many smaller selections subject to a cumulative gain budget. A full history reaching its prime origin gives a singleton leaf; other histories give a cut at an actual earlier vertex, not a bound on unrestricted ancestry. A physical-time version bounds the number of earlier large-label anchor states in a current arrival-time bin. Use the capacities for endpoint mass/rank exclusions in the existing medium and high ledgers. No proof of the joint residual or twin infinitude, no Lean compilation.

## 1. Original trajectories and reverse projected arithmetic

Keep X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u), Q=ceil(B/u), m_g=u^(19/4)/ell^4. Use original prime-root gain-stopped paths with original cutoff, full prior events (even those paid in an accounting mask), and actual terminal vertices. All horizons are even, strictly increasing, in [2X-2,7X]. An incoming selected prime q to post-horizon D satisfies q|D or q|(D+2). The prior horizon is D-q+1. For a physical poststate (t,D) the precise congruence is
    q|D+2(t mod 2), t=0 mod 2q if t even, t=q+2 mod 2q if t odd.
For fixed q and D only one of the two parities is possible, since q is odd and cannot divide both D,D+2. Thus the clock lies in ONE progression of period 2q, not two.

Let d(D) be the number of distinct eligible odd incoming labels dividing D(D+2). The product of d distinct primes is at least (d+1)!, and log(D(D+2))=O(u). Hence d(D)=O(u/ell). For q>=Y with log Y~u the uniform number of possible incoming labels is bounded by an absolute D0, say 16 for sufficiently large X. This is an arithmetic candidate bound even if actual predecessor masses are enormous. It does not say that all such labels are actual transitions.

A two-step unrestricted reverse word records the last two actual incoming labels, stopping at a root sentinel if fewer than two exist. At fixed E its number of possibilities is at most
    A2(E)=1+sum_(q|E(E+2), 3<=q<=B prime) [1+d(E-q+1)]
         = O((u/ell)^2),
with candidates outside the horizon domain omitted if necessary. A word determines a prior horizon after at most two reversals. Root-stop words determine an initial horizon, hence a unique original M. Distinct physical times are not included in this projected word.

## 2. A growing-depth compressed reverse frontier

Fix Y=max(5,ceil(B/u)), K=max(1,floor(log u/(16 log 32))), and J=2 max(1,floor(log u/(16 log 2))). Call selected q>=Y large, all other selected labels small for THIS coding only; this is independent of the LOW partition of the medium ledger. Reverse an actual history from a visited horizon E, maintaining the number k of reversed large selections and the cumulative reversed small gain b. Reverse any next small event if b+q-1<=J, otherwise stop with status S without reversing that event. Reverse a next large event if k<K, otherwise stop with status K without reversing it. At the actual original root stop with status R. In particular after reversing the Kth large label one can still reverse small events within the remaining small-gain budget, so all full histories with <=K large selections and total smaller gain <=J end with status R.

Record the even cumulative gains of the k+1 contiguous small blocks, interleaved with the k reversed large labels:
    (status; g0,q1,g1,q2,...,qk,gk),
    k<=K, sum g_i<=J.
A small block can have arbitrarily many labels, but its compressed sum is exact. At each large reversal, the intervening block sum determines its post-horizon, so there are <=D0 choices of q_i; subtract q_i-1 to obtain the next horizon. The entire code determines a boundary horizon D, even if the time and actual small-label words are unknown. For status R this must be 2M-2 of a prime M in [X,2X), and at most one M has that code at fixed E. For S,K all corresponding actual tags visit the same boundary D; no mass bound on that vertex is assumed.

The total number of relaxed codes at any E is at most
    A(Y,K,J) = 3 sum_(k=0)^K D0^k binom(J/2+k+1,k+1).
The binomial counts all nonnegative integer (k+1)-tuples with sum<=J/2. It upper-bounds the actual set without requiring realizability of small blocks or exact clocks. By binom(n,m)<=2^n,
    A <= 6 (K+1) 2^(J/2) (2D0)^K = O(u^1/4).
Indeed the two exponential factors are each <=u^(1/16) eventually, and K+1=O(log u). Both budgets tend to infinity. This gives a pointwise **prime-origin fibre bound** for the restricted full histories:
    # original prime roots reaching E with <=K large events
      and cumulative gain of smaller selections <=J = O(u^1/4).
It also bounds the number of actual reverse classes for ALL original histories reaching E, not just histories that terminate at the root before the cut. The latter property is essential for applying the construction to deep histories, but is a bound on classes, NOT on their masses.

The relaxed set can be enumerated independently: choose each even block sum in its remaining budget; at each resulting horizon, stop with R only if it is an original prime-root horizon, allow S if an incoming small candidate would exceed the remaining budget, allow K if k=K and an incoming large candidate exists, or reverse any candidate large prime if k<K. Omit reverse horizons below 2X-2. This uses no forward reachability test or physical clock. Distinct relaxed R words may determine the same prime origin; counting words rather than distinct roots only enlarges the bound. For actual code R at fixed E the mapping to M is exact.

For comparison with the earlier projected Kraft construction, this is not a bound on the product of all reverse branching factors up to E. It treats even a very long earlier history as an opaque group at the cut, and aggregates all small words by their actual cumulative gain rather than charging each small-label choice. It differs also from the parallel short-clock cumulative-gain reverse-root envelope by cutting arbitrary deep paths and by allowing K of order log u rather than sqrt(log u), with a different small-gain budget. No claim of novelty outside this project.

## 3. Physical anchor bound within a current arrival-time bin

Use the same procedure with Y_phys=max(5,ceil(B/2)), K_phys=max(1,floor(log u/(32 log 256))), and J_phys=J. For a code with k>=1 large reversed selections, retain the actual poststate of the EARLIEST of those k large selections as its physical anchor (D_a,t_a). It is a visited original state, even if the final cut D lies earlier after another small block. The projected code determines D_a, its incoming label, and the horizons of all k large poststates.

Fix an aligned arrival-time bin of width B for the current E. The most recent large posttime lies in the bin enlarged backward by <=3J, because the completed waits of the intervening small block total at most three times its gain. The time between consecutive large poststates going backwards is positive and at most 2B+3J: the wait of the more recent large event is <=2B, and all intervening small events use cumulative gain <=J. At each large post-horizon, the incoming large label fixes a single clock progression by section 1. Therefore for a fixed projected code the number of possible sequences of these physical posttimes, and in particular of possible earliest anchors, is at most
    c_B^k, c_B=1+ceil((2B+3J)/(2Y_phys))=O(1).
Eventually c_B<=4. Thus the number of pairs (projected code, physical anchor) for the whole arrival bin, with k>=1, is bounded by
    3 sum_(k=1)^K_phys (D0 c_B)^k binom(J/2+k+1,k+1)
    = O(u^1/4).
The choices of K_phys,J make this immediate from the previous power-of-two estimate (2D0 c_B<=128<256 eventually). No such physical-time bound is claimed for the k=0 codes; use their projected classes instead. No restriction on the initial path before the anchor, nor on the arrival-time distribution inside the bin. The physical anchor may itself already contain an arbitrarily large earlier basin.

The same argument works for the current bin plus its two neighbors, with a factor three, and for any fixed finite number of neighboring bins. In particular one can compare focal and partner whose current arrival ticks differ by up to a bin width without forcing exact synchronization. This is distinct from counting all arrival bins across H/B, which would destroy the small degree bound.

## 4. Arithmetic frontier endpoint admission

At a common projected pre-horizon E freeze the full original tag list of the pertinent class (medium with its original fixed source cell, or natural high without that cell restriction). Form three partitions, independently:
- the unrestricted two-step reverse word;
- the compressed projected frontier code in section 2;
- for tags with at least one reversed physical-large label, (current arrival bin, physical compressed code, actual earliest-large anchor) as in section 3.

Use each partner cohort's source order. For focal M and partner M', the relative rank is the number of cohort members in (M,M'] when M'>M, or [M',M) when M'<M. Focal need not be in the same cohort. It is at most c for at most 2c partner tags in that cohort.

Let m be a positive integer. For either projected partition with a occupied cohorts, admit rank<=max(1,floor(m/a)) within ANY partner cohort. For the physical partition use only focal's arrival bin and its two neighboring bins, let a count the occupied physical cohorts in their union, and use the same cap when a>0. Each partition gives directed degree at most 2max(m,a), before any other masks. The arithmetic bounds give a=O((u/ell)^2), O(u^1/4), O(u^1/4), respectively. They hold on FULL original endpoint tags, not on an induced residual graph. In particular for m>>u² the total directed degree of all three tests is O(m).

This covers all partner tags in any sufficiently small reverse class, including a root-stop singleton. For a nonroot code, if the total original tag mass at its earlier projected boundary D is <=floor(m/a), every member of this endpoint cohort is admitted, regardless of total mass at E. For the physical cohort the analogous sufficient condition is that the earlier original physical anchor mass is <=floor(m/a), even if its later descendants are a thick physical or projected group. Membership of the actual roots in the earlier state is required, not inferred from arithmetic compatibility. The rank test can cover additional interior portions of larger groups. This provides an actual earlier-fibre thinness implication, not a uniform bound on all earlier masses. The finite audit uses endpoint cohort rank; the thinness implication follows because cohort size is bounded by the original earlier-state mass.

### Medium actual-clock

At a later-hit least-factor band P, take m=m_P=max(1,floor((Q/P)^1/16 m_g/u^.25)). This grows faster than u² uniformly. The inherited per-directed-pair actual endpoint density, including arbitrary earlier quota predecessor choices and any previous masks, is
    c(M,M',E) <= C0 (P/Q)^1/8 b_M(E)/m_g,
where b_M(E) is the actual E-plus-LOW block length. The original partner allocation is unchanged. Thus over every focal incidence at E, the total covered charge is
    O(m_P (P/Q)^1/8 b_M(E)/m_g)
       <= O(u^(-.25) b_M(E)).
All actual blocks on a root are disjoint, and W_all<=3NH. Summing directly yields
    W_reverse=O(NT/u^.25)=o(NT).
No assumption of a physical meeting, comparable focal/partner waits or good occupation density. Both same- and different-history partners can be admitted. In particular all charges whose partner has a bounded FULL history from section 2 are paid; the proof does not require their number at the current E to be estimated empirically.

### High proxy energy

On the original natural high list at E (p>=Q, r>p/sqrt(log p)), take m=m_h=floor(Bu^1.5). Degree O(m_h) directly gives the ordered energy of admitted pairs with both tags retained:
    E_reverse << m_h sum_E r(E) W_J(E)
               << Bu^1.5 NT = O(T²Bu^.75)=o(T²Bu).
This covers both synchronous and asynchronous ordered products; a symmetric union would cost at most a factor two because r(E) is common. Union with all earlier absolute exclusions, with priority to avoid double counting. No claim that the whole high energy falls by this bound, only that these specified new pair products can be removed at the stated cost.

In addition the projected or physical frontier code (without absolute E, using the recorded word/status) can define one of the previous disjoint static history partitions for the weighted-membership local window theorem of 558a464. That gives a separate local graph cover for matching codes at common endpoints; no number-of-classes loss. It is not included in the present audit or needed for the direct degree proof.

## 5. Reproducible finite audit

Derived standalone research/min_prime_root_reverse_frontier_audit.mjs. Latest code commit dc035c51fc0916123a537ef29598ace91da045e2, blob 941631435a967e7ded31d70da6c5dd04f74e7654, exact remote readback. Commands:
    node research/min_prime_root_reverse_frontier_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_prime_root_reverse_frontier_audit.mjs --crt-stress --gain-stress --window-stress --reverse-stress 256 1024 4096 16384 65536 262144

Executed actual audit function in available ECMAScript runtime, not a separate Node process. Initial version 8 runs (analytic/concurrent, X256..16384), then six runs (analytic/concurrent/combined stress at X65536,262144). Final version permits the last small block after K large selections, verifies per-word physical clock capacities and compares independent arithmetic enumeration with actual codes. All 18 final runs (analytic, concurrent, combined four stress, six X) pass. Other final modes not rerun. Independent relaxed enumeration on up to 32 early full projected-state control groups and 32 largest natural high groups; not all endpoints exhaustively enumerated. Full actual code extraction at all tested high endpoints, medium residual endpoints, and controls. Check projected reverse arithmetic, exact small-gain budgets, stop conditions, prime-origin equality and injectivity, physical time differences/progression and actual anchor membership, per-word and per-bin anchor counts, directed degree, actual fractional medium partition, exact ordered high priority partition. High priority is after previous direct projected rank, global local-window, and exact-factor local-window masks ONLY (not the full cumulative hybrid). Finite analytic caps cover all retained quota charges before new masks, so no nonempty analytic medium residual exercised. Diagnostic K=2,J=8,Y=max(5,ceil(B/8)); stress K=3,J=16,Y=max(5,ceil(B/16)); physical diagnostic Y same as projected. These thresholds do not illustrate the limiting Y_phys=B/2 or growing K. Diagnostic medium m=2 or8, high m=4 or8; the degree bound uses max(m,a) exactly. Logs and inherited fractional weights use finite tolerances; no formal Lean proof.

At largest normal concurrent X262144:
- 24490 actual endpoint tags coded (cached, two compressed signatures each), 2418 root-leaf occurrences summed over both signatures, 2205 physical anchor memberships checked. Largest occupied cohort counts for two-step / compressed projected / physical in one bin =7/8/7; maximum observed projected root-leaf count at a tested endpoint3. These are counts on the sampled original lists, not general root-fibre maxima.
- 4070 independent actual-code inclusion checks, 2994 relaxed words and210 relaxed R words summed over both configurations and control endpoints; largest relaxed R-word count7, largest total relaxed words111. Distinct origins could be fewer. Analytic largest 4212 checks,414 relaxed words,31 relaxed R words, largest R2/total15. Combined stress largest 4070 checks,50430 relaxed words,3338 relaxed R words, largest R101/total1670, observed actual root-leaf maximum4.
- Ordinary medium previous residual114.315830555 (never62.518518519), new deletion ZERO; unchanged. All tested normal medium residual windows have zero additional payment. Combined stress largest medium64.019534259 ->62.625248545, pays1.394285714 via two-step word ranks, never12.222222222 unchanged. Thus this is not a numerical advance on the normal never-meeting obstruction.
- Normal natural high residual before new mask83476671; additional ordered energy2616100 =1612819 two-step+697590 projected compressed+305691 physical anchor (priority); async2146704. Residual80860571. At X65536 extra322265 (async219577), X16384 extra20299, X4096 extra986. Combined stress largest extra4085547 (async3485057), residual57834193. These are additional over the previous direct and local projected rank masks in the isolated natural-high ledger; not the complete high residual. The arithmetic refinements are nonvacuous even with arbitrary-size earlier groups.

## 6. Remaining proof task

The code count does not pay the deep origin fibres whose early boundary mass and relative ranks are all large. The new restricted prime-root bound gives an exact arithmetic subset that can be excluded independent of ancestry mass; the other leaves identify actual boundary groups. A next substantive target is to bound the formation of those boundary groups or to prove a contraction of their remaining mass through successive disjoint reverse cuts. Reapplying the code count alone does not establish such a contraction: many original roots may already share a physical anchor. In particular no general bound on the never-meeting medium residual or on the full synchronous/asynchronous high residual follows. The required joint estimates on the same unbounded dyadic windows and twin-prime infinitude remain OPEN. Main unchanged.
