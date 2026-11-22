# A166944 squarefree wheel: causal light cone, late-event energy, and a cancellation-preserving correlation split

Date: 2026-11-23 JST. Child [Issue #3](https://github.com/tara-sooo/A166944-Lean/issues/3), parent #1. This is a continuation of `2026-11-23-cross-prime-increment-dispersion-and-periodic-prefix.md` on branch `research/issue-3-cross-prime-correlation`, originally based on `bd180e3de0fe6e12cc3c3ea25d65a985445344eb`.

**Status.** Lemmas 1–4 below are elementary mathematical derivations for the squarefree clipped *original parity-specific GCD* recurrence, not Lean-checked declarations. Finite diagnostics in Tables 1–3 were run from the C++17 files listed below, and selected traces were independently checked with literal stepwise gcd. The required **uniform growing-prime correlation and mean-growth estimates remain OPEN**. Neither twin-prime infinitude nor `OeisA166944.conjecture` is proved.

## 1. Scope and exact objects

Fix even `X>=256`, `B=ceil(sqrt(7X))`, and the common odd-target interval

    V={v odd: X<=v<U}, U=2X+floor((3B+7)/2)+5.

Write `s=v+2`, `K(v)=floor((7v-1)/4)`, and `H(v)=K(v)-s=floor((3v-9)/4)`. For prime `q<=B`, let `L_q` be the squarefree product of odd primes up to q, and `L_{q^-}` the immediately previous prefix. At seed `D_L(s)=2v-2`, for `n>s`:

    d_L(n) = gcd(L, gcd(n,   D_L(n-1)-1))        (n even),
           = gcd(L, gcd(n-2, D_L(n-1)+1))        (n odd),
    D_L(n)=D_L(n-1)+d_L(n)-1.

For a fixed `v` define the untruncated-at-relative-time increment difference

    a_{q,t}(v) = [d_{L_q}(s+t)-1] - [d_{L_{q^-}}(s+t)-1], t>=1,

and the natural-cutoff signed stage growth

    delta_q(v) = sum_{1<=t<=H(v)} a_{q,t}(v)
               = G_q(v)-G_{q^-}(v).

The previous paper's *future-prime centered weight* is

    A_q(v)=W_{>q}(v)-4J_q,
    W_{>q}(v)=sum_{q<p<=B, p>=11 prime, p|v(v-1)(v-3)(v-5)} p,
    J_q=#{p prime: max(q,10)<p<=B},
    D_q=sum_{v in V} delta_q(v)*A_q(v).

The previous polynomial-incidence lemma `W_{>q}(v)<=13B` on `V subset [X,3X)` and `4J_q<=4B` imply the convenient *single-sided* centered bound `|A_q(v)|<=13B` (because `W>=0`, so `|W-4J|<=max(W,4J)`). This uses `X>=256` and `U<3X`.

## 2. Lemma 1: a universal prime-activation light cone (PROVED ON PAPER)

For **every** odd canonical seed `v>=7`, odd squarefree wheel and relative step `t>=1`, its deficit before the step is

    Z_before = 2(s+t-1)-D_L(s+t-1)
             = 6+2(t-1)-sum_{u<t}(d_L(s+u)-1),
    0<=Z_before<=2t+4.

Nonnegativity follows inductively from `Z_next=Z_before+3-d_L(n)`, the parity-specific gcd divisor of `Z_before+3` at even `n`, and of `|Z_before-3|` at odd `n`. In the odd case, `Z_before` is even, so `Z_before<3` means 0 or 2 and still `d_L(n)<=Z_before+3`.

If `n` is even, any prime dividing `d_L(n)` divides `Z_before+3<=2t+7`. If `n` is odd, every prime dividing `d_L(n)` divides `|Z_before-3|<=max(3,2t+1)<=2t+7`. So **no prime p>2t+7 can enter the increment at time t**.

The `q` and `q^-` prefixes agree until the first q-containing event. Their first possible difference must multiply an increment by q. Therefore

    BOXED: if 2t+7<q, then a_{q,t}(v)=0 for EVERY odd seed v.

This is an all-prime/all-start theorem independent of the enormous primorial `L_q`; no probabilistic model or CRT period is used.

## 3. Lemma 2: unconditional late-time activity is funded by growth energy (PROVED ON PAPER)

For either squarefree prefix, let `g_L(v)=G_L(v)` be its nonnegative growth up to natural cutoff. As proved in the earlier `2026-11-22-squarefree-sqrt-wheel-mean-reduction.md`, every nonunit event at relative time `t` satisfies `t<=3*g_L(v)` (each interevent gap <=3 times its own increment excess).

Hence for any integer `T>=1`:

    sum_{T<=t<=H(v)}(d_L(s+t)-1)
      <= g_L(v)*1_{g_L(v)>=T/3}
      <= (3/T)*g_L(v)^2.

Using `|a_{q,t}| <= (d_{L_q}-1)+(d_{L_{q^-}}-1)` and summing:

    BOXED: sum_{v in V} sum_{T<=t<=H(v)} |a_{q,t}(v)|
           <= (3/T)*sum_{v in V} [G_q(v)^2+G_{q^-}(v)^2].

This is an exact tail-moment bound, but its RHS includes **new-wheel** growth energy. It does not estimate that energy by old-wheel energy; making such a substitution would silently assume the difficult part of the problem.

## 4. Lemma 3: cancellation-preserving time cutoff + CRT / short-interval bounded variation (PROVED ON PAPER)

Choose integer `0<=T<=min_{v in V}H(v)=floor((3X-6)/4)`. Define the **signed horizon difference**, not a sum of absolute time increments:

    F_{q,T}(v) = sum_{1<=t<=T} a_{q,t}(v)
               = D_{L_q}(s+T)-D_{L_{q^-}}(s+T).

This is periodic in `v mod 2L_q` by the earlier universal shift-conjugacy. Write

    S_q = sum_{q<p<=B, p>=11 prime}p,
    M2_q(X)=sum_{v in V}(G_q(v)^2+G_{q^-}(v)^2),
    R_{q,T}=sum_{r odd mod 2L_q}|F_{q,T}(r)|,
    BV_{q,T}=|F_{q,T}(v_last)|
              +sum_{v, v+2 in V}|F_{q,T}(v+2)-F_{q,T}(v)|.

For every `p>q`, the centered four-residue sequence `c_p(v)=p*1_{p|P(v)}-4` has zero sum over a complete p-cycle of consecutive odd integers and every *contiguous* partial sum is bounded in magnitude by `4p`.

(a) **CRT version:** On each odd residue class modulo `2L_q`, `F_{q,T}` is constant; since `gcd(p,2L_q)=1`, the p successive occurrences exhaust the residues modulo p. The centered p-weight sums to zero over each complete p-block and has a partial-block error <=4p. Thus

    |sum_{v in V} F_{q,T}(v)*A_q(v)| <=4*S_q*R_{q,T}.

(b) **Short-interval version, independent of primorial size:** Abel/discrete summation by parts on the *consecutive odd v values* and the same partial-sum <=4p gives

    |sum_{v in V} F_{q,T}(v)*A_q(v)| <=4*S_q*BV_{q,T}.

For the remaining tail `delta_q-F_{q,T}=sum_{t>T}a_{q,t}`, Lemma 2 with threshold `T+1`, and `|A_q|<=13B`, yield the following **unconditional balanced-time bound**:

    BOXED: |D_q| <= 4*S_q*min(R_{q,T},BV_{q,T})
                      + (39*B/(T+1))*M2_q(X).

The `BV` option is genuinely independent of `L_q` and remains applicable when `L_q` greatly exceeds the dyadic interval, so the CRT period never completes. The q-dependent time slice lets one seek a small `BV_{q,T}` or `R_{q,T}` without paying for arbitrary subsequent activity. Unfortunately the measured `BV` by itself is not small enough to finish the desired `O(X*B^2/log B)` global bound; and the second-moment term remains unproved. This is a precise *reduction with two explicit dynamical inputs*, not the missing upper bound.

**Why `F_{q,T}` rather than `sum_{t<=T}|a_{q,t}|`:** The latter loses cancellations when the enlarged/new paths split then rejoin, or when the signed difference reverses before cutoff. Lemma 3 retains all cancellation before T and pays the late activity through a separate tail moment.

## 5. Reproducible finite diagnostics

The C++17 [time-sliced audit](time_slice_activity_audit.cpp) computes both capped parity-specific trajectories by *exact first-event jumps*, merges their event logs by relative time, and checks `sum_t sum_v a_{q,t}(v)A_q(v) = D_q`, the causal light cone, and final/new/old total-growth conservation. It also records the `BV` of endpoint and truncation `T=2q` as a proxy for short-interval regularity. For the shown X/q:

| X | q | first active t | last active t | `D_q` | sum_t abs(sum_v a_t A_q) | sum_v,t abs(a_t) | sum_v abs(delta_q) | BV of terminal delta |
|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| 1024 | 59 | 30 | 139 | 0 | 11,352 | 264 | 0 | 0 |
| 4096 | 11 | 3 | 114 | 83,430 | 191,014 | 13,036 | 10,932 | 8,196 |
| 4096 | 59 | 27 | 431 | 13,428 | 817,680 | 16,446 | 14,418 | see program |
| 4096 | 97 | 45 | 341 | -150,630 | 733,626 | 16,148 | 12,108 | 5,364 |
| 4096 | 149 | 71 | 281 | -1,920 | 16,896 | 1,056 | 120 | 120 |

The [episode audit](coalescence_episode_audit.cpp) independently scans the same event trajectories and identifies every return of the horizon difference to zero. At X=1024,q=59, precisely **one** of the 580 odd starts is dynamically affected, **v=1209**: a single completed excursion lasts 109 relative steps, its maximum horizon difference magnitude is 72, and the *terminal difference is identically zero for all 580 seeds*. The unweighted time-slice L1 is still 264 and signed time correlations have L1 11,352. **Thus paying time-slice absolute values can assign cost to a prime insertion whose total terminal cost is exactly zero.** At X=4096,q=149, only two of 2,179 starts differ at all; the time-slice L1 is 1,056 versus terminal L1 of 120 (8.8-fold loss).

The [independent infinite-wheel event-jump scanner](infinite_wheel_activity_audit.cpp) reproduces the earlier exact all-canonical-residue stop times for q=7,11,13,17: 48,114,157,239. It now exhausts all `L_19=4,849,845` canonical odd residues in about 2 seconds on the tested environment and obtains

    q=19, full seeds=4,849,845,
    max safe-arrival relative time=388 at v=8,264,687,
    max infinite growth=568 (same v), 2 seeds have T>19^2=361.

The extreme witness was independently verified by the literal original-parity clipped gcd for t=1,...,419: at t=361 growth=552 and not absorbed; at t=388 growth=568 and both neighbor gcds with L=4,849,845 are 1. Its last increments are (t,d)=(360,7),(364,3),(365,3),(388,13). This **refutes** the tempting universal candidate `T_q<=q²` already at q=19, though subquadratic eventual stopping is not thereby refuted. The q=23 scanner additionally samples 2,000,000 (not all) of its 111,546,435 odd residues: max observed T=425 and growth=684. No uniform-in-q termination bound follows from finite tests.

Build:

    g++ -std=c++17 -O3 -Wall -Wextra research/time_slice_activity_audit.cpp -o /tmp/time_slice_audit
    g++ -std=c++17 -O3 -Wall -Wextra research/coalescence_episode_audit.cpp -o /tmp/episode_audit
    g++ -std=c++17 -O3 -Wall -Wextra research/infinite_wheel_activity_audit.cpp -o /tmp/infinite_wheel_audit

Runs:

    /tmp/time_slice_audit 1024 59
    /tmp/time_slice_audit 4096 11
    /tmp/time_slice_audit 4096 97
    /tmp/time_slice_audit 4096 149
    /tmp/episode_audit 1024 59
    /tmp/episode_audit 4096 149
    /tmp/infinite_wheel_audit 17
    /tmp/infinite_wheel_audit 19
    /tmp/infinite_wheel_audit 23 2000000    # random sample, not exhaustive

## 6. Exact next open target

The balanced-time inequality isolates two unresolved dynamic estimates: **(i)** the actual *short-interval first-difference variation* of `F_{q,T}(v)` rather than primorial-wide phase variation, and **(ii)** the second-moment growth tail `M2_q(X)`. Choosing `T` on the scale of q or q logq is plausible numerically but no uniform theorem is known. The q=19 explicit `T>q²` witness warns against guessing a convenient stopping bound.

An alternative renewal approach is to bound **uncompleted** horizon-difference excursions at the cutoff, preserving cancellation from completed excursions. Mere time-wise activity sparsity and CRT modular periodicity cannot force weighted equidistribution when `L_q>>|V|`; an arbitrary periodic profile can correlate perfectly on a shorter interval. Any successful growing-q argument must use specific GCD excursion geometry, local variation or a directly proved growth-moment bound beyond periodicity alone.

These are new paper-level intermediate bounds and diagnostics, not an asymptotic proof of E or of the original problems. No Lean theorem was compiled during this checkpoint.
