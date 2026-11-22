# A166944 squarefree wheel: small-event cancellation of active large-prime clocks, exact token ledger, and a weaker winning-clock moment target

Date: 2026-11-23 JST. Research scope: [Issue #4](https://github.com/tara-sooo/A166944-Lean/issues/4) (parent #1), branch `research/issue-4-terminal-survivor-positive-budget`. Builds on `2026-11-23-composite-prime-clock-and-one-tail-event-bound.md`. The algebraic lemmas are complete **paper** arguments, **not Lean-kernel checked**; the measurements are finite original-parity clipped-squarefree-GCD computations. Neither twin-prime infinitude nor A166944 has been proved.

## 1. Definitions and an exact small-event disarming lemma

For even X>=256, B=ceil(sqrt(7X)), an odd start X<=M<2X, let s=M+2, K=floor((7M-1)/4), and C(s)=2M-2. At clock n>s use the original parity GCD

    g(n,C)=gcd(n,C-1)       if n even,
           gcd(n-2,C+1)     if n odd;
    d(n)=gcd(L_B,g(n,C)),   C'=C+d(n)-1,

where L_B is the squarefree product of odd primes <=B. At a plateau state C define the *active-prime set*

    A(C)={odd prime q<=B: q | (C-1)(C+1)}.

An active prime has a parity-restricted next q-clock in at most 2q steps; **it need not reach that clock**, because an earlier event may change C.

**Lemma D1 (unconditional paper proof).** Suppose the next nonunit event has odd squarefree increment d>=3 and a prime q is active before it with q>d+1. Then:

- if q|C-1, q is absent from BOTH C'-1 and C'+1;
- if q|C+1 and d>=5, q is absent from BOTH C'-1 and C'+1;
- if q|C+1 and d=3, q becomes active only on C'-1 (plus-to-minus switch).

Proof: C'=C+d-1. If q|C-1, then C'-1=d-1 and C'+1=d+1 mod q; both lie strictly between 0 and q. If q|C+1, then C'-1=d-3 and C'+1=d-1 mod q; for d>=5 both lie strictly between 0 and q, and for d=3 the first is zero. The first and second neighbor sets are disjoint because q is odd. Thus a *single smaller intervening event* kills the waiting q-clock except for a d=3 side-switch. If a second event with d'+1<q occurs without q firing, that exceptional switched q is then killed. This only controls one activation episode: q can be reactivated by a later event.

**Lemma D2 (consumption of a firing prime).** If q|d at an event, q>=5 is absent from both neighbors after the event. If q=3, the only exception is an odd-time event: 3|C+1 before the event and 3|C'-1 afterwards. Proof: d=0 mod q, C'=C-1 mod q; inspect C'±1 on each side. A new event may later switch the active 3 back to the plus side, so *do not* claim that one q=3 activation can fire at most twice globally.

## 2. Exact activation-birth / cancellation / hit ledger

For a single trajectory with event states C_0,C_1,...,C_E, put A_i=A(C_i), b_i=|A_i\A_(i-1)|, and v_i=#q in A_(i-1)\A_i which **do not** divide the event increment d_i (lost without firing). Let omega(d_i) be the number of distinct prime factors of d_i; h_i=1 if the event clock is odd and 3|d_i, otherwise 0. D2 implies that exactly omega(d_i)-h_i firing primes leave the active set at event i, so the elementary set-cardinality telescope gives

    BOXED: sum_i omega(d_i)
       = |A_0| + sum_i b_i - sum_i v_i + sum_i h_i - |A_E|.  (L1)

This is an exact identity for the original process. It is NOT an independence or branching assumption. Since every nonunit event contains at least one prime,

    E_B(M) <= |A_0| + sum_i (b_i-v_i+h_i) - |A_E|.          (L2)

The sum of initial active-prime counts over all starts is elementary:

    sum_(odd M in [X,2X)) |A_0(M)|
      = X*sum_(odd p<=B prime)1/p + O(pi(B))
      = O(X log log B).

Thus a **sufficient but OPEN** compensated-creation estimate is

    sum_(M,i) (b_i-v_i+h_i) = o(X B).                       (L3, OPEN)

Together with (L2), this gives E_total=o(XB) and, by the earlier unconditional clock/horizon bound W_X<=3X+4B*E_total, gives W_X=o(X²) and infinitely many twin primes. L3 is nearly equivalent in difficulty to event-count control, but it isolates the arithmetic cancellation term v_i that is invisible in raw activation counts. Directly bounding sum b_i alone is too crude (see measured ratios).

## 3. A new per-prime *winning-clock* sufficient hypothesis

Let H_q(X)=sum over starts M of the number of their FULL B-wheel nonunit events whose increment d_i is divisible by q. These are **successful clocks**, not mere activations. Every event contributes to at least one H_q, hence

    E_total(X) <= sum_(3<=q<=B prime) H_q(X).               (L4)

The following explicitly weaker-than-1/q-equidistribution uniform moment would suffice for infinitely many twin primes:

    WINNER HYPOTHESIS (OPEN):  H_q(X) <= C*X*sqrt(B)/q
    for ALL odd prime q<=B, with an absolute C.

Indeed sum_{q<=B}1/q=O(log log B), so E_total=O(X sqrt(B) log log B)=o(XB), which implies W_X=o(X²). More generally sqrt(B) can be replaced by B^(1-delta) for any fixed delta>0. This allowance is essential since the finite q=3 hit count is substantially larger than a small fixed constant times X/3; the hypothesis permits a factor sqrt(B) of loss. No such uniform estimate has been proved.

D1 suggests an attack on this bound: decompose q's **activation episodes**, and require each episode to survive the competition from earlier events. For a waiting q>d+1, an earlier event of size d>=5 cancels it immediately; d=3 can grant at most one extra competing event if the initial side was C+1. This is a *modular disarming theorem*, not a probabilistic assertion. To turn it into a uniform H_q mean bound, one still needs arithmetic dispersion of the adaptive first-clock races over M and across dyadic q-bands. The previously audited failure of naive uniform plateau phase is relevant: conditional actual-clock phases are not independent or uniform.

## 4. Finite exact audit

Source: `research/active_clock_survival_audit.cpp`. Built with

    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/active_clock_survival_audit.cpp -o /tmp/active_clock_survival_audit
    /tmp/active_clock_survival_audit 4096 16384 65536

The program uses exact next-prime-clock events, independent literal-step GCD checks on odd 7<=M<=119 and cap 41, full historical event/growth regressions, per-start equality (L1), and per-event D1/D2 checks. All three scans PASS. The `smallKills` count is the number of active q>d+1 lost after a preceding smaller event; `unhitDeaths` counts ALL active primes that disappear without firing. `births` records primes newly dividing C'±1 after an event. `allPrimeHits` sums omega(d_i) and may exceed event count for composite increments.

| X | B | starts | events E_total | initial active tokens | births | non-firing deaths | small-event kills | all prime hits | max_q q H_q/(X sqrt B) |
|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| 4096 | 170 | 2048 | 29349 | 5781 | 54421 | 31355 | 27683 | 29884 | 0.65263178 (q=3) |
| 16384 | 339 | 8192 | 171428 | 25096 | 354156 | 210084 | 186771 | 175707 | 0.66940278 (q=3) |
| 65536 | 678 | 32768 | 795689 | 107744 | 1806563 | 1123623 | 1017497 | 816075 | 0.53801895 (q=3) |

In all three audited finite windows, (i) >1.8 newly active q tokens were born per event; (ii) roughly 58%–62% of born tokens never fired and were eventually canceled; (iii) roughly 88%–91% of non-firing deaths were explained by the one-step q>d+1 small-event cancellation mechanism; (iv) max H_q-normalized witness was q=3, below 0.67. The measured q=3 ratio itself grows in unnormalized p H_p/X between some scales, illustrating why an exact fixed-C/p model is not warranted. No population/asymptotic conclusion follows.

The finite audit happened to have |A_E|=0 at all tested starts. L1 retains the terminal-active term because it is not universally zero at arbitrary cutoffs. Do not infer that every starting M will reach a twin-prime terminal state at all scales.

## 5. Status and next attack

- **Paper proved, not Lean kernel checked:** D1, D2, L1/L2/L4 and their conditional consequences, and arithmetic initial-token mean.
- **Finite tested:** D1/D2/L1, q hit counts and regressions through X65536.
- **Open:** L3, the per-prime WINNER HYPOTHESIS, E_total=o(XB), twin-prime infinitude, and original strict-record A166944 conjecture.

The most promising specific next estimate is a **dyadic clock-survival estimate for newly activated q in [Q,2Q)**, conditioned on the state at its activation and on smaller intervening events. It must handle possible later q reactivation separately and preserve the special q=3 odd event. The measured cancellation fraction shows that tracking all activations as actual q hits introduces a large overcount; a successful argument should explicitly subtract the forced canceled clocks.
