# A166944 reset-prime rigidity and disjoint excitation-recovery budgets

Date: 2026-11-22 JST. **Status:** new elementary paper theorems with independently executed exact-gcd audits and existing Lean first-hit inputs. No new Lean compilation. No proof of Cap B or infinitely many twin primes.

This extends [two-speed reset and prime burning](2026-11-22-two-speed-reset-prime-fuel.md), using [ReplayOffset210.lean](../A166944/ReplayOffset210.lean), [FirstHitArithmetic.lean](../A166944/FirstHitArithmetic.lean), and the actual A166944 gcd recurrence. Earlier [frozen-wheel constructions](2026-11-22-frozen-wheel-phase-budget-and-neutral-paths.md) prove that arbitrary finite reset-only chains are locally realizable from synthetic starts. The results below are exact **necessary accounting constraints**, not a universal escape proof.

## 1. Large events from X=0 or X=6 are PRIME, apart from exactly three composite possibilities

For an exact first-hit path, let X(s)=2s-D(s) be either 0 or 6 and let r=s+g be the next nonunit event, with odd e=d(r)>=9. The previously established two-speed identity gives

    r even: 2g+X(s)+1 = k e;
    r odd:  2g+X(s)-5 = k e;
    k in {1,3}, X(r)=(k-1)e + (0 if r even else 6).

**Theorem 1 (reset-prime rigidity).**

    k=3 => e is prime.
    k=1 => e is prime, or e in {9,15,25}.
    In particular, e>=27 => e is prime.

**Proof.** If e is odd composite, let q>=3 be its least prime factor, e=q*h, with h>=q and h odd. Exact first-hit periodicity gives g<=2q, because an index congruent to r mod 2q would have triggered earlier if g>2q. In the k=1 case, both parity formulas yield 2g>=e-7, hence e<=4q+7 and h<=4+7/q. For q=3, the only odd h>=q allowed are 3 and 5, giving e=9 or15. For q=5, only h=5, giving e=25. For q>=7, h>=q>4+7/q, impossible. In the k=3 case, 2g>=3e-7>=9q-7>4q, a direct contradiction. QED.

The exception set is **locally sharp** under exact gcd first-hit tests:
- (s,C)=(17,28) first hits at r=18, e=9, g=1;
- (s,C)=(26,46) first hits at r=30, e=15, g=4;
- (s,C)=(141,276) first hits at r=150, e=25, g=9.

The e=25 phenomenon also occurs on the authentic A166944 trajectory; the e=15 witness is a synthetic local state, not asserted attained.

## 2. Excitation can NEVER be cleared by proper-factor events alone

Use the **per-index** pre-hit offset x=2(n-1)-D(n-1)>=0. The gcd increment e at n has cofactor

    U=x+3 (n even), or U=x-3 (n odd),

and the exact offset update is x_after=x+3-e.

If x>=8 and a nonunit event has e<U with U>0, then since e and U are odd and e|U, the quotient U/e is an odd integer >=3. This is a **proper-factor event**, not a primitive hit. Direct substitution gives

    x_after-6 >= (2/3)*(x-6).                         (A)

For unit steps x_after=x+2, so x-6 increases. In particular, once x>6, no sequence consisting only of units and proper-factor events can reach x<=6.

Now a k=3 event of size p>=9 from X(s) in {0,6} leaves X(r)=2p or 2p+6; by Theorem 1, p is PRIME.

**Theorem 2 (mandatory primitive discharge).** Every later return to X in {0,6} after such an excitation necessarily passes through a first **primitive event** f=U>0 (that event itself returns to 0 or 6). All intervening nonunit events before the first primitive are proper-factor events. Thus the intervals from an excitation to its first primitive discharge are **pairwise disjoint** across a first-hit path, aside from harmless endpoints.

This sharpens the earlier vague alternative “primitive or proper detours”: proper detours may delay and diminish the offset but can NEVER themselves complete the return.

## 3. A quantified, NON-DOUBLE-COUNTING discharge budget

For a completed excitation, write p for its initial (prime) increment; its starting offset x0 is 2p or 2p+6. Suppose m proper-factor hits occur before the first primitive hit f, at index b. Let a be the excitation index, and let

    H=D(b)-D(a)

be the **growth after the excitation**, including all proper detours and the closing primitive f, but not the initial excitation increment. Put y0=x0-6 >=2p-6>0.

By (A), across m proper events and arbitrary intervening units,

    x_before_f - 6 >= (2/3)^m*y0 >= (2/3)^m*(2p-6).

At its primitive hit, f=x_before_f+3 (even closing event) or x_before_f-3 (odd closing event). Therefore

    boxed: f >= 3+(2/3)^m*(2p-6).                     (B)

Every proper event has odd increment >=3 and growth >=2, and the final primitive contributes f-1. Thus

    boxed: H >= 2*m+(f-1)
             >= 2*m+2+(2/3)^m*(2p-6).               (C)

In particular this yields an entirely integer-form logarithmic requirement

    boxed: H >= 2+ceil(log_2(2p-6)).                  (D)

For (D), put a1=(2/3)^m(2p-6). Then 2p-6=(3/2)^m*a1 <=2^(2m+a1), using a1<=2^a1 for a1>0. Since H-2>=2m+a1 by (C), we have 2p-6<=2^(H-2), proving (D).

**Nonoverlap theorem.** For ANY finite path segment [u,v], select all fully completed excitation-to-first-primitive intervals with both endpoints in [u,v]. Since their open-to-close growth intervals are disjoint, their charges can be summed ONCE:

    sum_completed [2*m_i+2+(2/3)^m_i*(2p_i-6)]
          <= D(v)-D(u).                                (E)

This is an actual joint growth-capacity inequality, unlike a proposal to add overlapping p-reuse costs arbitrarily. It applies to all genuine or artificial exact first-hit trajectories, not only canonical records. The still-open excursions at v cannot be charged for a future primitive that has not occurred.

## 4. Exact DIRECTIONAL prime-recharge table, strengthening the prior p-1 bound

Let p>=5 be an odd prime factor of the increment at one event, and again at a strictly later event. Let C' be the horizon after its first use, H be the pre-horizon of the later use, and R=H-C' be the intervening growth (even, nonnegative). Event orientation gives:

    First use parity     Later use parity     minimum R
    even                 even                 p+1
    even                 odd                  p-1
    odd                  even                 p+3
    odd                  odd                  p+1

**Proof.** After an even first use, C' ==0 (mod p); after an odd first use, C'==-2 (mod p). The later pre-horizon H must be +1 modulo p for an even hit, or -1 modulo p for an odd hit. Solve these four congruences for the least nonnegative EVEN R. Since p is odd and >=5, the four least solutions are exactly the table.

This strictly refines the previously Lean-checked generic reuse-growth minimum p-1. The entries are arithmetic lower bounds, not a claim that all four values are always attained by realizable paths.

**Combining recharge with disjoint excursion growth.** If an excitation of prime increment p is closed by a primitive event f divisible by that SAME p, all growth strictly between the two events is from the intermediate proper events, so

    proper_growth >= directional_recharge(p, opening parity, closing parity).
    H >= proper_growth + (f-1) >= directional_recharge + (f-1).

This is genuinely additive **within the excursion**, because the recharging events and the final primitive event are distinct. Together with (C),

    H >= max( 2*m+2+(2/3)^m*(2p-6),
              directional_recharge+(f-1) )            (F)

when p|f. There is **no sum** of the two right-hand sides; that would double-count the proper detours.

**Sharp genuine synthetic-canonical witness:** from M=101119 (actual prime pair 101117,101119), use the exact locally replayed synthetic canonical-shaped trajectory. At odd opening index a=101311 the excited prime is p=13. One proper hit of increment 17 follows (growth 16), then at even index b=101322 a primitive increment f=39 occurs. Odd->even demands exactly p+3=16 and this is met; f adds 38 further growth. The entire discharge costs H=54=16+38. This is an exact run from the synthetic canonical-shaped state, NOT claimed to be attained in the global recurrence from a(1)=2).

## 5. An INDEPENDENT index-time budget for excitation primes

Any k=3 excitation p>=9 from a low-offset state has gap

    2g >=3p-7.

The incoming gaps for different excitation events are disjoint in time. Therefore, on any finite interval [u,v], with all excited events directly preceded by low-offset event states within [u,v],

    boxed: sum_excitation (3p_i-7) <=2*(v-u).          (G)

In particular if all p_i>=P>=9, their number is bounded by floor(2*(v-u)/(3P-7)). On a canonical cutoff interval u=M+2, v=K=floor((7M-1)/4), any SINGLE excitation also obeys

    p <= floor((2*(K-(M+2))+7)/3) <= (M+1)/2.          (H)

Thus “excitation p>M/2 requires immediate proper detours under old-record cap M” is a false route INSIDE this canonical cutoff: such huge p cannot fit into its index span in the first place. This is a useful negative check on proposed amortizations.

Unlike (E), which uses **horizon growth**, inequality (G) spends **index time**. A future mixed dual budget may couple both resources without counting either twice.

## 6. Audit, sharpness and precise remaining gap

The [standalone exact recurrence audit](reset_prime_excursion_budget_audit.py) performs:
- the locally sharp e=9,15,25 composite-reset gcd witnesses;
- the authentic original recurrence through n=2,500,000 (249 nonunit events after n=2): among 46 low-reset to large-hit transitions, 36 are k=1 and 10 are k=3; there are 7 composite e=9 and 3 composite e=25, none e=15 on this finite prefix;
- nine completed excitations before n=2,500,000 and one still open (p=11), testing (B)-(E);
- all 125 repeated-prime-factor uses (p>=5), including 14 cases saturating the directional table in full actual history;
- synthetic canonical-shaped M=367,100549,101119 and the exact odd->even same-p excursion p=13, f=39, proper growth 16.

The finite audit passed locally; source is committed and independently read back. The paper deductions above have **not** been translated into a Lean kernel proof.

**OPEN:** These constraints do NOT force the terminal BAD crossing to disappear. In particular, previously constructed artificial inert-wheel paths can have arbitrarily many distinct prime k=1 resets and **zero excitations**: (C)-(E) give no cost for them beyond ordinary event growth. Moreover repeated prime-fuel recharge can overlap with an excursion's proper-growth payment; equation (F) correctly uses max rather than improperly adding overlapping costs.

The actual missing theorem is a **global first-hit density/prime-admissibility obstruction for long k=1 reset chains from attained twin-prime starts**, together with a nonoverlapping allocation of any remaining repeated-prime demands against (E)-(G). The new theorems supply sharp structural restrictions and a sound partial amortization, but NO proof of Cap B, infinite return, or twin-prime infinitude.
