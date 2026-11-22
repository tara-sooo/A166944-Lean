# A166944: GOOD-parent → BAD-child prime-clock activation gates

Date: 2026-11-22 JST. **Status:** elementary paper deductions and exact original-gcd audits. **The intended global GOOD→BAD prohibition was NOT proved.** Neither Cap B nor twin-prime infinitude is proved here; no new Lean compilation.

Sources: [canonical GOOD genealogy and exact relay F](2026-11-22-record-genealogy-quiet-parent-high-reuse.md), [terminal BAD factor clock](2026-11-22-terminal-cutoff-factor-short-crossing-dichotomy.md), [last event skeleton](2026-11-22-bad-last-hit-clock-skeleton-and-twin-depth.md). Independent verifier: [two-generation q activation audit](a166944_two_generation_bad_q_audit.py).

## 1. What the two-generation congruence does (and does not) say

Let `m` be a *genuinely attained* (or an artificial canonical-shaped) parent with GOOD cutoff, and let `g=G(m)>=0`. Its next canonical child is

    M=2m-1+g,
    s=M+2, D(s)=2M-2,
    K=floor((7M-1)/4), D(K)=2M-2+G(M).

Consequently

    D(K)=4m-4+2g+G(M).                               (1)

For any prime q dividing D(K)+sigma (sigma=+-1), the parent-child congruence

    2g+G(M) == 4-4m-sigma (mod q)                    (2)

is **algebraically identical** to the child's one-generation equation `2M-2+G(M)+sigma ==0 mod q`. Without additional information on parent `g` or on intermediate events, (2) is NOT an independent CRT constraint. This important negative result changes the proof strategy: simply appending the parent's formula cannot ban BAD.

## 2. New four-linear-form admissibility gate for prime divisors of parent growth

Assume all four numbers `m-2,m,M-2,M` are prime, as for a GOOD relay between twin-prime input pairs. Let q>=3 be an odd prime with

    q | g,  q < m-2.

Since `M==2m-1 mod q` and `M-2==2m-3 mod q`, none of the four prime integers can be divisible by q. Therefore

    BOXED: m != 0, 2, inv2, 3*inv2  (mod q),         (3)

with `inv2=2^(-1) mod q`. This restriction simultaneously involves the genuine parent and its child and does not follow from child twin-primality alone. For q=3 the allowed residue is only 1; for q=5, the forbidden residues are 0,2,3,4, so the allowed residue is only m=1 mod5.

For sufficiently large twin-prime GOOD parents, g is divisible by6 (m,M==1 mod6). **If 5|g**, (3) implies

    BOXED: m==M==1 (mod 30),
           D_child(M+2)==0 (mod 60).                 (4)

Thus neither 3 nor5 divides the initial child's horizon neighbors D(s)±1. The **QUIET parent** g=0 is a particular case (all primes divide 0): if m>7 and all four numbers m−2,m,2m−3,2m−1 are prime, then m==1 mod30, M=2m−1==1 mod60 and

    BOXED: D_child(s)==0 (mod 120).                  (5)

This is more restrictive than merely saying the parent was GOOD. It excludes an initially active 3- or 5-clock for the child, but later events may activate either clock.

**Exact q=5 seed gate for arbitrary GOOD parent growth:** for any parent m and g=G(m), the child's start is C_s=4m−4+2g. Its 5-clock is active precisely when

    5 | C_s−1  <=>  g == 3m (mod5),
    5 | C_s+1  <=>  g == 3m+4 (mod5).               (5a)

In the artificial m=19 GOOD relay g=6, M=43, the second condition holds and the 5-clock is initially active; for m=31 and g=0 neither does. For a large twin-prime GOOD relay the 3-clock is always initially inactive because M==1 mod3.

**The restriction cannot be extended to every prime q>=7 from four-prime admissibility alone:** m=31 is a quiet GOOD parent, with (29,31,59,61) all prime, and child M=61 has initial horizon 120. Since 120−1=119=7*17, the 7-clock is already active at the child's start. Its scheduled first even hit from s=63 would be index70, but a different factor, 17, causes the ACTUAL first event at n=68 (e=17), changing the horizon and preempting the q=7 clock. The gcd at n=70 then has e=5, not 7. This illustrates why *all* competing prime clocks must be accounted for, not just one residue.

## 3. BAD terminal factor demands a LATE FOREIGN catalyst

Let `(s,C_s)` be any even-horizon original-gcd state and `K>s`. Let q>=5 be an odd prime with

    q | D(K)+sigma, sigma in {+1,-1},
    K-s>=2q.

Let `r_q` be the **last** index n in (s,K] at which `d(n)-1` is NOT divisible by q. Such an index necessarily exists: otherwise D stays constant modulo q, so q would have been active already at s. Its corresponding factor clock would force a q-divisible event within 2q steps, contradicting the absence of residue changes.

After r_q the horizon residue modulo q stays fixed and q remains active in one of its neighbors, so another q-divisible event would necessarily change that residue (since a q-divisible increment e has e−1==−1 mod q). Therefore the same factor clock gives the exact bound

    BOXED: K-2q < r_q <= K.                            (6)

The increment e=d(r_q)>1 satisfies

    BOXED: e not==0,1 (mod q).                         (7)

Indeed e≡1 would not change the horizon residue, whereas if q|e at r_q, the post-event horizon D(r_q) is 0 modq (even r_q) or −2 modq (odd r_q), neither of which has q dividing its ±1 neighbors when q>=5. The terminal factor q must have been (re)activated by a **FOREIGN event**, an increment not divisible by q. For terminal BAD q<=sqrt(D(K)+1), the length assumption holds automatically for sufficiently large canonical M (e.g. all M>=968 under the standard canonical cutoff bounds).

**Special factor 3:** a canonical child with a twin-prime input M>3 starts at D(s)==0 mod3. If q=3 divides the terminal neighbors, a last residue-changing event r_q exists with K−6<r_q<=K. It either has e≡2 mod3 (foreign activation), OR is an exceptional odd q-divisible hit at r_q=K≡5 mod6 leaving D(K)==1 mod3. The exception cannot occur earlier because the immediately following even index is divisible by6 and necessarily has a 3-divisible gcd. This separates the small q=3 BAD branch from q>=5.

## 4. What GOOD parent adds to terminal q

At the GOOD parent's cutoff, D_parent=M−1 and its neighbors are the prime integers M−2,M. Any terminal BAD proper factor q<=sqrt(D_child(K)+1)<M−2 (for M sufficiently large) is **not active at the parent's cutoff**. The intervening canonical record hit has index M+2, increment M, and raises the horizon from M−1 to 2M−2. That large step may create an active q-clock at the child's start, even though q was absent in the parent. However the long child cutoff interval forces a **later** q-changing event, located in the final 2q indices by (6), and foreign to q by (7).

If the parent has 5|G(m), q=5 cannot be active at the child start by (4), so a terminal factor 5 definitively requires a child-internal foreign event in (K−10,K]. For a terminal factor 3, a child-internal event occurs in (K−6,K], with the explicit odd-index exception above.

The parent-child identity (2) itself adds no capacity; the new genuinely useful constraints are (3) and the late **foreign** activation condition (6)-(7). A small foreign event can activate a large terminal factor (e.g. e=7 activating q=47/53 in earlier artificial terminal constructions), so there is no available universal lower bound of order q for this last catalytic increment.

## 5. Exact original-gcd experiments and scope

Standalone Python script replays the complete parity-gcd recurrence for every tested canonical-shaped input, never substituting terminal CRT plausibility for actual gcd events. All 9 BAD synthetic odd starts M<=3000 are enumerated: 11,13,23,25,39,41,43,45,305. All proper small terminal-factor witnesses satisfy the late-catalyst theorem; 8 have q>=5, one q=3.

**Two exact GOOD→BAD local relay examples** (the first is also on the original a(1)=2 orbit):

    parent m=7: G(m)=0, GOOD -> M=13 (ACTUALLY attained),
      child K=22, terminal C=40, terminal q=3 | C−1;
      last q-modulating event n=20,e=5, lag 2.

    parent m=19: G(m)=6, GOOD -> M=43 (ARTIFICIAL relay),
      child K=75, terminal C=132, terminal q=7 | C+1;
      last q-modulating event n=66,e=33, lag 9.
      Earlier n=51,e=7 had made the 7-clock INACTIVE; e=33
      reactivated it at n=66 without being divisible by 7.

The original a(1)=2 sequence DOES attain M=43, but **does NOT attain m=19 as a record**; the actual path to 43 runs through the earlier BAD M=13, so 19→43 is a synthetic GOOD relay and is not misrepresented as an original-record edge.

Synthetic GOOD parents m<=800 with BAD children are exactly:

    (7,13), (15,43), (17,43), (19,43), (21,43).

Of these, only m=7 and 19 have twin-prime *parent* inputs. The exact audit of 200 twin-prime GOOD parents between31 and10000 found 24 with 5|G(m) and 9 quiet parents, all satisfying the inherited prime-quartet gate. Not all are original attained records.

**Counterexample to a naive density consequence of quiet parent:** m=237691 is quiet GOOD (four required primes, m≡1 mod30); its child M=475381 starts with D=950760 divisible by120 yet has 186 internal nonunit events, 157 repeated-prime events, and still terminal GOOD. Thus eliminating the initial 3/5 clocks does NOT bound the number of later events or prohibit their subsequent activation.

## 6. Next possible mathematical breakthrough

The two-generation experiment establishes a target for a **prime-clock preemption / deadline-covering theorem** rather than an unconstrained growth budget: every BAD terminal proper factor q>=5 requires a late foreign catalyst at r_q>K−2q, even if its clock was seeded by the giant GOOD record jump (q=3 has the explicitly classified terminal odd-hit exception). Distinct q may share one catalyst; any global counting theorem must handle that overlap using the products of active factors of D±1 and the exact first-hit race. A possible strategy is to show that any purported sufficiently large BAD child in the REAL reached F-orbit would require an impossible simultaneously deadline-respecting activation/preemption schedule across the two generations. This schedule impossibility is **open**; the present results do not show it must happen.

Status: PAPER lemmas plus exact finite audits, NO proof that every large GOOD child is GOOD, NO Cap B/twin-prime infinitude, and NO new Lean-kernel result.