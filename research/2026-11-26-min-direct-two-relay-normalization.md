# Two-relay minimal returns, exact mod-three normalization, and reset resonance

Continuation of [7b73565](https://github.com/tara-sooo/A166944-Lean/commit/7b73565c41272dcdc8d54fa3eccf629bcf0298ed) on the independent direct-arithmetic branch. This note derives a second way to extract twins (from the selected labels themselves, even when cofactors are composite), a uniform local normalization theorem with a complete reset table, and sharper necessary conditions for the remaining two-relay returns. No source ensemble, return-cost decomposition, merger estimate, or asymptotic prime distribution. Paper proofs plus exact finite diagnostics; no Lean verification or external novelty claim. Twin infinitude and the original A166944 conjecture remain open.

## 1. Notation and two-relay arithmetic

Use actual adaptive MIN from H even >=8 at time t, with H<=2t. The earliest strict future hit at n is chosen, ties by least eligible odd prime p<=sqrt(H+1). Write e=+1 on the even/minus side, e=-1 on the odd/plus side; p divides H-e and n-2I, where I=(1-e)/2. Write w=n-t, q=(H-e)/p (odd and >=p), Z=H+p-1, d=2t-H, delta=2n-Z, D=delta-6I. For p>=5, D is a nonnegative multiple of 2p. For p=3 the odd-side possibility D=-6 need not be nonnegative. In the following reset state means an arbitrary plateau (t,H) with 2t-H=6(t mod2), equivalent to adjusted D=0 for an immediately preceding event.

The preceding note proves that for two occurrences of p>=5, with intervening gain G (excluding both p events),

    q2-q1=2m, m>=1;
    G=(2m-1)p+1+e2-e1;
    n2-n1=l*p+2(I2-I1), l>=1, l=I2-I1 mod2;
    D2-D1=2p(l-m).                                      (1)

Here m=1 iff G<3p-1. Two successive p occurrences with exactly two intervening nonunit events p,a,b,p (a,b distinct from p) satisfy

    a+b=(2m-1)p+3+e2-e1.                                (2)

In particular, if both a,b<p (p is maximal on this block), G=a+b-2<3p-1, so m=1. Consecutive a=b>=5 is impossible in the relaxed horizon rule because after a use the residue is 0 or -2, neither +/-1. The case a=b=3 is allowed in general.

Assume BOTH p waits are >6. Then both pre-horizons H1,H2 are 0 mod3: otherwise the eligible prime3 hits within 6 ticks. From H2-H1=2mp+e2-e1, in a minimal return (m=1) the sides must differ. There are two cases:

    even -> odd: p=1 mod3, a+b=p+1;
    odd -> even: p=2 mod3, a+b=p+5.                      (3)

**Label twin theorem.** If either relay a or b equals3, the other equals p-2 in the first case, or p+2 in the second. Thus the labels themselves form a twin pair. This does not require either cofactor to be prime or the endpoint scale to be near a square. Unbounded p in such actual returns suffice for twin infinitude.

For the even->odd case p=1 mod3, if both relays differ from3 they must both equal1 mod3 (and are >=7). For the odd->even case p=2 mod3, if both differ from3 they must both equal2 mod3. These are exact consequences of (3), not assumptions about prime distribution.

## 2. General mod-three excursion deadline

Consider any actual plateau (t,H), H>=8 even, H<=2t, H not 0 mod3. Let T be the first time at which the horizon becomes 0 mod3. Then T exists, and

    H=1 mod3: T-t<=12;
    H=2 mod3: T-t<=7.                                  (4)

Proof. A non3 label congruent to1 mod3 preserves the horizon residue, whereas a non3 label congruent to2 increases it by1 mod3. From residue1 the even 3-clock at ticks 0 mod6 is active; from residue2 the odd 3-clock at ticks 5 mod6 is active. A non3 event preserving the residue does not change the absolute scheduled 3-clock, so cannot indefinitely postpone it. If residue1 persists, the next even 3-clock (at most 6 ticks away) returns to0. If it changes to2 before that clock, the change must occur strictly earlier (3 wins a tie), hence within at most 5 ticks. Once in residue2, either a non3 increment reaches0 or the next odd 3-clock (within 6 ticks) wins. That 3 event leaves residue1, and the immediately following even tick is a 3 event, as proved in the three-support note. Thus the total bound is 5+6+1=12. Starting directly in residue2 gives 6+1=7. These are absolute tick bounds, not event counts. They hold for fixed pools containing3 as well.

By the envelope, the entire excursion's horizon gain is bounded by

    H(T)-H(t) <= d+2(T-t) <= d+24,
    d=2t-H(t).                                         (5)

Every label within that excursion is therefore <=d+25 (and <=d+15 if starting in residue2). This is an immediate consequence of (4), not a separate amortized cost estimate.

In any infinite adaptive trajectory, mod-three divisible horizons occur unboundedly, with the displayed uniform duration of every intervening nonzero excursion. This does not imply that the gaps between successive divisible horizons are bounded in ticks (long waits at an already divisible plateau are allowed), nor that an infinite path stops.

## 3. Exact normalization for adjusted reset states

For a reset state H=2t if t even, H=2t-6 if t odd, H>=8, H not 0 mod3, the first return to H=0 mod3 is COMPLETELY determined by the following table. The column 'word' omits quiet ticks; W is total elapsed ticks; d_out is ordinary deficit 2t_out-H_out at the end.

| reset parity | H mod3 | condition | word | W | d_out |
|---|---:|---|---|---:|---:|
|even|1|5 eligible and t+2=0 mod5|5,3,3|4|0|
|even|1|otherwise|3|4|6|
|even|2|all|3,3|2|0|
|odd|1|all|3|1|6|
|odd|2|5 eligible and t=0 mod5|5|2|6|
|odd|2|else 13 eligible and t+3=0 mod13|13,3,3|5|0|
|odd|2|otherwise|3,3|5|12|

Eligibility means p^2<=H+1 on the initial plateau for adaptive MIN; in a fixed pool use membership. If the prime5 condition applies, it preempts13.

Proof by raw gcd:
- Even reset H=2t with H=1 mod3 has t=2 mod6. At w=1 (odd absolute tick) raw gcd divides3 but t-1 is not divisible by3. At w=2 (even) it divides5; at w=3 (odd) it divides1. At w=4 even 3 wins unless 5 hit at w=2. In the latter case the 5 jump reaches a new even reset with residue2, and the following two ticks are the forced odd/even 3 doublet. Thus W=4.
- Even reset residue2 has t=4 mod6; odd 3 at w=1 and even 3 at w=2 are forced.
- Odd reset H=2t-6 with residue1 has t=5 mod6; even3 at w=1 is forced.
- Odd reset residue2 has t=1 mod6. At w=1 even the gcd divides9 but t+1 is not divisible by3; at w=2 odd it divides5; at w=3 even it divides13; at w=4 odd3 hits. If 5 wins, the horizon already reaches residue0. If 13 wins, its jump12 puts the state on an even reset, still residue2, followed by the forced doublet. Otherwise the odd 3 at w4 is followed immediately by even3. The stated deficits follow from H increments and elapsed ticks.

Thus every such reset normalizes in at most FIVE ticks, with gain at most16, using only {3,5,13}; at the resulting divisible horizon the ordinary deficit is at most12. This is a sharper exact version of (4)-(5), valid at arbitrary absolute scale, without a square-entry assumption.

A useful corollary: if a p=2 mod3 event starts from H1=0 mod3 and has D1=0, its post-horizon is residue1. If the p event was odd, the next event is necessarily even3 at the very next tick. If it was even, the normalization word is 3 or 5,3,3 in four ticks, as above. Hence these p resets always lead to a divisible horizon with ordinary deficit at most6, independently of p. At a later event with label P from that normalized plateau, 2w=P-1+delta-d implies w>=(P-7)/2; for large P relative to sqrt of its cofactor this certifies cofactor primality. No assertion that a large P must next occur.

## 4. Non3 odd-to-even minimal return: an automatic long second wait

Return to (3), in the odd->even case with neither relay equal3. Here p,a,b=2 mod3. The post-p horizon has residue1, the post-a horizon residue2, the post-b horizon residue0. Both a and b must preempt the active 3-clock.

Starting from the odd first p tick n1, let E be the next even 3 tick. If n1=5 mod6, E=n1+1 and no non3 first relay is possible. For n1=1 or3 mod6, E-n1=5 or3. The first relay occurs before E. The next odd 3 tick after that relay is at most E+5 (if the relay occurred at E-1); the second relay must occur strictly before it. Hence

    w_a+w_b <= 9.                                      (6)

The minimal opposite-side return identity gives n2-n1=l*p-2>=p-2, hence

    w2 >= p-11.                                        (7)

Also D1 cannot be0: the odd-reset normalization at residue1 forces an immediate3. Consequently D1>=2p. These conclusions only need H1,H2 divisible by3, not the cofactor certificates or long first wait separately.

**Finite-twins consequence.** Suppose twin upper members are bounded by T_*. For a minimal two-relay odd->even return with both p waits>6, p>T_*+2, pre-horizons <=Y, p>=101 and p^3>64(Y+1), the label twin theorem excludes a relay3. By (7), the second cofactor q2 is prime: q2< p^2/64 and w2>=p-11>2sqrt(q2). Therefore the first cofactor q1 must be composite. Since delta1=D1+6>=2p+6, the previous cofactor competition inequality gives the strengthened requirement

    d1 >= p+1+delta1-4 minfac(q1)
       >= 3p+7-4sqrt((Y+1)/p).                         (8)

In the regime p^3/(Y+1) growing without bound this is (3-o(1))*p, rather than the earlier generic (1-o(1))*p lower bound at an unspecified endpoint. Thus finite twins would require a large ordinary deficit specifically BEFORE the first p in this return type. In particular such a return is impossible if d1<=2p under the stated scale gate. If first p is an odd reset and p is maximal among the four labels, this minimal long-wait two-relay return is impossible UNCONDITIONALLY: non3 relays are excluded by the reset normalization, and a relay3 would require the other label p+2>p.

The absence of this non3 orientation in the finite canonical scan is NOT a general exclusion. An actual adaptive segment from abstract start (t,H)=(201864,303078) has word 29,11,23,29, sides odd,even,odd,even, waits7,1,1,25. The pre-horizons are303078,303106,303116,303138; first and last q=10451,10453 and D=100630 at both endpoints. This satisfies the envelope and all actual first-hit rules, replayed by literal parity GCD; no canonical ancestry claimed. In particular equal nonzero D does not suffice for exclusion.

## 5. Even-to-odd minimal return between resets: composite endpoint resonance

Consider p,a,b,p with BOTH p waits>6, m=1, first p even and second p odd, D1=D2=0, neither relay3. Then p,a,b=1 mod3, a+b=p+1, a,b>=7, and n2-n1=p+2 by (1). Let D_a,D_b be the adjusted post-deficits of the two relays, I_b=0 or1 according to the parity of the last relay.

From the even reset immediately after the first p, the first relay satisfies

    0<=D_a=2w_a-a+1-6I_a<=3a+1<4a

because w_a<=2a. Thus D_a is 0 or2a.

If D_a=0, its ordinary post-deficit is <=6. The next relay has D_b<=3b+7; since b>=7 this is <4b except the possible b=7,D_b=28.
If D_a=2a, then w_a>=(3a-1)/2. The total time p+2 and w_b>=1,w2>=7 imply 3a<=2p-11, hence b>= (p+14)/3. At the final reset,

    2w2=p+5-D_b-6I_b,
    D_b<=p-9-6I_b<4b.

Consequently in ALL cases D_b=0 or2b except for the small possibility b=7,D_b=28. If D_b=2b, the exact last wait is

    2w2=a-b+4-6I_b.                                    (9)

Now suppose p>=101 and p^3>64(Y+1), with both p pre-horizons <=Y, and q2 composite. Its least prime factor r<=sqrt(q2)<p/8 is smaller than p and preempts unless w2<=2r-1. Therefore

    D_b=p+5-6I_b-2w2 >= p+7-6I_b-4r > p/2+1.

In particular D_b is not 0 or the exceptional 28; it MUST equal2b. The state after b is H2, and every post-event horizon is -D mod4 since delta=D+6I and n has parity I. Hence H2=2 mod4. The post-first-p horizon is0 mod4 and the gain between them is p-1, so p=3 mod4. Together with p=1 mod3 this gives

    p=7 mod12.                                         (10)

By (9) and 7<=w2<=2r-1,

    10+6I_b <= a-b <= 4r-6+6I_b.                        (11)

Since a,b=1 mod3 and are odd, their difference is a multiple of6. In particular they must occur in descending order and be close on the scale of p: a-b=O(sqrt((Y+1)/p)). Both are approximately p/2 when p^3/(Y+1) is large. No claim that their difference is exactly2 or that (10)-(11) suffice for actual reachability.

**Direct witness condition.** Under the same scale and reset hypotheses with neither relay3, if p=1 mod4 then q2 MUST be prime. If the first cofactor is independently certified prime (e.g. d1<=p/2, for which w1>=(p-2)/4 and the strict scale gate, or directly using the earlier first-hit criterion), both cofactors q1,q2 form twins. To avoid borderline constants in the d1 sufficient condition, one may use d1<=p/3, which gives w1>=(2p/3-1)/2>p/4 for p>=101. The d1<=p/3 version therefore suffices throughout the stated scale range. With a relay3 the label twin theorem already suffices, independent of d1.

Thus under finite twins, large maximal p having a minimal two-relay long-wait return between resets and first cofactor certified must be in the even->odd direction, p=7 mod12, with D_b=2b and the narrow descending relay gap (11). This is a sharper arithmetic target than just asking for small pre-deficits at both endpoints. It does not force such returns at unbounded p, or rule out the exceptional resonance.

## 6. Finite diagnostics

[Audit at 715dd0f](https://github.com/tara-sooo/A166944-Lean/blob/715dd0f08566d791babf409ddb6357bb42996bc0/research/min_direct_two_relay_normalization_audit.mjs), blob faa916b0c949d059d1c29a8ead5c23d59755abdc, exact remote readback. Run:

    node research/min_direct_two_relay_normalization_audit.mjs 150000 200 1100

Executed the actual ECMAScript function in the tool runtime, not a separate Node process. All odd M=5..150000, at most200 actual nonunit events per source or earlier stop. 1,631,698 event incidences, no range truncation. 717,926 nonzero-mod3 excursion checks. Both bounds (4) attained on actual canonical paths: M981, (t,H)=(1020,1990), word11,3,3, ends (1032,2004), duration12; (1025,2000), word3,3, duration7. Verified exact reset table at 49,998 abstract states with H<=150000 and 170,443 actual canonical state incidences. All seven table branches observed.

103,776 two-relay same-label returns, 20,694 with both waits>6, 15,590 minimal among those. 15,466 had a relay3, giving 2,062 distinct physical endpoint pairs and SIX distinct twin lower labels {5,11,17,29,41,71}. 124 long-wait minimal non3 returns were even->odd; none were odd->even in this bounded canonical scan, not a theorem. Literal-GCD replay of the explicit abstract odd->even non3 counterexample in section4 demonstrates why no phase-space exclusion is claimed.

Representative actual canonical source M18033, word43,41,3,43, first p at n18060,H36078,e=+1,w18,q839,D0; second at n18105,H36162,e=-1,w21,q841,D0. q841=29^2 is composite, but the label twin theorem gives41,43. Largest label pair in canonical scan: M91937, word73,71,3,73, endpoint waits19/107, q2519/2521, certifies twin labels71,73 even though no claim that both cofactors prime.

Additional bounded abstract search: for primes p=1 mod3, 101<=p<=1100, q>=p, q=11 mod12, q<=min(8p,floor(p^2/64)-3), use even first-reset target H=pq+1, n=p(q+1)/2 and start at t=n-7 (not a canonical ancestry assertion). 24,355 candidate plateaus; 11,942 actual first hits p with wait7; one minimal two-relay reset-to-reset hit sequence with second wait>6, all relays non3. It has p421, word421,409,13,421, q1=851 (composite), q2=853 (prime), all adjusted D zero, waits7,207,3,213. This verifies existence of a high-scale non3 reset return in the general state space but does not certify twins by both cofactors. The last relay resonance (10)-(11) had NO high-scale composite endpoint instance in this finite audit; its exclusion implication is a mathematical proof, not claimed empirically demonstrated by a positive example. The single high-scale check had a prime second cofactor. Eight event incidences were replayed by independent literal parity GCD (two abstract examples). No Lean executable/formal verification.

## 7. Next target

The new label twin theorem dispenses with primality certificates when a minimal two-relay return contains 3. Exact reset normalization shows that 3-active intervals cannot persist, and for one of the two opposite-side return geometries it forces either twin labels or a much larger first pre-deficit. In the other reset geometry, a composite second cofactor confines the large label to 7 mod12 and the intermediate primes to a narrow descending resonance. The unresolved global step is to force unbounded short maximal-label returns with the required waits and deficit geometry, or to exclude the resonant branch by additional arithmetic. Prior multiplicity lower bounds do not force two-relay returns or resets, so no contradiction with finite twins has been obtained. General non3 odd->even returns exist at large deficit, and longer return words remain possible. Main and sibling branches unchanged.
