# Repeated-label cofactor twins, adjusted return strata, and relay exclusion

Continuation of [469d5d6](https://github.com/tara-sooo/A166944-Lean/commit/469d5d6093c466eaca088a56b82bd9a11161ed57) on the independent direct-arithmetic branch. Focus on actual adaptive MIN and exact two-event arithmetic. The previous cofactor primality lemma and three-support intervening-gain bound are used, but no square target, cumulative return-cost, energy, merger, source ensemble, or prime-distribution hypothesis. Paper proofs and finite exact diagnostics; no Lean kernel verification or external novelty claim. Twin infinitude and A166944 remain open.

## 1. Event coordinates and exact return identity

Canonical odd M>=5 starts (t,H)=(M+2,2M-2). At the earliest eligible tick n>t choose the least odd prime p with p^2<=H+1, p|H-e, and p|n on the even side e=+1 or p|n-2 on the odd side e=-1. Put w=n-t, q=(H-e)/p, Z=H+p-1, d=2t-H, delta=2n-Z. Then q is odd and q>=p: for even side p^2<=pq+2 excludes odd q<=p-2; odd side p^2<=pq immediately. The canonical envelope H<=2t holds, so d,delta are nonnegative even.

Let I=(1-e)/2, equal to 0 for even and 1 for odd. Define the adjusted coordinates

    U=n-2I,  V=Z+2I=p(q+1),
    D=2U-V=delta-6I.

Both U,V are divisible by p; V is even, so D is a multiple of 2p. For p>=5, D>=-6 and hence D>=0. (The label3 odd-side exception D=-6 is allowed; do not apply the nonnegative statement to that case.) The useful exact equality for the pre-deficit is

    2w=p-1+delta-d.                                     (1)

Compare any two distinct events of the same p>=5, in chronological order, not necessarily consecutive occurrences. Since H2-H1>=p-1 and e2-e1<=2, q2>q1. Since both q are odd, write q2-q1=2m, m>=1. Also U2-U1 is a multiple of p and is >=-1 because n2>n1 and each correction is 0 or 2. It cannot be zero: if e sides equal then n2>n1 gives positive difference, if sides differ then U values have opposite parity. Thus U2-U1=lp with l>=1. The exact identities are

    V2-V1 = 2mp,
    D2-D1 = 2p(l-m),
    n2-n1 = lp+2(I2-I1),
    l = I2-I1 mod2,
    H2-H1 = 2mp+e2-e1.                                 (2)

Let G=H2-Z1 be the entire intervening gain, including any intervening repeats of p if the chosen events are not consecutive p occurrences. Then

    G=(2m-1)p+1+e2-e1.                                  (3)

In particular for consecutive occurrences, the smallest possible return m=1 is equivalent to G<3p-1, and then G is one of p-1,p+1,p+3. This is the same adjusted horizon progression previously isolated for three labels, now a general exact identity with an explicit time coordinate. Same-side return has l even >=2, opposite-side l odd >=1. For a minimal same-side return D increases by at least 2p; for a minimal opposite-side return D cannot decrease. If two events have the same D (an equal adjusted-deficit stratum, including the reset stratum D=0), then l=m. In that case same-side m is even and opposite-side m odd.

## 2. Twin primes from a minimal repeated-label return

The earlier first-hit/cofactor lemma gives a simple certificate for q to be prime at an actual event:

    q<p^2 and w>=2*floor(sqrt(q)).                       (4)

Indeed if q composite with least prime factor r, then r<=floor(sqrt(q))<p, is in the adaptive pool, divides H-e and supplies a competing hit within 2r ticks. With p selected, w<2r (smaller r wins a tie), contradicting (4). Independently, the stricter condition w>2sqrt(q) also suffices by the roughness lemma; (4) is useful at near-square or moderately balanced scale. No implication that q is prime for every event.

**Minimal-return witness theorem.** If two occurrences of a fixed p>=5 have m=1 in (2), and both satisfy (4), then their cofactors q1,q2 are twin primes. This does not require q1=p, q1=p+2, or H to be a square. It even holds for arbitrary plateau starts satisfying the envelope, and is valid for the adaptive canonical trajectory. Since q1>=p, arbitrarily large p in such witnesses suffice for twin infinitude. Alternatively it is enough to force unbounded q1 irrespective of the labels p.

A directly usable version for short support: suppose consecutive occurrences of p are the largest label in their block and the intervening block uses at most two other labels. Then m=1 necessarily. By the exact relaxed two-label bounds, if both intervening labels a<b are >=5, intervening gain <=2a+b-3; if a=3,b>=7 it is <=b+5; if {3,5} it is <=16. All are <3p-1. A one-label or empty intervening block also has gain <3p-1. Thus both endpoints satisfying (4) certify twins. The short-support assumption alone does not force the endpoints to satisfy (4).

There is also a finite-twins obstruction in pre-deficit coordinates. Assume all twin primes have upper member at most T_*. Take a minimal return of p>T_* within pre-horizons H1,H2<=Y, with p^3>Y+1. Then q1,q2<p^2 and q1>=p>T_*. At least one q is composite, say at endpoint i. For its least prime factor r<=sqrt(q_i)<p, w_i<=2r-1. From (1) we obtain

    d_i >= p+1+delta_i-4r
        >= p+1-4sqrt((Y+1)/p).                          (5)

Thus every such minimal return must have at least one large PRE-event deficit. In the regime p^3/(Y+1)->infinity, this lower bound is (1-o(1))*p. This is true even when both POST-event deficits equal their reset values. It is not enough to bound only post-deficits.

Equivalently for fixed 0<eta<=1, if p>=2/eta, p^3>64*(Y+1)/eta^2, and both pre-deficits d_i<=(1-eta)*p, then (1) gives w_i>=eta*p/4>2sqrt(q_i), certifying twins for any minimal return. No hypothesis about first entrance into a square. This produces a new precise sufficient forcing target: arbitrarily large cofactors at two low-pre-deficit occurrences of a repeated maximum label with a short-support return.

## 3. Modulo 3 and return spacing

Call an event qualified here if it satisfies (4) AND w>6. The latter forces H=0 mod3, since otherwise one neighbor has an eligible 3 clock within 6 ticks. Hence for qualified p>=5 events

    q = -e*p mod3.

Comparing two qualified occurrences gives

    m=0 mod3             if same side;
    m=e1*p mod3          if opposite sides.               (6)

Let s_i be the representative +1 or -1 of e_i*p mod3. Suppose both cofactors exceed the last twin upper member (under finite twins), so m=1 is excluded. Then same-side m>=3, flip s1=1 to s2=-1 requires m>=4, flip -1 to 1 requires m>=2. Uniformly

    m >= 3+(s1-s2)/2.                                    (7)

If the events also belong to the SAME D stratum, (2) forces m even on the same side and odd on opposite sides. The three respective lower bounds become 6,7,5, uniformly

    m >= 6+(s1-s2)/2.                                    (8)

These bounds are conditional only on exclusion of m=1 between the qualified events. In particular they apply under finite twins beyond the largest twin center. For any ordered list of g+1 qualified p occurrences, telescoping (7) gives q_last-q_first>=6g-2. For any list in one fixed D stratum, (8) gives q_last-q_first>=12g-2. This does not require that the selected visits be consecutive occurrences of p. In a pre-horizon interval [X,Y], these imply respective count bounds

    count <= 1 + floor(((Y-X+2)/p+2)/6),
    count <= 1 + floor(((Y-X+2)/p+2)/12)  in one stratum.

Here q_last-q_first=(H_last-H_first-e_last+e_first)/p<=(Y-X+2)/p. If no qualified events occur the count is zero; the displayed bounds are deliberately not optimized by the initial/final signs. In particular, a minimum return m=1 among qualified occurrences must flip s from +1 to -1; two successive such minimum returns are impossible even without the finite-twins assumption.

These upper bounds depend on p and the horizon window, not on the number of other labels. They improve the raw spacing 2p between adjusted horizons to an average of 6p, or 12p in a fixed stratum, under finite twins. They do not contradict the earlier lower bound Omega(log X) on the multiplicity of some primes: e.g. for p comparable to sqrt(X) and Y=2X, even the improved upper bound remains of order sqrt(X), and the high-multiplicity primes need not be qualified.

## 4. Unconditional one-relay exclusion, independent of cofactor primality

Consider three successive nonunit events p,h,p with p>=5 and h!=p, where BOTH p events wait more than 6 ticks on their respective pre-plateaus. The relay h is prime. Equation (3) with G=h-1 gives

    h=(2m-1)p+2+e2-e1.                                  (9)

Because both pre-horizons are multiples of3, (6) applies without the cofactor-primality condition (4). There are three cases.

- e1=+1,e2=-1: h=(2m-1)p is a multiple of p, so impossible for a distinct prime relay.
- e1=e2: h=(2m-1)p+2 and m=0 mod3, so h>=5p+2.
- e1=-1,e2=+1: h=(2m-1)p+4 and m=-p mod3. Reducing h modulo3 gives h=-1-p mod3. Therefore p=2 mod3 makes h divisible by3, impossible since h>p>=5. So p=1 mod3 and m=2 mod3, hence h>=3p+4.

In one fixed D stratum, m parity from (2) improves the latter two bounds to

    same side: h>=11p+2;
    odd to even: p=1 mod3 and h>=9p+4.

The even-to-odd case is impossible regardless of waits. Indeed h=(2m-1)p always holds there. This theorem is unconditional, not reliant on twins being finite or the prime cofactors being certified.

A useful scale consequence: if a block lies below pre-horizon Y, all its labels <=sqrt(Y+1). Therefore long-wait p,h,p cannot occur if p>(sqrt(Y+1)-4)/3, or in one D stratum if p>(sqrt(Y+1)-4)/9. For the same-side patterns use the stronger 5 and 11 thresholds with +2. This excludes the simplest possible near-cutoff reuse mechanism. It does not exclude returns with two or more intervening labels. The next possibility is to use equation (3) on longer relay words rather than to count every prime-pair occurrence independently.

## 5. Exact diagnostic evidence

[Audit at 308d20b](https://github.com/tara-sooo/A166944-Lean/blob/308d20b31167e98d360e1c47e8a6b23ae17b0/research/min_direct_repeat_cofactor_audit.mjs), blob d09dbfca40fe081c7a6f49901367e215f3bb39fc. Exact remote readback. Run from repo root:

    node research/min_direct_repeat_cofactor_audit.mjs 150000 180

Executed the actual ECMAScript audit function in the tool runtime, not a separate Node process. All odd roots M=5..150000 for at most 180 nonunit events, or earlier stop. 1,630,951 actual adaptive event incidences, no range truncation. 493,049 consecutive same-label return checks for p>=5; 97,193 minimal returns. 75,167 qualified event incidences, 798 pairs of successive qualified visits, 214 equal-stratum residue checks (counts across overlapping check categories), 653 minimal-return composite-cofactor deficit checks for q_i<p^2; all passed. 1331 general conditional spacing checks and 27 conditional same-stratum checks excluding m=1. The diagnostic does NOT assume twins finite; it checks the implications when m!=1.

137 consecutive minimal-return incidences with BOTH endpoints qualified, representing 19 DISTINCT physical event pairs and 17 DISTINCT twin lower members (71,149,179,239,269,347,419,599,641,881,1019,1151,1229,1301,1319,1787,1949). Source incidences are not independent physical events. 34 pairs of successive qualified reset-stratum visits were all minimal (source incidences); finite observation, not universal claim. 44,156 maximal-label returns on at most three distinct labels were all minimal, as proved. Of these none had both endpoints qualified, but 4,676 had both cofactors prime by direct factorization. This is a finite observation, not a theorem that short-support witnesses are impossible. It is important to distinguish direct primality testing from the dynamic certificate (4).

Representative actual prime-root twin witness M=79481:

| event | n | pre H | label p | side e | q | w | D |
|---|---:|---:|---:|---:|---:|---:|---:|
|first|79657|159042|89|-1|1787|97|178|
|second|79922|159222|89|+1|1789|113|534|

Intervening word 3,7,11,3,61,13. Both q_i<89^2; both waits exceed twice floor sqrt(q_i). Thus the dynamics certifies the cofactors 1787,1789 prime without a special square geometry.

Representative PRIME root with equal reset stratum M=63149:

| event | n | pre H | label p | side e | q | w | D |
|---|---:|---:|---:|---:|---:|---:|---:|
|first|63300|126390|211|+1|599|54|0|
|second|63513|126810|211|-1|601|105|0|

Intervening word 17,5,3,3,5,3,139,17,3,5,7,3,11,3. Both cofactors certified by (4). The first pre-deficit is102 and the second6. Largest q witness by dynamics in the scan: M76981,p79,q1949/1951, waits118/127, D158/474. Example of a short-support return with directly tested prime cofactors, but NOT dynamically certified by (4): M149441, word 7,5,3,7, q42701/42703, waits14/7, D98 both. The small label is not a large-scale primality certificate in that case. All representative witnesses were replayed from their canonical roots with the literal tickwise parity GCD rule (122 replayed event incidences).

9,043 one-relay returns p,h,p, of which 995 had both p waits >6 and 25 also had equal D. All obeyed (9) and the appropriate unconditional lower bounds. Independent arithmetic controls: 753 prime relay candidates satisfying the modular conditions, p<=499,m<=50, all obey the same bounds (these controls do not establish actual reachability). Example actual M3399,p7,h37, both p even-side, waits14 and8, D98 and84; attains same-side lower h=5p+2. No formal verification by Lean/lake.

## 6. Next target

The prior proof approach needed special near-square arrivals. Here cofactor twin extraction works for any minimal repeated-label return with both waits long enough, and finite twins force a large pre-deficit at one endpoint of every high-scale minimal return. The exact return identity and one-relay theorem impose additional independent timing restrictions. The unresolved global step is to force infinitely many large dynamically certified minimal returns from actual MIN, or to prove an upper bound on the simultaneous recurrence of qualified/unqualified labels that contradicts the all-window multiplicity lower bounds. Finite computations show actual witnesses at moderate roots, not their unbounded occurrence. No final twin-infinitude proof, A166944 proof, or external novelty claim. Main and sibling branches unchanged.
