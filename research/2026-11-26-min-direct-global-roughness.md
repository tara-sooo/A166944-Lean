# Global multiplicity / certified rough-neighbor alternative

Independent direct-arithmetic branch, continuation after d949201 and the Pell note 7033c24. No short-return geometry or historical cost framework is assumed. Paper proof; twin infinitude and A166944 remain open.

## Interval lemma

At each adaptive event let g=p-1, w be the wait, H'=H+g, t'=t+w, d=2t-H. The canonical envelope d>=0 and the p-clock imply w<=2p<=3g, hence d<=6+5(H-H0) for canonical start H0=2M-2, t0=M+2.

In any contiguous event interval from (t_a,H_a) to (t_b,H_b), let G=H_b-H_a, W=t_b-t_a, d_a=2t_a-H_a. Let Y bound all pre-horizons. Set C=floor sqrt(Y+1), B=1+floor cbrt(512(Y+1)). Define U as total gain of p<=B; V as total gain of p>B with 4w>=p-1 (certified large events). Other events satisfy 4w<g. Thus

    2W=G+d_b-d_a>=G-d_a,
    4W<=G+11(U+V),
    11(U+V)>=G-2d_a.

For each certified large event, all prime factors f of H±1 satisfy f>=w/2>=g/8>(Y+1)^(1/3). Indeed a smaller factor is eligible since w<=2p<=2sqrt(H+1), and its clock would preempt. Neither neighbor can have three prime factors counting multiplicity. The selected neighbor H-e=pq has q>=p by square-root eligibility and odd parity, so q is prime; the opposite neighbor is prime or semiprime. No reset or square geometry required. For repeated occurrences of p>=5, q strictly increases since H increases by >=p-1 while e varies by at most2.

Write A(z)=sum_{odd primes p<=z}(p-1), pi_o(z)=number of odd primes <=z. Let A_s=A(min(B,C)), A_l=A(C)-A_s, D=max(0,G-2d_a). For D>0 either U>=D/22 or V>=D/22. In the first case some p<=B has multiplicity >=D/(22 A_s). In the second case define m=D/(44 A_l). Certified labels with multiplicity <m contribute at most D/44 gain, so the others contribute >=D/44. Each of these rich labels has >=m certified occurrences. For any p, its certified gain is bounded by

    (p-1)(pi_o(floor((Y+1)/p))-pi_o(p-1)),

because its prime cofactors are distinct in [p,(Y+1)/p]. If K bounds this capacity uniformly for B<p<=C, there are >=D/(44K) distinct rich labels.

## Global consequence

Under finite twins, each canonical adaptive trajectory beyond the last twin center is infinite. Fix such a root. For even X>=max(H0,256), Y=16X, take the block from first horizon >=X to first >=Y. H_a<=X+sqrt(X+1), pre-horizons <Y. Thus

    G-2d_a >= Y-11H_a-12 >= 5X-11sqrt(X+1)-12 >=4X=Y/4.

So either U or V >=Y/88. Elementary pi_o(z)<=7z/log z follows from theta(z)<=4z log2 by dyadic binomial coefficients, counting primes above sqrt(z), and sqrt(z)<=z/log z. Hence A(B)=O(Y^(2/3)/log Y), A(C)=O(Y/log Y), K<=14(Y+1)/log(Y+1). In EVERY sufficiently large crossed [X,16X], one or both alternatives hold:

(A) Some p<=8(16X+1)^(1/3)+1 is used Omega(X^(1/3) log X) times.
(B) At least Omega(log X) distinct p>B are each used Omega(log X) times in certified large events, with prime cofactor and both neighbors having at most two prime factors.

Constants absolute. Optional PNT constants in Y: A(B)~96 Y^(2/3)/log Y, so (A) >=(1-o(1))*Y^(1/3)log Y/8448. A_l~Y/log Y, K<=(2+o(1))*Y/log Y, so (B) >=(1-o(1))*log Y/352 distinct labels each with >=(1-o(1))*log Y/176 certified events. PNT not needed.

If every fixed prime has finite total multiplicity M(p) and M(p)=o(p log p) as p->infinity, (A) is eventually impossible (uniformly over p<=B, by separating finitely many primes). Then (B) holds in every sufficiently large window. This excludes infinite paths with these multiplicity restrictions and only composite cofactors at sufficiently large labels. Neither (A) nor (B) alone contradicts finite twins; prime cofactors need not differ by2. No global forcing of short returns.

## Diagnostics

Run `node min_direct_global_roughness_audit.mjs 300000 180`. Scan all odd M=5..300000 up to180 events. No 16-fold crossing found; global theorem is a paper deduction. Incidences overlap across windows/sources. No Lean executable/kernel check. Main/siblings unchanged. Remote persistence attempts failed; see current conversation for final status.
