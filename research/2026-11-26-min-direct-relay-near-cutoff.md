# Near-cutoff composite cofactor exclusion

Continuation of [5132aee](https://github.com/tara-sooo/A166944-Lean/commit/5132aeef250c4ae338ddffdebd2395b52617ff34). Same independent branch. Paper proof, not Lean kernel verification.

## Theorem

Assume the descending composite-endpoint branch of the earlier two-relay normalization: four successive actual adaptive events p,a,b,p, p>=101, neither relay3, both p waits>6, minimal even-to-odd return, both endpoint adjusted deficits zero, p^3>64(Y+1) and all pre-horizons<=Y. Let Q be the composite second cofactor, r=minfac(Q), c=a-b, d=Q-p, and e_a,e_b in +/-1 the relay signs. The prior reduction gives p=7 mod12, a,b=1 mod3, a+b=p+1, c,d=6 mod12, c>0, Q=1 mod12, Q>=p+2, Q<p^2/64, c<=4r, and final wait w=(c+4-6I_b)/2, I_b=(1-e_b)/2.

For all sufficiently large p in this branch,
    d > (11/10)*sqrt(p) and d > 2r.
No assumption on primality of Q-2. The size threshold is existential (no explicit numerical bound).

## Exact clock lag

At the final odd reset n=p(Q+1)/2+2, any prime f|Q with f!=p has its preceding odd clock at n-ell_f, with 0<ell_f<2f even. Since 2ell_f=p=-d mod f,
    2ell_f=h_f*f-d, h_f=2 mod4, d<h_f*f<d+4f.
If f^2<=pQ, preemption requires w<=ell_f (equality at start permitted). Ineligible f and the winning p are not competitors. In particular r is always eligible; if d<2r, then h_r=2 and
    c+d+4-6I_b<=2r<=2sqrt(Q).
Equality d=2r is impossible since 3|d and 3 does not divide Q.

## Integral quadratic and limiting lattice

Prior odd parameter j=u-v satisfies j ab=Q(p+1-c^2)-b(c+1-e_a)+a e_b, j=1+e_a+e_b mod3. Let S=p+1,L=4-j. On an unbounded sequence with d=O(sqrt(p)), Q/p->1, c<=4sqrt(Q), and j=4(1-c^2/p)+o(1). Extract fixed odd j<=3, L positive odd; c/sqrt(p)->sqrt(L)/2. Then F(S)=0, where
    F(X)=-LX^2+(4c^2+2c-4d-2e_a-2e_b+6)X
         +(4d-j-6)c^2+(2e_a-2e_b-2)c.
Define N=4L S-(16c^2+8c-4dj-8e_a-8e_b+j^2+2j), and S0=(4LS-N)/(4L).
Expansion:
    16F(S0)=-8(4d-4e_a+4e_b-j-2)c
                +(4d-j-6)(4dj+8e_a+8e_b-j^2-2j).
    2F'(S0)=-(8c^2+4c-4dj+8d-4e_a-4e_b+j^2+2j-12).
Thus 16L F(S0)+4F'(S0)N-N^2=0.
Since d=O(c), S,S0~4c^2/L, F(S0)=O(c^2), derivative between S,S0 is ~-4c^2, the mean-value theorem gives S-S0=O(1). Extract fixed N, signs, and z=lim d/sqrt(p)>=0. Divide exact equation by c^2:
    N=4j z^2-4sqrt(L) z.
Furthermore N=5 mod16 if j=1 mod4, 9 mod16 if j=3 mod4, and N=-j(j+2) mod3. These follow from S=0 mod4, S=2 mod3, c,d=0 mod3, c even, d=2 mod4 and j=1+e_a+e_b mod3.

Case A: d<2r implies Q/p->1, z<=2-sqrt(L)/2, L<=15.
Case B: d>=2r but d<=(11/10)sqrt(p) gives sqrt(L)/4<=z<=11/10 by c<=4r<=2d, L<=19.
Both imply d=O(sqrt(p)). For the indicated closed intervals the exact quadratic gives the following inclusive integer ranges, with only one pair (j,N)=(3,9) satisfying its mod48 condition:
|L|j|N mod48|A|B|
|--:|--:|--:|--:|--:|
|1|3|9|0..21|0..10|
|3|1|21|-3..0|-3..-3|
|5|-1|25|-11..0|-14..-7|
|7|-3|21|-12..0|-26..-13|
|9|-5|9|-11..0|-37..-21|
|11|-7|37|-7..0|-48..-31|
|13|-9|9|-4..0|-59..-43|
|15|-11|21|-1..0|-70..-57|
|17|-13|25|empty|-81..-73|
|19|-15|21|empty|-91..-91|
Evaluate endpoints and the vertex sqrt(L)/(2j) if j>0 and inside. BigInt rational outward bounds independently check the table.

## Pell descent

j=3 forces e_a=e_b=+1. For N=9 the exact equations give S=4c^2+2c-3d+2 and
    9c^2+2cd+2c-3d^2+2d=0.
Put x=14c+2, y=3d-c-1>0 (the negative quadratic root for d is negative). Then x^2-7y^2=-3 and (x,y)=(2,11) mod12. Every positive solution comes from (2,1) or (5,2) via (x,y)->(8x+21y,3x+8y). Indeed for y>=6, 21/8<x/y<8/3, so inverse (8x-21y,8y-3x) is positive, preserves norm and decreases y; y<=5 has only those seeds. Mod12 their orbits are
    (2,1),(1,2),(2,7),(7,2);
    (5,2),(10,7),(11,2),(10,1).
Neither contains (2,11). This excludes the last exact pair. Any unbounded sequence violating either theorem bound would yield case A or B and that pair, contradiction.

If Q=rs, r<=s, the theorem implies s/r>4Q/d^2; for d<=1.5sqrt(p) this exceeds 16/9. Near-cutoff exceptions must have uneven factors.

## Diagnostics and limits

Exact CRT scan p<=50000: 2868 scale candidates, all N identities/congruences verified. Among the previous 87 composite coarse-clock candidates: 176 factor lag checks, 175 eligible, 1 ineligible, 51 rejected by eligible earlier hits, 36 survive this additional test (not actual realizations). Zero d<2r before lag filtering. Minimum d/sqrt(p) in these candidates 262.64789 (p3079,Q17653); after lag test 710.18299 (p1423,Q28213). These are not near the theorem boundary. Node v22 standalone audit executed successfully; check actual remote path for persistence. No empirical inference of the limiting theorem. Separately SymPy factored Q and six later neighbors for all 25 prior cubic families: Q irreducible cubic, neighbors irreducible sextics or two cubics, no degree1/2 factor obstruction. The 25 families remain; the present proof mainly attacks the semiprime scale. No global forcing of the short return, no twin proof, no Lean verification. Main and siblings untouched.
