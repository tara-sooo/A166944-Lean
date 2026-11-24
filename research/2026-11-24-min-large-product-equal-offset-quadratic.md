# Large CRT product: equal-offset quotient reduction and quadratic residue sieve

2026-11-24 JST. Continues 8a452377fcb0c47af4912aeb40eb4933aa988b81 on the SAME research/min-cycle-forest-2026-11-24 branch. Paper deductions using the earlier uniform upper-bound sieve, plus exact finite audit. No Lean compilation. The full matching estimate and twin-prime conjecture remain open.

## 1. Preserve the quotients

Use canonical MIN, LOW7 L=210, N=X/2, B=ceil(sqrt(7X)), original individual cutoff tags, and the disjoint stopped-cohort far matching and projected first-contact interface of the preceding notes. At a first asynchronous projected contact (p,C) with distinct previous high labels q,q', suppose the two previous indices k,k' are positive. For the two preceding low gains g,g' and their divisibility signs sigma_q,sigma_q' in {-1,1}, define the even offsets s1=1+sigma_q-g, s2=1+sigma_q'-g'. Let sigma in {-1,1} be the current divisibility side. Then
    C+sigma = p a0,
    C+s1 = q a1,
    C+s2 = q' a2,
    |s1|,|s2|<=L+2.
The exact three-label clock relation is
    kq-k'q'=d=2jp+e/2,
    j!=0, |e|<=7L+4r(C)+6, e even.
Both quotients a1,a2 are positive integers. For arbitrary offsets, subtraction and elimination yield
    q a1-q'a2=s1-s2,
    (k'a1-k a2)q+d a2=k'(s1-s2).
These are exact, including when e=0. The second identity follows by multiplying the first by k' and substituting k'q'=kq-d. It is not a sufficient condition for an actual MIN history.

Consider specifically the unresolved large-product range pqq'>X U, with p,q,q' distinct, U=log^lambda B, lambda>beta>0, and
    1<=k,k'<=H=log^beta B,
    1<=|j|<=H,
    r(C)<=z=ceil(log^gamma B).
Then p>=X U/B^2, so p>H and p>L+3 eventually. In particular p does not divide k or k'. Previous mass caps m(q,D)<=qW,m(q',D')<=q'W, W=log^delta B, will be imposed where needed. All matching bounds use degree one; for fixed parent keys the number of actual matched pairs is at most the smaller whole executed parent mass.

## 2. Equal offsets give a quadratic residue condition, no CRT +1 loss

Suppose s1=s2=s. Then C+s=v q q' with a positive integer v, since q,q' are distinct. The two parent quotients are v q' and v q. Set t=sigma-s, a bounded O_L(1) integer. Current divisibility implies
    v q q'+t=0 mod p.
If t=0, p|v, giving pqq'<=C+s<=7X+O_L(1), contrary to pqq'>X U eventually. If t!=0 then p does not divide v (because p>|t|). Reduce the clock equation modulo p, multiply the divisibility condition by k', and substitute k'q'=kq-e/2 mod p:
    v k q^2 - v(e/2)q + k't = 0 mod p.
The coefficient vk is nonzero mod p. Therefore for fixed p,v,k,k',e and t the prime q lies in AT MOST TWO residue classes modulo p, even if the discriminant vanishes. Keeping j as an additional fixed integer uniquely determines q' from q. This counts actual candidate C directly via C=vqq'-s, with no use of a truncated three-modulus CRT progression. The following estimates exploit this structure. In both, all q,q' are distinct from p and d!=0: otherwise kq=k'q' with polynomially large distinct labels and k,k'<=H is impossible.

## 3. Theorem A: top parents with arbitrary current prime in the large-product range

Let q,q'>=B/log^alpha B with fixed alpha>0. Then v<=O_L(log^(2alpha) B). For each fixed p,v,k,k',j,e and s,sigma, the quadratic permits at most two classes mod p. For either class, the possible q are in [B/log^alpha B,B], a progression of length at most O(1+B/p). Use the uniform dimension-one upper-bound sieve on an interval of parameter length comparable to n=1+B/p, omitting p; sieve cutoff a sufficiently small power of n, level n^(1/4). For bounded n the trivial count suffices. All actual q exceed the cutoff for sufficiently large B, and the standard residue error O(n^(1/4)) is absorbed. The candidate prime count is
    O((1+B/p)/(1+log(B/p))).
No primality assumption on the determined q' is needed for this upper bound. Each candidate (q,q') fixes C and both previous keys given g,g' and signs. Under the uniform cap T=B the number of matched pairs charged there is <=B; under the normalized cap it is <=BW. Use BW below (also covers the uniform cap since W>=1).

The elementary prime-counting bound gives
    sum_{p<=B prime} 1/[p(1+log(B/p))]
        = O(log log B/log B).
For p<=sqrt B, use 1+log(B/p)>=0.5 log B and the harmonic prime sum. For p>sqrt B, use logarithmic bands i=floor(log(B/p)), each of harmonic prime mass O(1/log B) by the elementary upper bound pi(t)=O(t/log t); sum 1/(1+i) over i<=0.5log B. Since 1+B/p<=2B/p, the total candidate q count summed over p is O(B log log B/log B) per fixed tuple of all other coefficients and offsets. There are O_L(log^(2alpha) B H^3 (1+z)) such tuples, including the v range and the bounded LOW gains/signs. Multiplying by BW gives
    V_equal_top = O_L(X W log^(2alpha) B H^3(1+z) log log B/log B).
This is o(X) whenever 2alpha+3beta+gamma+delta<1. For alpha=1/16 and beta=gamma=delta=1/8, lambda=1/4, it is O(X log log B/log^(1/4) B). The previous small-product theorem also applies with these choices since 3beta+gamma+delta+lambda=7/8<1. With the uniform cap one can replace W by1 in this theorem and gain its entire exponent. Importantly, no lower bound on p except what follows from the large-product inequality is needed. This removes the equal-offset top-parent class even when p is far smaller than both parents. It does not cover unequal offsets.

## 4. Theorem B: power-separated current prime, broad parent bands

Fix theta,epsilon>0, theta<1, and suppose q,q'>=B^theta and
    p <= min(q,q')/B^epsilon.
Retain the large-product and short-clock/short-index/short-lag conditions of section1 and impose normalized whole parent mass caps m<=qW,m'<=q'W. These hold automatically above the hybrid floor exponent eta<theta. The stronger separation allows a uniform two-form sieve at a power-sized progression length. We prove
    V_equal_sep=O_(theta,epsilon,L)(X W H^3(1+z)(log log B)^3/log B)
       =o(X) if 3beta+gamma+delta<1.
There is no top-band assumption on q,q'.

Proof. Orient the pair so q<=q', which just changes the signs of j,e and swaps the offsets. Use dyadic bands Q<=q<2Q, Q'<=q'<2Q' with Q' >= Q. Thus Q>=B^theta/2. The quotient count v<=O(X/(Q Q')) holds since C+s=vqq' and C=O(X); the expression X/(QQ') is bounded below by a positive constant because QQ'<=B^2=O(X). Fix v,k,k',j,e,p and the bounded LOW gains/signs. The quadratic gives at most two q classes modulo p. In addition the integrality of q'=(kq-d)/k' gives either no solution or a congruence on q modulo k'/gcd(k,k'), coprime to p since p>H. Thus parameterize q and q' as two integral affine forms in one integer l, with slopes p k'/gcd(k,k') and p k/gcd(k,k'). Their determinant is nonzero since d!=0, and the possible exceptional primes divide 2pkk'd, an integer O(B^2 polylog B). The parameter interval is contained in one of length comparable to Q/p, at least B^epsilon/2 because p<=q/B^epsilon and q<2Q. For sufficiently small fixed sieve cutoff B^c depending on theta and epsilon, with level B^(min(theta,epsilon)/4), actual q,q' exceed the cutoff; outside exceptional primes the two forbidden roots are distinct. The same dimension-two upper-bound sieve used in preceding notes gives O_(theta,epsilon)((Q/p)(log log B)^2/log^2 B) candidate prime pairs, uniformly. The residue error O(B^(min(theta,epsilon)/4)log B) is absorbed by Q/p >= B^epsilon/2. The exceptional sieve product costs O((log log B)^2), by the earlier product bound.

Each (v,q,q') determines C and both previous keys. Each possible tuple can account for at most 2Q W matched pairs. Sum over the O(X/(QQ')) possibilities for v. For the fixed dyadic parent bands and other coefficients, summing over p gives
    O(X W (Q/Q') (log log B)^3/log^2 B)
by the harmonic prime sum. Sum over Q'>=Q: sum Q/Q'<=2; then over O(log B) bands Q. Finally sum O_L(H^3(1+z)) other coefficient/gain/sign choices. This proves the displayed theorem. With beta=gamma=delta=1/8 and lambda=1/4 it gives O(X(log log B)^3/log^(3/8) B). No unproved distribution of modular inverses is used. The equal-offset reduction is the reason the v count, short congruence and sieve combine without paying the full CRT +1 term.

## 5. Unequal offsets and exact residual

For s1!=s2 we retain
    q a1-q'a2=s1-s2,
    (k'a1-k a2)q+d a2=k'(s1-s2),
and p|q a1+(sigma-s1), p|q'a2+(sigma-s2).
These constrain the quotient pair. Unlike the equal-offset case, q q' does not divide either common shifted integer, and v=C/(qq') is not an integer parameter. Merely bounding each quotient by O(X/q) or O(X/q') and applying these congruences separately does not give the saving in sections3-4. No aggregate upper bound for the unequal-offset class was obtained. Equal-offset cases with intermediate ratio p/min(q,q') outside the two theorems also remain, as do the other previously unresolved large-height, long-lag, reset/reset, small-label and mass-overconcentration classes. The new theorems remove only specified parts of the previously untreated large-product residual, not all asynchronous pairs.

## 6. Exact finite verification

Extended the previous asynchronous matching script with exact divisor-side recovery and all quotient identities above, including the quadratic congruence and the t=0 product upper bound. Executed saved function bodies:
    node research/min_asynchronous_quotient_audit.mjs 256 1024 4096 16384 65536 262144
Preserve both original diagnostic rules (uniform floor(B/4) and hybrid 4 max(ceil(sqrt B),p)), original cutoff tags and exactly the prior sorted-half matching. Counts match prior audit for every window. At every pair with both previous highs verify the quotient identities. For distinct p,q,q' with product>X, partition by actual s1=s2 or s1!=s2; check the quadratic for every equal-offset pair including finite k=0 cases. Exact script and JSON remote readback at da1965637fc1d4ad9c16896067777190b2aa1244.

|X|uniform large product|equal offset|unequal offset|hybrid large product|equal offset|unequal offset|
|--:|--:|--:|--:|--:|--:|--:|
|4096|66|13|53|50|4|46|
|16384|167|44|123|169|25|144|
|65536|519|89|430|606|109|497|
|262144|685|29|656|1879|274|1605|

At X262144 the equal-offset class contains 12 (uniform) and 103 (hybrid) pairs with both parent indices positive. None has both parents >=B/2 in either run. The loose diagnostic p<=min(q,q')/B^.125 holds for 2 and 60 respectively of those both-positive equal-offset pairs; this ignores other theorem hypotheses and is not a count of all qualifying asymptotic pairs. No equal-offset case in these tested windows had sigma=s. A uniform example C882826,p11,q137,q'179,k5,k'1,j23,e0,s=2,sigma=1,v36: 882828=36*137*179; 36*137*179-1 divisible by11; kq-k'q'=506=2*23*11. This verifies that e=0 does not prevent the nondegenerate quadratic. A hybrid example C564630,p13,q163,q'433,k=k'=1,j=-11,e32,s=2,sigma=-1,v8 satisfies 564632=8*163*433 and 163-433=2*(-11)*13+16. The unequal-offset class dominates these finite diagnostics, so the new arithmetic saving should not be mistaken for resolving the largest observed residual.

The proof route still requires the full disjoint matching deficit or a different argument implying enough unstopped roots. The most direct continuation of the present arithmetic approach is the unequal-offset quotient equation, for which a new correlation bound is needed. No new branch, no main change, no Lean compilation.
