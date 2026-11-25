# Odd relay parameters and finite cubic families for a three-factor endpoint

Continuation of the two-relay normalization and cubic-gap notes (9231f33, recovered note 6f6637f). Same independent branch. This is a local necessary-condition theorem, not a proof of twin infinitude. No Lean kernel verification.

## 1. Hypotheses

Use the remaining branch from the previous notes: four successive adaptive nonunit events p,a,b,p, neither relay 3, both p waits >6, minimal return, even to odd, both adjusted endpoint deficits zero, p>=101, p^3>64(Y+1), all pre-horizons <=Y, and composite second cofactor Q. The previous proof gives p=7 mod12, a,b=1 mod3, a+b=p+1, c=a-b>0, c=6 mod12, Q=1 mod12, Q>=p+2, Q<p^2/64, D_b=2b, and c<=4r<p/2 for r=minfac(Q). Put e_a,e_b=+/-1 for even/odd relay signs. The pre-horizons are H1=p(Q-2)+1, H_a=p(Q-1), H_b=pQ-b, H2=pQ-1.

The prior note's integer quotients are u=((c+1)(Q-1)+e_a)/a, v=((c-1)Q-e_b)/b, positive with u odd and v even; the relay cofactors are 2(Q-1)-u and 2Q-1+v. Write C=-(c^2-1)+(c-1)e_a+(c+1)e_b, and k=(c+1)v-(c-1)u. Then k>0 odd and

    kb=c(c-1)u-C.
    k ab=c(c^2-1)(Q-1)+c(c-1)e_a-aC.
    k ab < (11/9)c^3 Q.                              (1)

The last inequality is the earlier cubic-gap proof; do not confuse k with number of labels. In particular k=1 mod6 for (+,-), k=3 mod6 for (-,+), k=5 mod6 for equal signs.

## 2. Factorization exclusion and coprimality

For k=1 necessarily e_a=+1,e_b=-1 and C=-c^2-1. Substitute b=c(c-1)u+c^2+1, a=b+c in the formula for Q:

    (c+1)(Q-2)=(cu-1)((c-1)u+c+2).                   (2)

Because Q>=p+2=a+b+1, u>c+1, both factors on the right exceed c+1. If Q-2 were prime, one factor would be divisible by it, and the other would divide c+1, impossible. Thus k=1 is excluded whenever the first cofactor is prime (whether by dynamics or direct primality).

Also gcd(k,c-1)=1: reducing kb=c(c-1)u-C modulo any common prime l gives 0=-2e_b mod l, impossible since c-1 odd. If l divides k and c+1, reduce to u=-e_a mod l, while a u=e_a mod l from (c+1)(Q-1)=au-e_a. Thus a=-1 mod l and b=a-c=0 mod l. In the range b>c+1 this contradicts primality of b, so gcd(k,c+1)=1 there. No coprimality claim for the exceptional case b<=c+1.

Since c=2 mod4, Q=1 mod4, u=e_a*a mod4 and v=(1-e_b)b mod4. As b=-a mod4, k=a(1-e_a-e_b) mod4. Combining with mod6 and (2), the lower k values for first cofactor prime are: equal signs a=1 mod4:11; equal signs a=3 mod4:5; (+,-) a=1 mod4:13; (+,-) a=3 mod4:7; (-,+) a=1 mod4:9; (-,+) a=3 mod4:3. These are necessary lower bounds, not attainability claims.

## 3. Odd difference parameter and balanced quantization

Let j=u-v, a nonzero odd integer, possibly negative. Eliminate Q:

    j ab=Q(p+1-c^2)-b(c+1-e_a)+a e_b.                (3)
    2u=k+(c+1)j, 2v=k+(c-1)j.
    k-j=2 mod4, j=1+e_a+e_b mod3.                   (4)

This yields the exact inequality
    Q*abs(p+1-c^2) >= ab-b(c+2)-a
because abs(j)>=1. Thus the gap cannot lie in an arbitrarily small band around sqrt(p) in balanced scale.

Along any family with p tending to infinity and Q<=A p for fixed A>=1, c<=4sqrt(Q)=O_A(sqrt(p)), ab=(p^2/4)(1+O_A(1/p)). Uniformly,

    j=(4Q/p)(1-c^2/p)+O_A(p^(-1/2)).                 (5)

In particular if Q/p->1 then j<=3 eventually, hence c^2/p>=1/4-o(1). Then r>=c/4=Omega(sqrt(p)), and r^3>Q for large p. The composite Q must be semiprime, with both factors of order sqrt(p), counting multiplicity. More generally if Q has >=3 prime factors, r<=Q^(1/3), hence c<=4Q^(1/3)=O_A(p^(1/3)). Equation (5) improves to

    Q/p=j/4+O_A(p^(-1/3)).

Here j is positive odd >=5 eventually. Equal positive relay signs force j=0 mod3 and thus j>=9; opposite signs force j=1 mod3 and j>=7; equal negative signs force j=2 mod3 and j>=5. So the respective lower limits for Q/p are 9/4,7/4,5/4. This excludes three-factor Q near Q/p=1. Four or more factors are impossible for large p in balanced scale by the earlier r^3 Q lower bound and r^4<=Q. The result is a restriction on the surviving branch, not every adaptive cofactor.

## 4. Finite cubic polynomial families for three factors and Q<=2p

If Q has three factors, c^3<=64Q and (1) give k<11264 A^2/27 using ab>3p^2/16. Thus k and j have boundedly many possible integer values. With A fixed, c tends to infinity by the earlier cubic gap. For each fixed pair (k,j) and signs, the exact inverse parametrization is

    u=(k+(c+1)j)/2, v=(k+(c-1)j)/2,
    b=(c(c-1)u-C)/k, a=b+c, p=a+b-1,
    Q=(au-e_a)/(c+1)+1.                             (6)

All are rational polynomials in c; Q is cubic since the numerator au-e_a vanishes at c=-1 (after clearing denominator k). Denominator divides 4k. For fixed positive j,k,
    p~(j/k)c^3, Q~(j^2/(4k))c^3.
Since Q>=c^3/64, necessarily k<=16j^2 in the limit; odd parity makes equality impossible. Uniformly for all sufficiently large p with Q<=A p and three factors, k<16j^2: there are only finitely many possible pairs, so each pair violating this asymptotic inequality can occur only at bounded c.

Take A=2. Then j=5 or7, with only the following sign/k families possible for sufficiently large p and first cofactor prime:
    j=5, (--), k=11 mod12, k<400: 33 families.
    j=7, (+-), k=1 mod12, 1<k<784: 65 families.
    j=7, (-+), k=9 mod12, k<784: 65 families.
Total 163. This is an asymptotic classification, not a claim covering all small p.

All three waits after the first p grow unboundedly: w_a>= (a-1)/2, w_b= (3b-1+6I_b-D_a-6I_a)/2 with D_a=0 or2a and a,b~p/2, so w_b=Omega(p); w2=(c+4-6I_b)/2 tends to infinity. Thus for every fixed odd prime l, eventually l cannot divide any of H_a±1,H_b±1,H2±1, since such an eligible clock would preempt within 2l ticks. Also p,a,b,Q-2 are prime by hypothesis and tend to infinity. No avoidance condition on the other neighbor of H1 is needed.

For each family (6), M=48k is a period of integrality and all residues mod12. For each c=6 mod12 representative mod M, retain if a,b,p,Q are integral and have the necessary mod12/mod3/parity values. For each prime l=5..47, enumerate the l lifts c+M*t, 0<=t<l. The denominator bound 4k implies the polynomial values mod l are periodic under t->t+l. Retain the base class if for each l some lift avoids l in all ten integers p,a,b,Q-2,H_a±1,H_b±1,H2±1. If not, no sufficiently large c in that class can be an actual target. Choices of t mod distinct primes can be combined by CRT, so surviving classes are locally consistent for this finite sieve, not necessarily prime or actual.

Exact ECMAScript BigInt enumeration: 163 families, 71 with integral compatible base classes (220 classes); 25 families survive the finite-prime test (86 base classes). 98 base classes rejected first at l=5, 28 at7, 8 at11. Breakdown: (--,j5) 33->13->9; (+-,j7) 65->18->6; (-+,j7) 65->40->10. Surviving k lists:
    (--,5): 11,83,131,143,179,239,251,263,311
    (+-,7): 109,169,241,529,541,709
    (-+,7): 45,165,225,297,345,417,465,477,597,765
Independent SymPy factorization of six prime-required polynomials p,a,b,Q-2 and both relay cofactors for the 25 surviving families found none reducible over Q. This does not imply simultaneous prime values. The case Q semiprime is not classified by the finite family reduction. No unbounded exclusion yet.

## 5. Diagnostics

[Odd parameter audit 4e06ada](https://github.com/tara-sooo/A166944-Lean/blob/4e06ada690a1ec4106377ad0c61cb01b5ab4cf87/research/min_direct_relay_odd_parameter_audit.mjs), blob a2eabdaf92fc6c62c5f514cb719cb0bb1e517a03, exact remote readback. Run node research/min_direct_relay_odd_parameter_audit.mjs 50000. Actual function executed in ECMAScript tool runtime. All 2,868 prior CRT scale candidates verified (3),(4),(6), gcd conditions and the k=1 factorization: one k=1 case, Q-2 composite; 556 candidates with Q-2 prime, none k=1. Of 87 composite short-wait candidates, two have >=3 factors, neither Q/p<1.25; the finite scan has no actual descending composite-endpoint return. These are candidate counts, not actual trajectories.

The local sieve code is separately stored or attached with this note. All counts were computed, not inferred from a prime-distribution model. Previous note recovered at 6f6637f; previous standalone audit/results recovery was attempted separately, and new audit is self-contained. No main or sibling branch changes. The unresolved global step remains forcing unbounded reset-to-reset short returns or another stopping principle; the narrow three-factor branch now has a finite set of algebraic families in balanced Q<=2p, but the remaining 25 and the semiprime branch are not excluded.
