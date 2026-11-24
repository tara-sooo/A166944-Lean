# MIN prefix: two-form sieve, growing LOW cutoff, and multi-donor return reductions

2026-11-24 JST. Research-only continuation of the 2P-prefix paper at 640482a6b3da6140a7771ca43f40b755bbb31bd8. The deductions below use the established canonical MIN clock budget and deterministic LOW-only barrier, standard prime counting and the published upper-bound sieve. They are paper arguments, NOT new Lean-kernel theorems. The aggregate contraction and twin-prime conjecture remain open.

## 1. Setup and original-source weights

For dyadic X divisible by four, take odd M in [X,2X), s=M+2, C0=2M-2, K(M)=floor((7M-1)/4), B=ceil(sqrt(7X)). Select the lexicographically earliest (time,prime) among eligible parity clocks for odd primes <=B; the gain of selected p is p-1.

Let y>=7, L=2 product of odd primes <=y, and P=pi(B)-pi(y). Let v_M contain the first min(2P,number of HIGH(y) selections) high labels p>y, preserving the original cutoff. For sufficiently large B we will take L<=max(210,(log B)^beta), with beta>0 fixed, y maximal. Thus y tends to infinity, P~B/log B and L=o(B).

By the established LOW-only barrier, a block of primes dividing an even modulus D has total gain strictly less than D. Each LOW(y) block therefore contributes <L. All pre-event horizon states C in v_M satisfy

    2X <= C < 7X, 0 <= C-C0 <= G=2P(B+L)=O(X/log B).

The upper absolute bound follows from C<=2t<=2K(M). Since C0 for odd M is spaced by 4, a fixed pre-event pair (C,p) occurs in at most floor(G/4)+1 original sources. Each source visits C at most once. This bound counts original-source returns even if many trajectories coalesce; it does not count distinct reset states in their place.

For consecutive selected occurrences of p, let E be the total gain strictly between those p selections (excluding the gain p-1 at the first p). If the endpoint signs are sigma0,sigma1 in {-1,+1}, p divides (p-1)+E+sigma1-sigma0. The expression is positive and even for p>=5, hence is a positive multiple of 2p. In particular E>=p-1.

## 2. Uniform two-linear-form sieve

Let Q=ceil(B/(log B)^alpha), 0<alpha<1. In a dyadic band U<=p<2U, U>=Q, consider two prime-valued linear forms in one integer variable, both values >=U/3, with nonzero determinant and nonzero leading coefficients, all coefficients bounded by a fixed power of log B. The number of possible integer arguments in an interval of length O(U) is

    O(U (log log B)^2/(log B)^2).

Here is a verification of uniformity rather than an independence assumption. Choose D0=(log B)^C with fixed C sufficiently large to exceed every prime divisor of the leading coefficients and determinant; sieve only primes D0<ell<=z=U^(1/4). For large B the prime values themselves exceed z. Each included ell excludes exactly two distinct residues, and the density is g(ell)=2/ell on these primes and 0 otherwise. The dimension-2 upper bound condition (Omega0) holds uniformly (g<=min(2/ell,1-1/3)); for squarefree d composed of included primes the remainder is O(2^omega(d)). Mertens gives V(z)=O((log D0/log z)^2), and the sum of remainders for d<=z is O(z log(2z)), negligible compared with U/log^2 B. Ford, Sieve Methods Lecture Notes (Spring 2023), Theorem 2.4, printed p.18, applies. See also Theorem 2.5, printed p.19. Direct source inspected 2026-11-24: https://ford126.web.illinois.edu/sieve2023.pdf . This argument does not require admissibility at excluded small primes.

## 3. NEW paper bound for all light-background returns (arbitrary number of intervening selections)

For any fixed alpha in (0,1) and nonnegative J=O((log B)^beta), count R_light(X,Q,J): original-source consecutive p returns in v_M with p>=Q for which some intervening high selection q!=p supplies all but at most J of the intervening gain E. This includes arbitrary other selections, LOW or HIGH, before/after q; their number and order do not enter the bound.

**Claim:**

    R_light(X,Q,J) = O(XB (J+1)^2 (log log B)^2 (log B)^(2alpha-3)).
    Consequently R_light=o(XP) if alpha+beta<1.

Proof. Fix such a return and split its other gain into E1 before q and E2 after q, so E1+E2<=J. Recharge E>=p-1 gives q>=p-J>=p/2 for sufficiently large B. From the p endpoint divisibilities we get

    q = k p + c, c=2-E1-E2+sigma0-sigma1.

Since p,q are distinct primes, c!=0 (otherwise p divides q). For large B, k>=1, k=O(B/U) in the dyadic band U<=p<2U. The first and q-event divisibilities constrain C modulo p and q:

    p | C+sigma0,
    q | C+(p-1)+E1+sigma_q.

For each choice of E1,E2 and signs there are O(B/U) choices of k. The two-form sieve on p and kp+c bounds possible prime pairs by O(U (log log B)^2/log^2 B) per k. For each pair CRT gives at most 1+5X/(pq)=O(X/U^2) pre-event C values, using X~B^2/7. Summing over the O((J+1)^2) gain choices, constant sign choices and dyadic bands U>=Q, the number of possible (C,p) is

    S_light <= O((J+1)^2 * XB/Q^2 * (log log B)^2/log^2 B).

Indeed the band sum is geometric in U^-2. Multiplying by the original-source fibre bound O(X/log B) from section 1 proves the claim. Each return has a unique first endpoint for its source and p, so counting state-label pairs bounds the number of returns even if several witnesses q exist.

This saves one further factor of log B (up to log log factors) versus the previous count that used primality only for p. For fixed LOW7 and J=420 it permits ANY alpha<1 (previous alpha<1/2).

## 4. NEW deterministic exclusion of repeated single-donor type

Suppose the high labels strictly between the consecutive p selections have at most one distinct value q. If there are no such labels, E<L, excluding p>=Q for large B. If q occurs at least twice, any consecutive q occurrences in this interval have only LOW labels between them. Recharge for q gives q-1<L, hence q<=L-1 (L is even, q odd). Every donor label in the entire p-free interval divides the even modulus Lq. The same deterministic barrier, now with modulus Lq, shows

    p-1 <= E < Lq <= L(L-1).

Since Q grows faster than L^2, this is impossible for large B. Thus the only remaining single-distinct-high-donor pattern has exactly one q; it is covered by section 3 with J>=2L. In particular p,q,q,p is excluded for all p>=Q eventually, not merely at the initial positions. The argument applies also to any number of consecutive q high selections.

## 5. NEW two-donor restrictions and weighted bounds

Consider consecutive p returns with exactly two intervening high labels q,r, q!=r, with LOW blocks between the four highs. Let E0 be the sum of the three LOW-block gains, so 0<=E0<3L. The endpoint signs imply

    q+r=k p+c, c=3-E0+sigma0-sigma3.

Here c is odd and <=5; k is a positive odd integer (the expression q+r-c is positive). In particular if 3p>=2B+3L, then k=1 and

    min(q,r) <= (p+5)/2.

This excludes two top donors both exceeding that half-bound in a top-band return.

For R>=1 of polylogarithmic size, let R_two(X,Q,R) count the original-source two-donor returns for which min(q,r)<=R OR |q-r|<=R. The union is counted at most by the sum of its two classes.

**Claim:**

    R_two(X,Q,R)
      = O(XB (L+1)^2 (R+1) (log log B)^2 (log B)^(2alpha-3)).

In particular, if L=O(log^beta B), R=O(log^gamma B), and 2alpha+2beta+gamma<2, this is o(XP).

Small-donor case. Fix the smaller donor s<=R, its position, the sum E0 and the total LOW gain preceding the larger donor u. These gain variables each range over O(L+1) choices, and signs contribute only a constant. The return equation yields u=kp+c-s. By recharge q+r>=p+1-E0, so u>=p/2 for sufficiently large B. Its nonzero offset c-s cannot vanish because u and p are distinct primes. The two-form sieve applies to p,u. Fixing the donor position and gains before u, the divisibility of p at C and of u at C+(p-1)+(optional s-1)+preceding LOW gain fixes one CRT class modulo pu. Thus the bound on state pairs is exactly as in section 3 with O((L+1)^2(R+1)) choices in place of O((J+1)^2).

Close-donor case. Fix d=r-q with |d|<=R, E0, the LOW gain before q, and signs. Then 2q=kp+c-d. Recharge gives q>=p/3 for large B. Write p=2n+1 and q=kn+(k+c-d)/2 (only integral cases occur). The two forms have nonzero determinant c-d (c odd, d even) and polylogarithmic coefficients. The sieve bounds possible p,q prime pairs by the same expression. The first p and first donor q divisibilities determine C modulo pq. Sum over d, gains, signs, k and dyadic bands, and multiply by the same original-source weight bound, giving the claim.

The two-donor estimate does NOT cover unrestricted q,r of intermediate or large size separated by large differences; it only removes the specified subclasses.

## 6. Sharpened sufficient twin-prime criterion

Use the following single parameter choice, asymptotically:

    alpha=2/3, beta=1/6, gamma=1/4,
    L maximal LOW primorial <= max(210,log^(1/6) B),
    Q=ceil(B/log^(2/3) B),
    a=ceil(log^(1/3) B),
    J=3L+ceil(log^(1/6) B),
    R=max(31,ceil(log^(1/4) B)).

Let n(M,p) be the multiplicity of p in v_M, D=sum_{M,p>y}(n-1)_+, and

    A=sum_{M,y<p<Q} (n(M,p)-1-a)_+.

Let R_res count consecutive p returns (p>=Q) having >=2 DISTINCT high donor labels, excluding light-background returns (E minus largest donor gain <=J) and excluding two-donor returns with min(q,r)<=R or |q-r|<=R.

The small baseline is at most (X/2)*pi(Q)*a=O(XP/log^(1/3) B). All zero/single-distinct donor cases are eliminated or light for sufficiently large B. The light and two-donor excluded terms satisfy, respectively,

    R_light/(XP) = O((log log B)^2/log^(1/3) B),
    R_two/(XP) = O((log log B)^2/log^(1/12) B).

Hence the paper deductions imply

    D <= A + R_res + o(XP).

The existing canonical MIN clock bound gives K(M)-s <= (H_y(M)+1)(2B+3L) for a non-twin terminal. Since 2P*(2B+3L)=o(X), every non-twin source in sufficiently large windows has >=2P high selections, and at least P repeat labels in its prefix. Therefore the **OPEN** sufficient condition

    liminf_(dyadic X) (A+R_res)/(XP) < 1/2

implies infinitely many twin primes. Each successful terminal has C-1>=2X-3. The remaining estimate is still a substantial arithmetic problem; no contraction or general source-weighted multi-donor bound has been obtained. For A it would suffice to prove a uniform O(log^delta B) average small-label multiplicity with delta<2/3, on the same windows; the improved cutoff permits a longer tail threshold than before. These are sufficient conditions, not established estimates.

## 7. Finite source-counted audit

Code: research/min_multidonor_audit.cpp. Independent C++17 clock and literal parity-GCD comparator, preserving actual original source and cutoff. Run:

    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_multidonor_audit.cpp -o /tmp/min_multidonor_audit
    /tmp/min_multidonor_audit 256 1024 4096 16384 65536 262144 1048576 4194304

Compiled and executed successfully with these flags. Local tested code Git blob d88e0b13d595712aa41e273ce502439e30c67afc, remotely read back identically at a13263ac164585df1443a2de62678a21bd06f09e. 6140 literal clock comparisons at the two smallest windows. The code checks recharge, low-block gain, single-distinct barrier, endpoint congruences, odd k, top-band restriction, origin span, and light-gain identity. In all listed finite windows y=7, L=210, J=632, R=31; the two cutoff choices in the code are alpha=1/3,a=ceil(log^(1/6) B) and alpha=2/3,a=ceil(log^(1/3) B). The first is a comparison; the latter implements section 6. The finite data do NOT test an actually increased y. For the improved cutoff:

| X | Q | D | A | large mixed | light multi | residual | max small doubling ratio |
|--:|--:|--:|--:|--:|--:|--:|--:|
|256|18|107|2|5|5|0|.361446|
|1024|32|109|0|1|1|0|.112399|
|4096|58|2174|196|13|13|0|.259515|
|16384|105|12840|1908|26|22|4|.252494|
|65536|195|74022|13303|212|171|41|.265498|
|262144|364|425129|103336|426|282|144|.271745|
|1048576|683|2292324|675019|386|42|344|.280073|
|4194304|1292|11810091|2422567|1272|191|1081|.286900|

At X=4194304, B=5419, P=712, all 2097152 sources stopped at twin terminals before exhausting their 2P-prefix limit. A+R_res=2423648, about 0.162315% of XP/2=1493172224. This percentage compares only the remaining terms with the asymptotic criterion, NOT an exact finite certificate: the o(XP) bounds have unspecified constants and the clock length condition is not met at this scale. At this largest X the earlier alpha=1/3 cutoff has Q=2646, A=3878989, large mixed=142, light multi=80, residual=62. No distinct two-donor returns at either large cutoff for X>=4096; this is a finite observation only, and many small-label two-donor returns exist (1592827 two-donor checks over all p>7 at the largest window). The finite test supports the exact structural restrictions, not an asymptotic extrapolation.

Status PARTIAL: new paper upper bounds and structural reductions, finite tests PASS, no new Lean compilation and no proof of the remaining sufficient condition. Main untouched.
