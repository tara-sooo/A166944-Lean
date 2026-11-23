# Twin-prime-first: LOW7 reset-ghost CRT, two-step large-band sieve, and the open-path obstruction

Date: 2026-11-23 JST. Scope: Issue #3, cross-check #4, parent #1. This is a substantive attempt on the **unweighted future high-event second moment** after a MIN-wheel first high reset. Results below are exact elementary paper deductions with fully finite integer replay, plus explicit still-open long-path estimates. There is **NO proof of infinitely many twin primes** and no new Lean kernel check in this checkpoint.

## 1. The exact target

Let X be dyadic, B=ceil(sqrt(7X)), and let A_X be the actual first high (p>=11) reset atoms from odd canonical MIN-wheel starts M in [X,2X). A reset atom at time n is v(n)=(n,C_0(n)), where

    C_0(n) = 2n - delta(n), delta(n)=0 for even n, 6 for odd n.

Let U_B(v(n)) count subsequent selected p>=11 events until Kmax=floor((7(2X-1)-1)/4). The prior exactly derived, paper-level L2 bridge proves

    H_X <= Hpre_X + sqrt([X/2+(B+33)Hpre_X/2] * V_X),
    V_X = sum_(n in A_X) U_B(v(n))^2.

It is sufficient (still open) to show Hpre=O(X B^alpha) and V_X=O(X B^beta) for alpha,beta>=0, alpha+beta<1, along unbounded dyadic X. This note attacks the **first and second high events after a reset**, but does not prove the full moment bound.

## 2. Exact 210-class LOW7-MIN reset ghost and a 1195-class incidence theorem

Start the MIN wheel at v(n) for arbitrary integer n, with only primes {3,5,7} enabled, and record the cumulative selected gains E at each prefix, **including zero**. The state of this small wheel is determined entirely by n mod 210: t=n (mod210), C_0(n)/2=n-delta(n)/2 (mod105). This is a 210-state *reset-origin* slice of the full 22050-state LOW7 graph.

For residue r in {0,...,209}, let G_r be the finite set of all those prefix gains; set

    D_r = { E-1, E+1 : E in G_r }.
    
All values of E are even. Exhaustive 210-residue integer computation, independently verified by direct integer-by-integer gcd (no jump formula), gives:

    sum_(r=0..209) |D_r| = 1195;
    max_r |D_r| = 16;
    max_(r,E in G_r) E = 32;
    max LOW7 event count on this reset slice = 9.

The universal LOW7-MIN total-growth bound from ALL 22050 residue states is 34 (separately computed in the prior project); the 32 bound is only for the reset slice.

Until the FIRST selected high prime p>=11 appears in the full MIN wheel, the selected LOW7 events coincide with a PREFIX of this LOW7-only ghost. Even a tied high raw factor is ignored when the MIN policy selects a smaller low prime. Hence, for the first selected high p, necessarily

    p | 2n-delta(n)+a for some a in D_(n mod210).  (FIRST-HIGH-CRT)

This is an arithmetic condition on the **initial reset time n**, not an independence hypothesis. Fix any integer interval I of length T and any finite prime set P all p>=11. Because gcd(210,p)=1, for every r,a,p the two congruences n=r (mod210) and 2n-delta(r)+a=0 (modp) select exactly ONE residue class mod 210p. Summing the interval occupancy yields the unconditional inequality

    # { n in I : first selected high prime exists and belongs to P }
       <= (1195/210)*T*sum_(p in P)1/p + 1195*|P|.   (ONE-STEP)

For P={p: B/2<=p<=B} and T=O(X), PNT/Mertens gives O(X/log B); the +|P| term is O(B/logB)=o(X/log B).

The same 210-class ghost applies at every ordinary canonical start s=M+2, because s is odd and C(s)=2s-6.

## 3. Two distinct first high selections in the same large band

Suppose the FIRST TWO selected high-prime events after v(n) use p,q>=37. Their labels MUST differ: between two consecutive selections of p with no other HIGH selection, only LOW7 selected events intervene, with total growth <=34<p-1. Thus p≠q.

Let E_0 be the total LOW7 gain before first high selection p, and E_1 the gain between first high p and second high q. They are even and lie in [0,34]. The two selections require, for some signs eps_0,eps_1 in {-1,+1},

    p | 2n-delta(n) + E_0 + eps_0,
    q | 2n-delta(n) + E_0 + (p-1) + E_1 + eps_1.  (TWO-HIGH-CRT)

There are at most 18 choices each of E_0,E_1 and four sign pairs. For FIXED distinct p,q and parity of n, these are two independent affine residues modulo p,q; CRT gives ONE class modulo pq within that parity. Across both parities, the number of possible n in an interval I of length T is at most

    1296 * (T/(p*q) + 2).                            (PAIR-CYLINDER)

Let P be a dyadic prime band [Q,2Q) with Q>=37 and 2Q<=B+O(1), and s=|P|, sigma=sum_(p in P)1/p. Summing PAIR-CYLINDER over distinct ordered labels gives

    # { n in I : first two selected high primes both in P }
       <=1296 * (T*sigma^2 + 2*s^2).

For T=O(X) and Q<=B=O(sqrt X), PNT implies O(X/(log Q)^2) when Q tends to infinity and Q is a dyadic band of comparable primes. In particular this applies to top-half P=[B/2,B] for B sufficiently large. This is a GENUINE two-step sieve saving but does not address interleaved small-high donors.

## 4. Three high selections q,r,q: a repeated-label rank gain

Suppose the FIRST THREE selected high primes from a reset are q,r,q, with q>=B/2, q>=37, and r>=11. Between the two q hits there are precisely two LOW7-only segments, of combined growth L<=68. The selected r event contributes r-1. The necessary q-recharge congruence is

    q | (r-1+L-c),  c in {-1,1,3},
    or r-k*q = 1+c-L in [-68,4].                    (SINGLE-DONOR-RESONANCE)

Since r<=B and q>=B/2, for sufficiently large B the integer k must be 1 or 2. For each q, r lies in one of TWO intervals of bounded length around q and 2q, so there are O(1) possible integer r, even before primality. The two FIRST high selections q and r satisfy TWO-HIGH-CRT; their labels are distinct and qr is comparable to B^2. Consequently, among ALL reset-time starting integers n in an interval of length T=O(B^2),

    # {n : first three high selected labels are q,r,q with q in [B/2,B]}
       = O( pi(B) * (T/B^2+1) )
       = O(B/log B).                                (THREE-RETURN)

This is a real saving past the usual CRT +1 saturation, specifically for the repeated label (the rank relation eliminates one free prime label). The implied constant is large and the bound is not a statement about all q-returns or arbitrary third fresh primes.

## 5. A separate unconditional static second moment

For an integer reset time n write Z_P(n)=# {p in P: p|(C_0(n)-1)(C_0(n)+1)}, with P any set of odd primes >=11. Let s=|P| and mu=2 sum_(p in P) 1/p. On each parity class n=2m+e, each p imposes EXACTLY two distinct residue classes m modp, and each pair p≠q imposes four classes modpq. For any integer interval I of length T, elementary CRT second-moment expansion gives

    sum_(n in I) Z_P(n)^2 <= T*(mu+mu^2) + 8*s^2.   (STATIC-L2)

For P in [B/2,B] and T=O(X), B^2=O(X), this is O(X/log B). This holds unconditionally over ALL reset-time states, hence over the reached atoms A_X as a subset. It does NOT bound the future U_B(n): a p not active at the initial reset can be activated later by selected events.

A strict finite audit X1048576, B2710 on the 2621436 possible reset-time n found static sum Z^2=585854, while 19341 of the 148388 actually reached first-reset atoms had NO initially active p>=B/2 but subsequently selected a p>=B/2. This explicitly refutes the naive inference 'no initially active top prime => no future top selection'.

## 6. Exact spectral difficulty and the true longer-word obstacle

For the forward map Phi(v) = post-state after the NEXT selected high event (if any before Kmax), define (Tf)(v)=f(Phi(v)) if Phi exists, zero otherwise. All genuine edges strictly increase the event time. Consequently T is nilpotent on any finite horizon and

    Tr(T^k)=0 for ALL k>=1.

The actual required future-tail count is an **OPEN PATH sum**,

    b_X(k) = # { v in A_X : U_B(v)>=k }
           = < 1_A, T^k 1 >.

The Helfgott--Radziwill *Expansion, divisibility and parity* trace method applies to a very different **symmetric** prime-divisibility graph, where Tr(A^(2k)) counts closed walks. Its theorem assumes a much shorter prime range, e.g. log H <= (log N)^(1/2-epsilon), while B~sqrt X violates that range. Literal forward-trace substitution is zero, not a useful moment bound; the missing object is a source-/survivor-conditioned open-path or singular-value estimate that survives adaptive coalescence. Their *lone prime / repeated label* rank method is nonetheless an exact algebraic model for section 4. Primary: https://arxiv.org/abs/2103.06853 and https://webusers.imj-prg.fr/~harald.helfgott/Expansion_1.html .

The classical large sieve DOES have the critical (T+Q^2) scale at Q~sqrt T (Tao, https://terrytao.wordpress.com/2015/01/10/254a-notes-3-the-large-sieve-and-the-bombieri-vinogradov-theorem/). But applying it to the adaptive images Phi^k(n), rather than fixed linear forms in n, needs a NEW pushforward discrepancy/moment theorem. First TWO high labels p,q can be summed at O(T/log^2B), since the CRT +1 over O(pi(B)^2) pairs is acceptable. For THREE distinct fresh top labels, raw CRT enumeration contributes O(pi(B)^3)=O(X^(3/2)/log^3 X), which swamps the entire O(X)-sized source interval. The q,r,q resonance in section 4 solves only the repeated-label subclass.

The earlier proposed log-scale exponential tail b_X(t)<=C X exp(-c*t/log X) is stronger than it appears: because b_X(t) is INTEGER, it forces max_(v in A_X) U_B(v)=O((log X)^2). The TWO-MOMENTS condition in section 1 is weaker and is the more flexible immediate goal.

## 7. Exact tests and interpretation

The 210-residue LOW7 reset-prefix table was computed by first-hit jumps and independently checked for EVERY residue against direct per-integer gcd. Finite full MIN scans of all reset-time n in [X+3,Kmax] and actual reached atom subsets give:

    X       B    all time states   first TOP all   first TWO TOP all   first THREE q-r-q TOP all    first TWO TOP reached
       256     43             636              29                   0                          0                        0
      1024     85            2556             295                  27                          1                        0
      4096    170           10236             580                  25                          0                        0
     16384    339           40956            1808                  61                          0                        1
     65536    678          163836            5142                 236                          0                       11
    262144   1355          655356           13909                 353                          0                        9
   1048576   2710         2621436           44697                 694                          0                       24

For these diagnostics TOP means selected p>=max(37,ceil(B/2)), not the literal B/2 lower end for small B<74. The q-r-q example at X1024 has initial reset time n=1271, high labels (43,29,43) selected at times (1290,1307,1335), low gain L=14. An independent literal n-by-n parity-GCD implementation agrees on full all-time first-two counts for X256 and1024 and q-r-q counts X256,1024. These are finite tests, not asymptotic proofs.

The practical next analytic target is **to sum THREE-AND-MORE fresh high-label paths without a pi(B)^3 CRT remainder**, e.g. a stopped large-sieve inequality or source-conditioned open-path moment estimate on the induced MIN clock operator. The one- and two-step CRT facts and the repeated-label resonance are proven elementary inputs to such an estimate, not a solution of that open problem.

Verification classes: sections 2-5 elementary PAPER proofs with finite literal verification of their small ghost premise; table finite computational evidence; section 6 exact linear-algebra observation plus OPEN spectral step; no Lean build of the new lemmas, no assertion of twin infinitude, no modification of main.
