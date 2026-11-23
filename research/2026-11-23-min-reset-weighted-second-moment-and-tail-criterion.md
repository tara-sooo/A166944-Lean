# Twin-prime-first: first-reset weighted second-moment bridge and exponential-tail target

Date: 2026-11-23 JST. Focus: source-weighted renewal after the first MIN high-prime height reset, Issue #3 (related #4, parent #1). The new result is an **exact deterministic paper-level second-moment inequality**, reproducible finite arithmetic diagnostics, and a **conditional** twin-prime implication from two simpler tail estimates. Neither the tail estimates nor infinitely many twin primes are proved. The MIN LOW7 22,050-state growth ceiling 34 is exhaustive computational arithmetic, not independently Lean-kernel certified; the previous PRODUCT LOW7 certificate is separately Lean certified.

## 1. MIN wheel and first high-prime reset

For a dyadic integer X, set N=X/2, B=ceil(sqrt(7X)), I_X={odd M:X<=M<2X}, s=M+2, K(M)=floor((7M-1)/4). Run the actual parity-GCD MIN wheel: at each next nonunit event choose the smallest odd prime p<=B in the gcd, set C<-C+p-1. The canonical start is C(s)=2M-2. A HIGH selection means p>=11.

Define a *reset* at the FIRST high event (time rho) whose post-height h=2rho-C(rho) equals 0 (even rho), or 6 (odd rho). The post-state is then exactly v=(rho,2rho) or v=(rho,2rho-6). Let A_X be the set of distinct FIRST reset states attained by canonical M before its own K(M). Let w_v be the count of corresponding M, S=sum_{v in A_X}w_v<=N, Hpre_X the total high selections up to AND INCLUDING the first reset for those M, or all high selections for M with no reset, and Hpost_X the remaining high selections. Hence H_X=Hpre_X+Hpost_X.

For each reached v, define U_v as the count of subsequent high MIN selections from v up to the COMMON Kmax=K(2X-1), deliberately extended past some source-specific cutoffs. Since dynamics before the cutoff depend only on (time,C,B), exact coalescence gives

    Hpost_X <= sum_{v in A_X} w_v U_v.                 (ENVELOPE)

The inequality was equality in all eight finite audit windows, but equality for all X is not claimed.

## 2. NEW exact fibre L2 bound via growth energy

Let E_X be the sum, over RESETTING sources M, of the partial gain G_rho(M)=C(rho(M))-(2M-2)>=0 at their first resets. Fix any reset atom v=(rho,C_v) with k=w_v distinct odd sources M_1<...<M_k. Their partial gains satisfy

    G_i=C_v-2M_i+2; G_i-G_{i+1}>=4, G_k>=0.

Therefore sum_{i=1}^k G_i>=2k(k-1). Summing over the DISJOINT first-reset fibres,

    sum_v w_v(w_v-1) <= E_X/2,
    sum_v w_v^2 <= S+E_X/2.                       (FIBRE-L2)

This is exact combinatorial arithmetic, including source coalescence.

A second bound uses MIN's special LOW7-only segments: the exhaustive 22,050-state MIN graph gives cumulative low-only growth at most 34 from ANY even state (including any prefix), also in the presence of high raw-clock ties that MIN does not select. Before and including a first high-reset, if the source has h>=1 selected high events, there are at most h interspersed low-only segments, each with gain<=34. Every high selection adds p-1<=B-1. Thus G_rho(M)<=(B+33)h. Summing,

    E_X <= (B+33)*Hpre_X.                           (ENTRANCE-CHARGE)

Combining FIBRE-L2, ENTRANCE-CHARGE, ENVELOPE and Cauchy-Schwarz, put V_X=sum_{v in A_X} U_v^2 (UNWEIGHTED over reached atoms). For every dyadic X,

    BOXED:
    H_X <= Hpre_X
           + sqrt( [S + (B+33) Hpre_X/2] * V_X )
       <= Hpre_X
           + sqrt( [N + (B+33) Hpre_X/2] * V_X ).   (L2-BRIDGE)

No independence assumption, Fourier equidistribution, invariance of an induced dynamical measure, or unweighted replacement of w_v is used. This is an upper bound, not yet an asymptotic estimate.

## 3. A mathematically sufficient pair of weaker asymptotic estimates

Suppose for some fixed nonnegative exponents alpha,beta with alpha+beta<1, along arbitrarily large dyadic X,

    Hpre_X = O(X B^alpha),
    V_X = O(X B^beta).                              (TWO-MOMENTS)

Then L2-BRIDGE gives

    H_X = O(X B^alpha + X B^((1+alpha+beta)/2)) = o(XB).

As there are at most N*pi(B)=O(XB/logB)=o(XB) distinct first high-owner selections, R_X<=H_X=o(XB). The established LOW7 event-block/squarefree-MIN terminal certificate then yields INFINITELY MANY TWIN PRIMES. This is a logically correct *conditional implication*, not a proof of TWO-MOMENTS.

An attractive stronger candidate is a pair of exponential tails at logarithmic scale. Let
    L=log(2X),
    a_X(t)=#{odd M in I_X: Hpre(M)>=t},
    b_X(t)=#{v in A_X: U_v>=t}.
If for some universal constants C,c>0 and every t>=1 eventually

    a_X(t) <= C*N*exp(-c*t/L),
    b_X(t) <= C*|A_X|*exp(-c*t/L),                  (TAIL-LOG, OPEN)

then summing tails yields Hpre_X=O(X L) and
    V_X=sum_{t>=1}(2t-1)b_X(t)=O(X L^2).
Consequently L2-BRIDGE gives

    H_X=O(X L + X sqrt(B)*L^(3/2))=o(XB),

and hence infinitely many twins. Unlike an unsupported claim that w_v and U_v are independent, TAIL-LOG only concerns TWO UNWEIGHTED marginal distributions. Its proof is the current mathematical obstruction.

Even a power saving instead of logarithmic tails suffices: alpha=1/2 and beta=1/4 are one example of TWO-MOMENTS. These are not established either.

## 4. Genuine finite experiments and independent literal checks

Strict C++17 event-jump auditor: research/min_reset_weighted_moments.cpp, with -O3 -Wall -Wextra -Werror. It checks ENVELOPE, FIBRE-L2, ENTRANCE-CHARGE and computes high-count moments. An independent per-integer gcd implementation, research/min_reset_weighted_moments_literal.py, exactly cross-checks X256,512,1024 (all relevant values, including first-reset gain, fibre moment and future second moment). These are FINITE checks.

       X       reached atoms  Hpre       Hpost       sum w²      V_X       Umean    weighted Umean    Pearson(w,U)
       256         28           240         151          143         346       2.5714       2.7455         +0.1276
       512         64           285         355          522         538       2.0000       2.4653         +0.2835
      1024        126           608         540          961        1207       2.1667       2.0377         -0.0685
      4096        544          4222        5177         5148       20698       4.1875       4.0008         -0.0503
     16384       2235         18583       31514        23017      171035       5.9691       5.8982         -0.0124
     65536       9064         83720      178835       113988     1156208       7.8036       7.7579         -0.0058
    262144      36726        365564      971997       536802     7910280      10.0540      10.0777         +0.0021
   1048576     148388       1593931     4971489      2467695    48666794      12.4055      12.3922         -0.0009

At X1048576 there are 401179 covered sources and max individual atom mass 94. The post-event envelope exactly matched observed 4971489 events (finite only). By X262144, doing a four-slab partition by reset time n in [X,2X) gives weighted/unweighted U means (9.5647/9.4783), (10.4424/10.3875), (10.4223/10.4328), (9.8661/9.9049): small correlations do not arise solely from mixing drastically different time scales.

A sharper *empirical tail diagnostic* tests, for EVERY positive integer t rather than just dyadic thresholds, the largest ratios

    max_t [a_X(t)/N] exp(t/log(2X)),
    max_t [b_X(t)/|A_X|] exp(t/log(2X)).

                         X       maximum pre ratio       maximum atom ratio
                       256             0.926251               0.880397
                       512             0.848347               0.848347
                      1024             0.848427               0.805339
                      4096             0.946599               0.914024
                     16384             0.964278               0.937414
                     65536             0.983593               0.962466
                    262144             0.991654               0.977480
                   1048576             0.999708               0.987555

All displayed finite runs fit C=c=1 in TAIL-LOG; the maxima often occur at t=1 and are approaching 1. This is NOT an asymptotic theorem; the constants may have to be weakened, or the shape may eventually fail. In particular, the stronger idea "Pearson covariance is always nonpositive" is FALSE already at X512 (+0.2835).

## 5. What this does and does not transfer from prior literature

Helfgott--Radziwill, *Expansion, divisibility and parity* (arXiv:2103.06853), and Helfgott's direct exposition (https://webusers.imj-prg.fr/~harald.helfgott/Expansion_1.html), use trace/moment bounds and removal of exceptional high-degree vertices to control a divisibility-graph operator. The **analogy** here is to bound the tail of the **number of selected high events U_v** on the finite set of reached reset atoms, rather than claiming a mixing law for their entrance weights. Kowalski, https://blogs.ethz.ch/kowalski/2008/09/01/demystifying-a-bit-the-arithmetic-large-sieve/, explains dual large-sieve control of squared residue-frequency sums. Neither existing theorem bounds the adaptive, source-selected U_v here; the required moment/tail theorem would be new.

**Important non-improvement warning:** if one instead bounds sum U(n)^2 over ALL possible time-indexed height-0/6 states (n,2n) for even n and (n,2n-6) for odd n in [X+3,Kmax], then the sum INCLUDES every original canonical starting state at n=M+2 odd. A bound O(X polylog X) on that much larger quantity ALONE implies twins by Cauchy on those M, without any regeneration. Hence this all-time version is not a genuine shortcut. The reached-atoms V_X is the proper, potentially cheaper, source-free-of-weights moment target; however membership in A_X is itself selected by the earlier dynamics.

The L2-BRIDGE is deterministic and solved the algebra of separating coalesced source weights from future event counts. The two marginal tail/moment estimates remain unsolved. Numerically observed near-zero correlation is not an independence proof. No Lean statement of the new inequality has yet been checked; the parent twin-prime conjecture remains open.

## 6. Reproduce

    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_reset_weighted_moments.cpp -o /tmp/min_reset_moments
    /tmp/min_reset_moments 256 512 1024 4096 16384 65536 262144 1048576
    python3 research/min_reset_weighted_moments_literal.py 256 512 1024

The literal independent oracle also checks the all-time future square sum on small X, but as explained above that object is only a diagnostic. Keep working branch research/issue-3-cross-prime-correlation; no main modification, no twin-prime proof.
