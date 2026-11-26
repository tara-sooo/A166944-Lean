# Fast direct recovery: odd multiplier shift and nearly quadratic deficit escape

Continuation of [0782bd1](https://github.com/tara-sooo/A166944-Lean/blob/0782bd1a321319f7de58dfa1ba15fd10382029fd/research/2026-11-26-min-direct-first-pair-gap-and-direct-recovery.md). Use the exact clock of the fast first high successor, not a roughness hypothesis on that successor. The adjusted multipliers satisfy an odd shifted product relation. Counting its large prime divisors and the horizon CRT yields a support-sensitive supply bound without a long CRT progression. Under the previous near-minimal GLOBAL source-support and low-relay conditions, almost all macroscopic direct-recovery word weight escapes every deficit cap T^(2-delta). At polynomial label scales the same hypotheses force a nearly quadratic deficit diameter even with an arbitrarily high baseline. These are conditional restrictions, not an exclusion of the escaping population.

## 1. Exact odd shift

Use actual MIN events on a canonical contiguous block with pre-horizons in [X,Y], Y=lambda X, lambda>1 fixed, total gain G=O_lambda(X), label cap C=floor sqrt(Y+1). Let integer T->infinity, T<=C, and fix K>=1. A first high pair consists of an upward source s with label p in [T,KT] and its next event t of label >=T, with label r in [T,KT]. All strictly intervening events have label <T. Let E be their total physical gain, V their total waits, w the target wait. Let I,J be their endpoint sides, e=1-2I,f=1-2J. For high labels >=5 the exact post-deficits are
    d'_s=2hp+6I, d'_t=2kr+6J,
with h,k nonnegative integers. We allow resets initially; in particular k=0 is permitted. Each physical event has 0<w_i<=2p_i<=3g_i, hence 0<=V<=3E, and E is even. The actual clock and horizon equations are
    H_t-H_s=p-1+E, n_t-n_s=V+w,
    d'_t-d'_s=2(V+w)-E-(r-1).
Substitution gives
    2hp-(2k+1)r=c,
    c=E-1-2(V+w)+6(J-I).                             (1)
In particular c is an odd nonzero integer; no equal-shift zero case needs separate treatment. For integer cutoffs E<=B, 1<=w<=W, define Q=5B+2W+7. Then |c|<=Q. Assume Q<T, as will hold in the application. We have h>=1: if h=0 then |c|=(2k+1)r>=T. Also E<T-1, so p!=r by the earlier same-label spacing lemma. A downward target is automatic if 2W<T-1; the counting proof does not need this extra restriction. The two exact divisibilities are
    r | 2hp-c=(2k+1)r,
    p | (2k+1)r+c=2hp.                                (2)
For fixed (p,h,c), the first expression is a positive integer for every candidate pair. Conversely, fixed (r,k,c) determines a positive integer divisible by p. These are a necessary condition on the actual fast clock, not independent prime tests for an arbitrary deficit pair.

For fixed p,r,E,I,J, H_s=e mod p, H_s+p-1+E=f mod r gives one residue mod pr. One actual first horizon on a monotone physical ray determines at most one next high event, independent of all its intermediate clocks. We need not count the relay tick sum V or the target wait w separately after c is fixed. The exact stronger congruence with h,k fixed is
    H_s=A mod 4p, H_t=D mod 4r,
    A=e+p(2I-2h-1), D=f+r(2J-2k-1).
When D-(p-1+E)-A=0 mod4 there is one starting class mod 4pr; otherwise no pair is possible. This follows from the firing parity formula n=p((q+1)/2+h)+2I. We only need the weaker modulus pr in the upper count below.

## 2. Two-sided multiplier support capacity, without long CRT progression

Consider any collection of actual first pairs satisfying these conditions, with nonnegative weights <=K_w T for a fixed K_w. We may also count bounded high words of lengths 2..J0 with such a first pair, where J0 is fixed, and the weight refers to the full word; multiply constants by J0 because each first pair has at most J0 possible such consecutive high-prefix words on the actual ray. Denote total weight by F(B,W). Let
    D_s=sum_p |{h occurring with source label p}|,
    D_t=sum_r |{k occurring with target label r}|.
These counts include actual distinct label-multiplier incidences, not visits. Both endpoint deficits are O_lambda(X) by the canonical envelope, so the positive integers in (2) are <=K_lambda X, for a fixed sufficiently large K_lambda. Let b=max(1,floor(log(K_lambda X)/log T)). A positive integer <=K_lambda X has at most b distinct prime divisors >=T. Thus for a fixed source incidence (p,h), odd c in [-Q,Q], E in [0,B], and two sides, there are at most b possible distinct target primes r, each with one horizon class mod pr. In a block of length O_lambda(X) there are O_lambda(X/T^2) possible H_s per tuple: the +1 from progression length is absorbed since T^2<=Y+1. This bound does not require T^2=o(X), let alone a CRT progression of polynomially growing length. Each candidate gives at most the fixed bounded word multiplicity. Weight by K_w T and sum. Reverse the argument using (r,k) and the other integer in (2). The result is
    F(B,W) << X/T * b (B+1)(Q+1) min(D_s,D_t).         (3)
Constants depend only on fixed lambda,K,K_w,J0; no sieve estimate or multiplier cap is required. A fixed source/target can have many different admissible multipliers; D_s and D_t count each once per label. The finite verification below tests the exact residue class and factor bounds, not an assumed uniform distribution of H.

For F(B,W)>=rho X with rho fixed positive, both supports consequently satisfy
    D_s,D_t >> T/[b(B+1)(B+W+1)].                     (4)
For T>=X^a fixed a>0, b=O_(lambda,a)(1), so the divisor multiplicity causes no logarithmic loss. For much smaller T the actual factor multiplicity must be retained, or use the capped result below.

Suppose S is the number of actual source primes, and all source post-deficits lie in a finite union of N_h intervals of total length A_h, with disjoint interiors (merge overlaps). Each source p has a lattice of possible ordinary post-deficits 2hp+6I, with two sides. For one side and interval, the number of possible h is at most 1+interval length/(2p). Thus D_s<=S(2N_h+A_h/T), counting h in both sides for an upper bound even if they coincide. In particular, if their diameter is R_s, D_s<=S(2+R_s/T). From (3),
    F(B,W) << X b S(B+1)(Q+1)(2N_h+A_h/T)/T.          (5)
This also applies at very large baselines. If T/[b S(B+1)(Q+1)] tends to infinity, a macroscopic population forces
    R_s >> T^2/[b S(B+1)(B+W+1)].                    (6)
The target diameter differs from the source diameter by at most O_K(T+Q) because their corresponding post-deficit differences are -r+c' with |c'|<=Q+6, by (1). The physical ordinary total variation on the block is at least either diameter. Equation (6) is a width obstruction and does not depend on the distance of the whole population from zero. It is different from a lower bound on absolute deficit.

## 3. Capped fast-pair supply and high-deficit escape

Suppose a subpopulation of first pairs has min(h,k)<=M for M>=0, M<=T^A with A fixed. If h<=M it is already capped on the source side. If k<=M then (1) and r<=KT, p>=T, |c|<T imply
    h <= [K(2M+1)+1]/2 = O_K(M+1).
Hence the source multipliers of the entire subpopulation are O_K(M+1), and the integer 2hp-c is O_K(T(M+1)). Its number of distinct factors >=T is O_(K,A)(1) even if T is subpolynomial in X. Use the source-side proof of (3), with D_s=O_K(S(M+1)), to get
    F_cap(M;B,W) << X S(M+1)(B+1)(B+W+1)/T.          (7)
Here the S is the actual source support of the full population or any containing set. No factor log X/log T occurs in (7); only the polynomial cap on the small endpoint was used to bound the number of possible target factors. Equivalently for 0<delta<1 the weight with either ordinary post-deficit <=T^(2-delta) is bounded by (7) with M=ceil(T^(1-delta)): that endpoint's multiplier is <=T^(1-delta)/2, and the other source multiplier is bounded as above. This bound includes reset targets, regardless of the original word's final target.

Apply the preceding direct-recovery theorem 0782bd1. Assume actual pairwise event-disjoint bounded high words with comparable labels [T,KT], total word weight F>=rho X, weights <=K_w T, source rise >=eta*(p-1), fixed rho,eta>0, and
    S=O(log^2 T), G_low=o(X log^2 T/T).
Here G_low is the full physical gain of labels <T. These are the previous additional global source-support and low-relay hypotheses, not implied by local source diversity or merely G_low=o(X). Let g_T=T G_low/X and B=ceil(max(sqrt(log T),sqrt(g_T log^2 T))), so B+1=o(log^2 T), (B+1)>=sqrt(log T), and the discarded relay tail is o(X). Fix any 0<delta<1, and choose fixed 0<alpha<delta (for example delta/2), W=ceil(T^alpha). By the prior four-form extended-clock sieve and disjoint low budget, all but o(X) of the word weight has first low relay E<=B and first successor wait <T^alpha. These words have Q<T and their first pairs are distinct; their direct causal overlap is Omega(T) per word by the previous overlap lemma (the overlap need not be in the original guard).

For the retained first pairs with min(d'_s,d'_t)<=T^(2-delta), (7) gives an upper weight
    O(X T^(alpha-delta) log^4 T) = o(X),
since S=O(log^2 T), B+1=O(log^2 T) and B+W+1=O(T^alpha). Thus for each fixed delta>0 (it suffices to prove 0<delta<1),
    all but o(X) of the original macroscopic word weight has
        d'_s>T^(2-delta), d'_t>T^(2-delta).            (8)
These refer to the FIRST two high events; they need not be the original endpoints of the causal word. In fact both pre-deficits also exceed, say, half that scale for 0<delta<1 after deleting o(X), since their individual changes and the whole low relay are O(T). Consequently all but o(X) of the word weight can be represented by disjoint direct recovery pairs with actual overlap Omega(T) and both endpoints at nearly quadratic deficit scale. No small total-variation premise is imposed. The conclusion applies to every growing T<=C, including T~sqrt X, under the stated support and low-relay assumptions. At near sqrt X this means escaping every fixed sublinear power cap X^(1-epsilon), not necessarily attaining a fixed positive fraction of X.

If also T>=X^a fixed a>0, b is bounded. For the retained fast population F(B,W)>=rho X-o(X), (4) gives D_s,D_t >> T^(1-alpha)/log^2 T. Since S=O(log^2 T), (6) forces
    R_s >> T^(2-alpha)/log^4 T,
and the target diameter has the same order lower bound (subtract O(T)). In particular for each fixed 0<delta<1, choosing alpha=delta/2 as above gives
    R_s,R_t,V_d = Omega(T^(2-delta)).                 (9)
The diameter assertion can be applied to ANY macroscopic-weight subcollection of the fast pairs, with the same source bound and cutoffs; no choice of a common high baseline removes it. Here V_d is the full block ordinary total variation. This is stronger in its scope than the previous cap-free low-variation bound because the source is upward and the target is nearly maximal downward, not a near-flat edge. It uses the actual fast successor reduction and the global small-support/relay assumptions, which are additional hypotheses. In particular we have not contradicted the canonical O(X) upper envelope or shown a universal high-deficit supply bound. At subpolynomial scales the absolute escape (8) remains but the width estimate (9) requires control of b. The general fast direct-pair population with high and dispersed deficits, large source support, general low/middle crossing and macro upward supply remain unresolved.

## 4. Diagnostics and preservation

[Audit 6e2a198](https://github.com/tara-sooo/A166944-Lean/blob/6e2a198921a95d21643afce389e15ff20625458b/research/min_direct_fast_pair_multiplier_shift_audit.mjs), blob a73aba5db99698e8dd0806456e29138fef5f4478. Exact remote readback. Run node research/min_direct_fast_pair_multiplier_shift_audit.mjs 60000. Executed actual ECMAScript in tool runtime. 29998 canonical odd roots through60000,549085 actual events,0 unresolved cap180. Finite T17/31/61/101, labels [T,6T], B=floor(T/16), W=max(1,floor(T/16)), Q=5B+2W+7<T. 1832 first high pairs with upward source, fast successor and small low relay, 1748 nonempty root/threshold controls.1832 exact clock, odd-shift, forward/reverse divisor, horizon CRT, stronger phase CRT and source positivity checks each.325 reset targets,32 source multipliers h>=T,1708 small-cap controls min(h,k)<=floor sqrt T,92 nonzero relay,1676 opposite-side incidences.1748 source and target support capacity checks each,1832 tuple capacity and disjoint low-budget checks each.5939 independent integer solutions of the odd shift with small absolute c (4403 with h>=p), not claimed realized MIN paths. Example p17,r31,H9810->9826,h1,k0,E=V=0,w1,c3, source/target post-deficit34->6. Counts overlap across roots/thresholds. The finite run tests the exact arithmetic and finite support bounds, not the earlier four-form analytic constant or the asymptotic sparse-support/relay hypotheses. All assertions passed. No Lean kernel verification, external novelty claim or twin-infinitude proof. Main and sibling branches unchanged.
