# Dense barrier capacities, far-event count without density loss, and timing constraints

Continuation of [584d6aa](https://github.com/tara-sooo/A166944-Lean/commit/584d6aab57a74317e6e11fe024a1dff997e4ab24) on the independent direct-arithmetic branch. The previous proof bounded barrier coverage by far jumps only by their total length. Applying the same periodic discrepancy estimate to these jumps yields a stronger count theorem and a gain/count tradeoff. We then couple barrier coverage to the actual waits, adjusted resets, and ordinary deficit at integer ticks. This gives necessary conditions on one actual ray, not merely admissibility at independent plateaus. No contradiction with finite twins, no proof of A166944, no Lean kernel verification.

## 1. Setup and previous inputs

Use adaptive MIN, canonical odd M>=5: initial (t,H)=(M+2,2M-2), ordinary deficit d=2t-H>=0. At each event (pre t,H; winning tick n=t+w; label p; side e=+1 even/-1 odd; I=(1-e)/2), gain g=p-1, post Z=H+g and ordinary post deficit d'=2n-Z=d+2w-g. Eligibility p^2<=H+1, w<=2p<=3g. Adjusted post deficit D=d'-6I is a multiple of 2p, and for p>=5 it is nonnegative. Thus D!=0 implies d'>=2p. The canonical bound d<=6+5(H-H0) holds at post-event plateaus (including the initial state) by summing 2w-g<=5g.

For integer R>=5, define P=product of odd primes<=R, alpha=product (p-1)/(2p) over those primes, and A=alpha P. An even J is an R-barrier iff J modp belongs to {0,2,...,p-3} for each such prime. No p<=R can cross J, where crossing means J in the half-open jump interval [H,H+g). For even endpoints a<=b let B(a,b) count barriers in [a,b). Previous exact periodic estimate:
    |B(a,b)-alpha*(b-a)/2| <= A.
In particular any jump, even a far one, covers at most alpha*(g/2+P) barriers, and at most g/2 barriers by counting even positions. Also alpha>=exp(-C R/log R) and P<=exp(4 log(2) R), by the earlier elementary Chebyshev estimates.

For an event write H=pq+e, q odd>=p, x=(p+q)/2, k=(q-p)/2. Fix eps in (0,1). A near event has k^2<=eps*x and x>=ceil(16/(1-eps)^2); a far event does not. At sufficiently high H the center threshold holds automatically. Square-band packing from 8b30078: for pre-horizons in [X,Y] the near gain is <=(Y-X)/2+O_eps(sqrt Y), and near count O_eps(sqrt Y), since there is at most one near event per integer center x. In particular a far event at sufficiently high H satisfies q-p>2 sqrt(eps*p).

## 2. Exact gain/count capacity and the strengthened global count

In any finite contiguous event block, let G be total gain. Partition the high events p>R into near events (gain N_g, count N_c) and far events (gain F, count m). Let B_f denote barriers covered by the far high events. The jump intervals partition the whole gained horizon interval. Low labels cover zero barriers, so
    2 B_f >= alpha [G-N_g-2P(N_c+1)].
Define the residual L0=G-N_g-2P(N_c+1). It may be negative for small finite blocks; then the corresponding lower bounds are vacuous.

Using both upper estimates for the far intervals gives
    F >= alpha L0,                                  (1)
    F+2P*m >= L0.                                   (2)
If all pre-horizons <=Y, set C_Y=floor sqrt(Y+1) (g<=C_Y-1). Hence
    m >= L0/(C_Y-1+2P).                             (3)
Unlike the old count obtained by dividing (1) by C_Y, (3) contains no alpha loss.

For every infinite canonical ray consider the block from the first post horizon >=X to the first >=Y=lambda X for a fixed lambda>1 and sufficiently large X beyond the initial root. All pre-horizons in [X,Y); initial overshoot <=sqrt(X+1). Therefore G>=(lambda-1)X-O(sqrt X), N_g<=(lambda-1)X/2+O_eps,lambda(sqrt X), N_c=O_eps,lambda(sqrt X). Set R=floor(c log X), with fixed 0<c<1/(8 log2). Then P<=X^(4c log2)=o(sqrt X), and
    L0 >= ((lambda-1)/2-o(1)) X.
Thus simultaneously:
    F >= ((lambda-1)/2-o(1))*alpha X,
    m >= ((lambda-1)/(2 sqrt(lambda))-o(1))*sqrt X,
    F+2P*m >= ((lambda-1)/2-o(1))*X.                  (4)
In particular far high events now have count Omega(sqrt X) (not merely X^(1/2-o(1))) and gain X^(1-o(1)) in the lower-bound sense. All labels exceed floor(c log X) and all are far in the stated sense.

The joint constraint is stronger than separate lower bounds. If m=O(sqrt X) along a sequence of crossed windows, then F>=((lambda-1)/2-o(1))*X on those windows, since P=o(sqrt X). More generally if m=o(X/P), the same conclusion holds. Conversely if F=o(X) on a sequence, then
    m >= ((lambda-1)/4-o(1))*X/P
        >= Omega(X^(1-4c log2)),
which has an exponent strictly above 1/2. These are conditional tradeoffs on actual m and F, not a claim that F is always a positive uniform fraction when R grows. The far subset can have many events of relatively small gain, in which case (2) is compatible with (1).

## 3. Long reset versus large ordinary post-deficit

In the high-far set call an event good when D=0 and 4w>=g, and bad otherwise. This definition is specific to this note; it does not impose the fourth-root threshold or assert a prime cofactor. Write F_g,m_g,B_g and F_b,m_b,B_b for gains, counts, and covered barriers. Then F=F_g+F_b, m=m_g+m_b, B_f=B_g+B_b. Each class separately obeys
    F_class>=2 B_class,
    F_class+2P*m_class>=2 B_class/alpha,
    m_class>=(2 B_class/alpha)/(C_Y-1+2P).
In the above crossed windows, at least one class has 2 B_class>=alpha L0/2. Therefore one class has simultaneously gain Omega(alpha X), count Omega(sqrt X), and gain+2P*count Omega(X). Constants depend only on eps,lambda,c, not the ray. The class may vary by window.

Every bad event forces a large ordinary deficit at an adjacent plateau. If D!=0, its own post deficit d'>=2p>=g/2. If D=0 but 4w<g, the pre-plateau deficit is d=d'+g-2w>g/2, because d'>=0. Charge each bad event to its own post plateau in the former case, and to the immediately preceding post plateau in the latter (or the initial state of the finite block if it is the first event). Each plateau is charged by at most two bad events, since only the event ending there and the next event can charge it. Every charged d>=g/2>=(R-1)/2. If Q denotes the set of distinct charged plateaus,
    #Q >= m_b/2,   sum_{z in Q} d(z) >= F_b/4.       (5)
The initial state contributes at most one counted plateau. On a crossed block starting at an actual event, it is itself a post-event plateau. Thus in every sufficiently large crossed window there is the following alternative:
(A) Omega(sqrt X) far high events are long resets, and their total gain is Omega(alpha X);
(B) Omega(sqrt X) distinct adjacent post-event plateaus have d>=(R-1)/2, with sum of their deficits Omega(alpha X).
In case B, the post-event labels at the charged plateaus need not themselves exceed R. Case A supplies distinct canonical reentries: p>R>=5 resets normalize within 7 ticks, gain<=8, before another p>=7 event by the seven-tick theorem in 123bbd4. At most one reentry is pending at the right endpoint. Hence A also forces Omega(sqrt X) roots in the window (up to one boundary loss).

If all ordinary post-event deficits in the block, including its initial plateau, are <(R-1)/2, no bad event exists. Thus in that regime ALL high-far events are long resets, with the count, gain and tradeoff (4). This is a conditional statement and the small-deficit regime has not been forced.

## 4. Root-sparse windows force far nonreset events, with the full count

Let N be the number of canonical visits in (t_start,t_end]. Split high-far events into resets and nonresets, with F0,m0 and F1,m1 respectively. By the seven-tick normalization m0<=N+1 on an infinite ray with initial H>=24. Count the barriers in the high-far reset class by their periodic capacity, and the remaining ones by length or periodic capacity. This gives
    F1 >= alpha [G-N_g-F0-2P(N_c+m0+1)],             (6)
    F1+2P*m1 >= G-N_g-F0-2P(N_c+m0+1).
If N=o(sqrt X) along any subsequence of crossed windows, m0=o(sqrt X) and F0<=C_Y*m0=o(X). Therefore the bracket is >=((lambda-1)/2-o(1))*X. In those windows, F1>=Omega(alpha X), m1>=Omega(sqrt X), and the joint inequality (4) holds with F1,m1. All these are high-far nonreset events and their OWN post deficits satisfy d'>=2p. In particular the sum of their post deficits is >=2F1. This improves the old root-sparse gain estimate (fixed power loss) and adds the far constraint. It is not an upper bound ruling out root-sparse rays.

## 5. Ordinary deficit at absolute ticks: truncated potential

Let h(t) be the horizon after processing absolute tick t, including quiet ticks. Put d(t)=2t-h(t). Then
    d(t+1)=d(t)+2-g_(t+1),
where g_(t+1)=0 at a quiet tick and p-1 at an event. For even threshold L>=0 set Q(t)=(d(t)-L)_+, and
    u_t=(d(t)+2-L)_+-(d(t)-L)_+,
    v_t=(d(t)+2-L)_+-(d(t+1)-L)_+.
Exactly Q(t+1)-Q(t)=u_t-v_t. Since d and L are even, u_t=2 if d(t)>=L and zero otherwise. Also
    v_t=min(g_(t+1),(d(t)+2-L)_+)>=max(0,g_(t+1)-L)
because d(t+1)>=0. Consequently for an arbitrary interval [a,b) of integer ticks, if F_* is total gain of any designated subset of events with g>=R inside it (events at a+1,...,b), then for L=2 floor(R/8)<=R/4,
    2 #{t in [a,b): d(t)>=L}
         >= (3/4) F_* - Q(a).                        (7)
This follows by telescoping the exact potential identity and using Q(b)>=0; no assumption about waiting times. It also handles a long initial deficit explicitly rather than silently discarding the initial potential.

Remove the boundary term on a larger crossed window as follows. Let t_a,t_b,t_c be first post plateaus reaching X,8X,16X respectively. Choose R=floor(c log X) as before. The result in section2 applied to [8X,16X] at this cutoff (the proof only uses P=o(sqrt X)) gives high-far gain F_*>=Omega(alpha X), and F_*<=9X eventually. Also
    2(t_b-t_a)=H_b-H_a+d(t_b)-d(t_a)
                 >= 2X-O(sqrt X)
by the canonical deficit bound at t_a, d(t_b)>=0, and first-crossing overshoots. Thus t_b-t_a>=3X/4 eventually, in particular >=F_*/16.

If Q(t_b)<F_*/4, (7) forces at least F_*/4 high-deficit ticks in [t_b,t_c). Otherwise d increases by at most two per tick, so d(t_b-j)>=d(t_b)-2j>=L for 1<=j<=floor(Q(t_b)/2). In [t_a,t_b) this gives at least min(t_b-t_a,floor(Q(t_b)/2))>=F_*/32 ticks for all sufficiently large X, since F_* tends to infinity. In either case,
    #{t in [t_a,t_c): d(t)>=2 floor(R/8)}
      >= Omega(alpha X)
      >= Omega(X exp(-C_c log X/loglog X)).           (8)
The elapsed time t_c-t_a is O(X) by w<=3g, so this also gives a lower bound Omega(alpha) on the fraction of ticks at those logarithmically growing deficits. For fixed R, the same argument gives a positive fraction at the corresponding fixed threshold (the result does not imply a divergent mean deficit). The growing-threshold result holds even if many event-end deficits are zero, because quiet ticks may be large-deficit ticks. It does not establish a large wait for each far event, nor the square/cube-root qualified roughness thresholds of earlier papers.

## 6. Diagnostics and persistence

[Audit ad04af5](https://github.com/tara-sooo/A166944-Lean/blob/ad04af53cfd2a1cd2cbf4110c549325082e84bfb/research/min_direct_barrier_timing_audit.mjs), blob 7164e5c00c6c6f50e7523e85c7bd6ee9a4041f5d, exact remote readback. Run node research/min_direct_barrier_timing_audit.mjs 100000 180. Actual ECMAScript execution in tool runtime, not separate Node process. All 49,998 odd roots M=5..100000 up to180 events: 1,020,339 actual events, 48,906 nonempty paths, 49,989 terminated before cap, 9 reached cap (no later stop asserted). For each nonempty full prefix and suffix of paths with >=4 events, cutoffs R=5,7,11,13,17: 457,840 block/cutoff incidences. 7,672,390 per-jump barrier capacity and exact plateau potential checks each; 457,840 far count/gain, good/bad charge, root-sparse and telescoping potential checks each; 209,770 local high-tick extension checks (where preceding elapsed time meets the size condition). 115,081 intervals had positive residual L0. 2,196,679 high-far event-window incidences: 346,432 good, 1,850,247 bad (179,297 short resets, 1,670,950 nonresets). Each bad charge verified, including multiplicity<=2 via the aggregate count/sum inequality. Example M75671, H151340->154620, R5, F3018 all bad, 81 events and 81 charged plateaus, sum deficits99490, 2885 high-deficit ticks at the diagnostic threshold L=0. This last threshold is trivial; the asymptotic high-threshold result is the paper deduction, not empirical extrapolation. Counts overlap across cutoffs/windows. All final assertions passed. No observed macroscopic crossed window claimed. Main and sibling branches unchanged.

Under finite twins every sufficiently large canonical root has an infinite ray, so the far-event count/tradeoff, timing alternative, and high-deficit duration apply to all such rays. They do not yet contradict finite twins. The stronger count and gain/count relation are independent of waiting-time assumptions. Next investigate a direct upper bound on high-deficit excursion duration or on the simultaneous count and gain of far long resets. No inference that the small-deficit branch or root-sparse branch alone is impossible.
