# A1 recovery: logarithmic deficit budget and consecutive growth obstruction

Continuation of [3f1448b](https://github.com/tara-sooo/A166944-Lean/commit/3f1448b7868095d73e15492d75b323faf760b98a) on the independent direct-arithmetic branch. The previous A0/A1/B alternative left the problem of recovering from A1 nonresets. This note couples successive A1 events, deficit-reducing events, low-label runs and canonical returns. It also constructs arbitrarily long finite consecutive A1 strings with increasing labels, so recovery cannot simply be presumed. No proof of twin infinitude or Lean kernel verification.

## 1. Deficit loss at one event

Use the existing adaptive MIN model, pre-plateau (t,H), winning tick n=t+w, prime p, side e=+1 even/-1 odd, I=(1-e)/2, post Z=H+p-1, ordinary deficits d=2t-H, d'=2n-Z, adjusted D=d'-6I. Then d'=d+2w-(p-1), w>=1, d,d'>=0, D multiple of 2p. For p>=5, D>=0. A1 means p>=47, p>=5d+15 and D=2p (the deterministic low-deficit nonreset class of the previous note, with the far condition optional).

A nonreset with p>=5 has d'>=2p, so
    d+3 <= d'+p <= (3/2)d' <= (3/2)(d'+3).
Thus log(d+3) decreases by at most log(3/2) at one nonreset. p=3 never decreases ordinary deficit because its gain2 and w>=1; this also handles its exceptional negative adjusted deficit. Any deficit-decreasing nonreset with p>=5 necessarily has d>d'>=2p, and is outside the low-pre-deficit A criterion. For a reset, d'=6I<=6, hence d+3<=p+6. Its log loss is at most log((p+6)/3).

The ordinary post-event deficit cannot equal 2,4,8: for an even event 2p divides d', and for an odd event 2p divides d'-6, none possible at these three values for any odd prime. The initial canonical deficit6 has the same exclusion. In particular p=5 cannot decrease deficit in a reset: even reset would require a positive pre-deficit <=2, odd reset would require a pre-deficit >6 and <=8. Hence every actual deficit-decreasing reset on a canonical trajectory has p>=7. By the seven-tick normalization theorem (123bbd4) each such reset is associated to a canonical root within seven ticks, before another p>=7 event, or termination. On an infinite ray the associated root always occurs.

At A1, d+3<=p/5 and d'+3>=2p+3, so log(d'+3)-log(d+3)>log10.

## 2. A1 pair recovery

Take two A1 events in chronological order with labels p,r, not necessarily successive in the entire event sequence. Between the first post-state and the second pre-state let the deficit-decreasing events have labels s_j (including resets, if any). The total positive reduction is at least the net reduction, and each reduction is at most s_j-3. Thus
    sum_j(s_j-3) >= d'_p-d_r >= 2p+6I_p-(r-15)/5.       (1)
In particular for r<=p the required reduction capacity is >=9p/5+3, and if all decreasing labels <=S (S>3), their count is at least (9p/5+3)/(S-3). These are bounds on the intervening events, not on the endpoint A1 events.

If there is no deficit-decreasing reset between them, let h count the decreasing nonresets. The log-loss estimate gives
    h log(3/2) >= log((d'_p+3)/(d_r+3)) > log(10p/r).
Consequently h>=max(0,ceil(log(10p/r)/log(3/2))) is a valid (slightly nonsharp at an exact integer boundary) lower bound. For r<=p/2,p,2p,5p it gives respectively 8,6,4,2 decreasing events. When the net deficit really falls, the last decreasing nonreset has post deficit <=d_r, so its label is <=d_r/2<=(r-15)/10. This is an additional small-label requirement on a recovery, not just a total gain bound.

If r<=61 (and hence r is one of the allowed A1 primes), d_r<10 while d'_p>=94. Such a fall must contain a deficit-decreasing reset: any decreasing nonreset ends at deficit>=10 and p=3 cannot decrease it. Such a reset has p>=7 by section1 and yields an actual canonical reentry before the next A1 event, since A1 labels >=47. Thus an A1-to-A1 pair with second label <=61 always has an intervening canonical reentry. No claim for larger r.

When there are no decreasing events at all, d_r>=2p+6I_p forces r>=10p+15+30I_p. In particular an uninterrupted string of adjacent A1 events (with no other nonunit event between them) has labels growing by a factor strictly greater than10 per event. If all pre-horizons <=Y and first label p0, such a string of length k satisfies
    10^(k-1) p0 <= sqrt(Y+1),
hence k<=1+floor(log(sqrt(Y+1)/p0)/log10). This is an absolute-scale restriction, not a uniform constant length bound.

## 3. Truncated logarithmic potential and bounded-label runs

Consider any contiguous event block of a canonical ray, with all pre-horizons <=Y and initial horizon>=8. Fix R>=47 and integer 5<=S<R. Select any designated subset of A1 events with p>R (e.g. the high-far A1 subset in the previous barrier theorem). Let m be their count. Among all other events with p>S let z count resets and n count nonresets; let J<=n count those nonresets with d'<d. Set
    T=R/5, Phi(d)=log(max(T,d+3)),
    K_S=2 product of odd primes<=S,
    epsilon=log(1+K_S/T).
Every marked A1 increases Phi by at least log10, since d+3<=p/5 and T<p/5. Each other high nonreset decreases Phi by at most log(3/2), and only if it decreases ordinary deficit. Each high reset with label q loses at most log_+((q+6)/T), with log_+ x=max(0,log x).

Each contiguous low-label run p<=S has total horizon gain <=K_S by the primorial cut barrier. Summing d'=d+2w-g over that run shows the ordinary deficit cannot fall by more than K_S, regardless of the length of its waiting times. Consequently its entire Phi-loss is <=epsilon: if d_start>d_end, then max(T,d_start+3)<=max(T,d_end+3)+K_S. There are at most m+n+z+1 such low runs. Summing yields the finite inequality
    m log10 <= Phi(d_end)-Phi(d_start)
             + J log(3/2) + sum_{high resets q} log_+((q+6)/T)
             + epsilon(m+n+z+1).                      (2)
No independence or assumptions about consecutive clock phases. In particular low labels may appear arbitrarily often within their runs, but their net logarithmic reduction per run is limited.

Write C=floor sqrt(Y+1), and N for actual canonical reentries in (t_start,t_end]. All z high resets have q>=7 and hence z<=N+1 on an infinite ray by normalization, allowing one pending right-endpoint visit. This also holds for actual finite canonical prefixes: if normalization terminates before an actual root, no next high reset occurs. Thus
    (log10-epsilon)m <= (log(3/2)+epsilon)n
          +(N+1)[log_+((C+6)/T)+epsilon]
          +epsilon+Phi(d_end)-Phi(d_start).             (3)
One may use actual reset labels rather than the uniform C bound, as in (2). This is a coupling between classes rather than independent lower bounds on each.

## 4. Consequences on a crossed macroscopic window

Use the previous high-far A1 class in a crossed [X,lambda X] on an infinite canonical ray, lambda>1 fixed. Let R=floor(c log X), 0<c<1/(8 log2), and choose S=floor(a log R), 0<a<1/(4 log2). For sufficiently large X, S>=47 and S<R. The earlier Chebyshev estimate theta(S)<=4 log2 S gives
    K_S<=2 R^(4a log2)=o(R), epsilon=o(1).
All endpoint deficits are O_lambda(X) by the canonical envelope d<=6+5(H-H0), so Delta Phi<=O(log X). Also C=O_lambda(sqrt X).

Suppose A1 is the barrier-heavy class of the previous theorem, so m=Omega(sqrt X). Equations (2)-(3) imply the following consequences in those windows:
* Either the actual root count N=Omega(m/log X) or the count n of other nonreset events with p>S is Omega(m). More precisely, along any sequence with N=o(m/log X),
    n >= (log10/log(3/2)-o(1))m.
The constant is approximately5.6789. The other events need not be high-far or satisfy A1; S is of order loglog X, not log X.
* In the same root-sparse sequence, if n=O(m), (2) gives the stronger conclusion
    J >= (log10/log(3/2)-o(1))m.
Every counted decreasing event has p>S, d>d'>=2p, and hence fails the low-deficit A test. Without the n=O(m) assumption (2) remains valid; if n is much larger than m, the count alternative already gives more nonreset activity. One cannot discard the epsilon*n term without such control.
* More generally (2) shows the deficit increase of the designated A1 events must be paid by the log losses of other events, bounded low-label-run losses, or a final deficit increase. The latter is O(log X) in the logarithmic scale, even when ordinary deficit is of order X.

This improves the local pair argument by allowing unbounded variation of A1 labels, low-label runs, and arbitrary other events within a single macroscopic window. It does not provide an upper bound on n or N strong enough to contradict finite twins; the other nonreset events can be numerous. The preceding barrier trichotomy still allows A0 or B instead of A1. No application of the formal fresh-residue law on one integer ray is made.

## 5. Arbitrarily long consecutive A1 strings are possible

The count bound for adjacent A1 events is not a constant bound. For every fixed positive integer k, construct k successive events all of class A1, all even-side, from a canonical root. Choose increasing primes p_0,...,p_(k-1), p_0>=47, all >max(2k+3,7). Choose p_0=3 mod4 and p_i=1 mod4 for i>=1. Each is 1 mod every odd prime <=max(2k,3); each later prime is 1 mod every earlier selected p_j. Require p_i>10p_(i-1)+15 for i>=1 (also >3p_(i-1)+6). All choices are possible by Dirichlet's theorem in fixed reduced residue classes.

Write h_i=sum_{j<i}(p_j-1). Require H0=0 mod4; for stage i, H_i=H0+h_i=1 modp_i; and for all other odd primes l<=3p_i+6 require H_i != +-1 modl. These conditions are simultaneous:
* At small odd primes <=max(2k,3) all shifts vanish, choose H0=0 modl.
* At a selected prime p_j its forced stage residue1 becomes0 at the next stage, and stays0 since later shifts vanish modulo p_j. Earlier stages do not constrain p_j because p_j>3p_i+6 for i<j.
* Every remaining prime l>2k has at most 2k forbidden residues, leaving at least one.
CRT gives a nonempty finite union of classes, choose H0 large enough for all p_i^2<=H_i+1 and H0>=8. The initial t0=H0/2+3 is canonical. Initial d=6, later d_i=2p_(i-1). The p_i size condition ensures the low-deficit A threshold. Since H0=0mod4, p0=3mod4 gives k_p=3; thereafter H_i=2mod4 and p_i=1mod4 again gives k_p=3. At each stage every competing factor with score <=3p_i is excluded by the imposed residues, or is the selected p_i (only on even side). Thus exactly the required p_i fires, with wait (3p_i-d_i-1)/2 and post ordinary deficit 2p_i. Induction proves the full actual consecutive A1 string. This is a positive-density set of odd canonical roots for each fixed chosen string, with no reentry or decreasing reset between the specified events.

The finite strings grow rapidly in selected labels and require huge initial horizons. They do not violate section2 or the macroscopic inequality (2), and do not show an infinite string from one fixed integer. A fixed-bound statement excluding all reset-free A1 pairs would be false.

## 6. Diagnostics

[Audit 631cbc8](https://github.com/tara-sooo/A166944-Lean/blob/631cbc8937787de6b2f3020e7d16cfef59699b85/research/min_direct_a1_recovery_audit.mjs), blob f0230792577b7bfbe6a039e68b743938d54135d2, exact remote readback. Run node research/min_direct_a1_recovery_audit.mjs 100000 180. Actual ECMAScript executed in tool runtime, not a separate Node process.

All odd M5..100000, up to180 events: 49,998 roots,1,020,339 actual events,49,989 stopped before cap,9 cap-unresolved. 9,591 A1 events;184,526 decreasing events,119,755 nonreset and64,771 reset, all satisfy the one-event bounds. 181 successive A1 pairs, all with at least one decreasing reset in this finite sample; 28 have second label<=61. The sample provides no reset-free recovery pair and cannot establish a universal reset theorem. 1,465,088 block/cutoff inequalities (2),(3) and root-count checks (R47/71/101/151,S5/7/11/13),6,574,824 low-run checks, all passed. The finite cutoff values need not have epsilon small; asymptotic claims are paper deductions.

Separate exact CRT controls from actual canonical roots: consecutive labels67,1021 and67,1021,10273. The two- and three-event representatives are 1305 and13266 decimal digits. Waits97,1464,14388; deficits6->134->2042->20546 (three-event string). 17,510 literal BigInt GCD ticks and4,287 competitor-residue checks; all passed. First greedy extension failed because previously selected increments left incompatible small-prime residue exclusions; selecting 1021 as the second label instead yielded the final valid three-event sequence. The constructive arbitrary-k proof above uses stronger congruence restrictions than this numerical witness. No Lean executable/kernel verification, no observed infinite ray. Main and siblings unchanged.

Next: use the last-decrease small-label constraint and low-run budget to analyze the B events required for A1 recovery, or find a global invariant bounding their frequency. The current inequalities permit abundant B events or canonical resets; finite twins alone does not exclude them.
