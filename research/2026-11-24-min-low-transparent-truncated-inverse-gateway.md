# Low-transparent stopping, truncated inverse caps, and last-large gateway moments

2026-11-24 JST. Continues 69fae6ceefa190ebe24614245fb79909fa23db90 on the SAME research/min-cycle-forest-2026-11-24 branch. Paper deductions using the established LOW barrier, per-prime upper-bound sieve and terminal capped-mass moment; exact finite audit. No Lean compilation. No proof of a complete stopping deficit or twin-prime infinitude.

## 1. Make the small-label region transparent to stopping

Canonical MIN, original odd M in [X,2X), N=X/2, B=ceil(sqrt(7X)), original source-specific cutoffs. Let 11<=Y<=B tend to infinity and write L_Y=2 product_(3<=p<Y prime) p. Treat every selected label p<Y as LOW for this new accounting rule: never stop at such an event. This does NOT change the underlying choice of prime, the event time, the state update, or the individual cutoff. Stop only at proposed high keys p>=Y. Every consecutive low-only block has gain <L_Y, elapsed <3L_Y, r-cost <3L_Y/2, since r<=p<=1.5(p-1). Each path has at most one more low-only block than executed high events, including any low suffix up to a natural terminal. These facts hold even when the proposed endpoint is a stop.

With uniform cap T=B on p>=Y only, executed high cost is bounded by B times the arithmetic selected-key sum S_key=O(XB/log^3 B). The total executed high incidence count is <=O(B X sum_(Y<=p<=B prime)1/p)=O(XB log log(3B)), since each projected key has fewer than B tags, and for fixed p there are O(X/p) eligible even horizons. Therefore
    R_pre = O(X^2/log^3 B + L_Y[X+XB log log(3B)]).
If L_Y<=sqrt B, the second term is o(X^2/log^3 B). By the elementary Chebyshev bound sum_(p<Y) log p=O(Y), one can take Y=c log B for a sufficiently small fixed c>0. Thus all stops are at p>=Y tending to infinity, while R_pre=O(X^2/log^3 B) is preserved. The old non-twin unstopped lower bound implies S=N-o(X) in a hypothetical no-twin window. The low-stop obstruction has been removed by modifying the stopping rule, not by proving that the old low-stop population was small. The new stopped population is different.

Any root whose first proposed high event is its stop has had only low events since its initial horizon 2M-2, so at a fixed stop horizon there are at most floor(L_Y/4)+1 such roots. Since the number J of stopped keys is <=N/B, the total is O(X L_Y/B)=o(X). In the hypothetical no-twin case, almost all roots then have executed at least one high p>=Y before their stop. This is a genuine all-depth structural consequence, not a bound on total stops.

## 2. Truncate the inverse-prime cap rather than retaining small-label stops

The previous inverse cap B^2/p with small-label cap B gave virtual variance o(X) on p>=Y but could put all stops below Y. Here choose a second cutoff Z, Y<=Z<=B, tending to infinity, and make p<Y completely transparent. For p>=Y put
    tau_p=ceil(B^2/max(p,Z)).
All minimum thresholds are at least B. The executed mass is <=B^2/max(p,Z) and each stopped mass is >=tau_p. The high cost is bounded using the earlier per-p estimate S_p=O(X/log^2 p):
    R_hi <= O(X B^2 [ (1/Z) sum_(Y<=p<Z) 1/log^2 p
                             + sum_(p>=Z)1/(p log^2 p)])
          = O(X B^2/log^2 Z).
Use pi(t)=O(t/log t) and partial summation. The executed high incidence count is at most
    O(X B^2 [ (1/Z) sum_(Y<=p<Z)1/p + sum_(p>=Z)1/p^2])
       = O(X B^2 log log(3Z)/Z).
The LOW-only bound then gives
    R_pre = O(X B^2/log^2 Z + X L_Y
                           + X B^2 L_Y log log(3Z)/Z).
Assume L_Y log log(3Z) log^2 Z=O(Z) and L_Y<=B (the latter follows eventually from the former with Z<=B). The whole budget is O(X^2/log^2 Z)=o(X^2), and again no twins implies S=N-o(X). This differs from applying an inverse cap to all labels: we explicitly account for the unbounded masses of low keys using the total gain per low block.

For example choose Y=c log log B with a sufficiently small fixed c>0 so that L_Y<=sqrt(log B), Z=(log B)^2. Round thresholds as needed. These choices obey the inequalities for sufficiently large B. All stops then have unbounded labels p>=Y, and the budget is O(X^2/(log log B)^2). Alternatively for any fixed 0<theta<1 choose Z=B^theta and Y=c_theta log B with L_Y<=B^(theta/2). The budget is O(X^2/log^2 B).

For the set E of stops p>=Z, the reciprocal sum I_E<=S_E/B^2<=N/B^2, since p m_v>=B^2, and J_E<=N/B. The previous terminal moment theorem with height H_E<=6N+4R_pre+4BN gives
    G_virt,D(E) = O(X D/B + X sqrt(D)/log Z).
For any integer D tending to infinity with D=o(log^2 Z), this is o(X). Also the mass of tags belonging to terminal clock classes of mass <=2D is o(X). The total within-clock terminal variance is >=S_E/2-o(X); restricting the physical forest to these tags and using the harmonic near deletion at d=floor(D/(log(2D))^(1/2+epsilon)) gives P_phys,far(E;D,d)>=S_E/2-o(X) for any fixed epsilon>0. This does not require that these stops have large actual minority mass or few clocks. On no-twin windows the necessary alternative is
    S_(Y<=p<Z) + 2 P_phys,far(E;D,d) >= N-o(X).
The small-label term is now an intermediate growing band: there are literally no stops below Y. It has NOT been proved that the intermediate stopped mass or physical far flux is small. With Z=(log B)^2 and D=floor(log Z), virtual dispersion at every stop p>=Z is o(X), but the physical scale is only O(log log B). This does not extend the earlier D=B theorem to that whole band.

## 3. Keep the original uniform stop rule: last-large gateways

For this separate theorem retain the OLD fixed LOW7 projected stopping rule T=B at all p>7, and its R_pre=O(X^2/log^3 B). Choose a growing cutoff Y>11 for classifying paths only, not changing the stopping rule. Let v=(p,C) be a stop with p<Y. For each of its stopped tags find the last EXECUTED event with label q>=Y, if any. Call its projected key a=(q,A), clock u, post-horizon H_a=A+q-1, and post-height h_a=2u-H_a. Since all subsequent executed events before the proposed stop have labels <Y, the barrier gives
    g=C-H_a even, 0<=g<L_Y,
    0<n-u<=3L_Y+2r(C).
The current proposal is unexecuted. Its clock wait is included in the latter inequality, not in g. The prior q divides C-g or C-g+2, and A=C-g-q+1. Tags with no such q have C-(2M-2)<L_Y and at most floor(L_Y/4)+1 can occur at any fixed stopped key. There are J<=N/B stops. Hence if L_Y=o(B), the entire no-large-ancestor stopped population at p<Y is o(X).

Now isolate tags whose last-large q>=Q=B/log^alpha B for a fixed alpha>0. Let S_* be their total number among the p<Y stopped tags. Group them by (terminal projected key v, gateway projected key a), and then subdivide each group by the actual gateway clock u. This partition is on original tag identities; no mass is duplicated. For a fixed v and each g<L_Y, the two nonzero integers C-g,C-g+2 are positive O(X); each has O(1) distinct prime factors >=Q since log Q asymp log B and log X=O(log B). Thus the number of nonempty (v,a) groups J_* is O(J L_Y), and their reciprocal-label sum
    I_* <= O(J L_Y/Q) = O(X L_Y log^alpha B/B^2).
No assumption that q is the selected prime at the stop is made; q is executed strictly earlier. Different (v,a) may in principle reuse the same a with different tags, but the count is by group, and the weighted height H_* = sum_tags h_a <=6N+4R_pre=O(X B^2/log^3 B) since each source is charged its gateway once and the event is executed.

The terminal capped-mass argument applies verbatim to these groups: for fixed a its possible clocks have period 2q and heights spaced by 4q. Put U_* = sum_(v,a,u) min(m_(v,a,u),2D), with integer D>=1. It follows that
    U_* <= 2D J_* + sqrt(D H_* I_*)
         = O(X D L_Y/B
             + X sqrt(D L_Y log^alpha B/log^3 B)).
If L_Y<=log^ell B with fixed ell>0, D=floor(log^beta B), alpha+beta+ell<3, then U_*=o(X). In particular all but o(X) of these S_* tags are in gateway physical classes with mass >2D, and the total variance WITHIN these physical gateway classes is at least
    S_*/2 - U_*/2 = S_*/2-o(X).
This follows from F_D(A)>=m/2-min(m/2,D). It is a stronger statement than merely bounding clock-class numbers, and does not presume that an original low stop is nearly synchronous. It applies even if its clock minority mass is large.

For example choose alpha=beta=ell=1/2, Y=c log log B with sufficiently small fixed c so L_Y<=sqrt(log B), Q=B/sqrt(log B), D=floor(sqrt(log B)). Then U_*=O(X/log^(3/4) B + X log B/B). Restrict the original physical forest to these S_* tags and truncate each at its own gateway. If two of these retained tags have reached the same actual clock-refined high state, their later proposed high sequence and actual stop coincide (both are stopped under their individual cutoffs). If that state is a last-large gateway of one, it is so for both. Consequently these truncated paths form a non-splitting forest with terminal physical classes exactly those in the partition above, including singleton injections. The earlier harmonic near bound at d=floor(D/log^(1/2+epsilon)(2D)) applies. The far physical merge proxy before or at the gateways is therefore >=S_*/2-o(X). No assertion that S_* is a substantial fraction of S is made. In particular the theorem does NOT bound the entire low-stop mass under the old rule: gateways with Y<=q<Q remain. The result isolates the top-gateway subpopulation independently of the last-stop clocks.

## 4. Exact finite audit and limitations

Saved research/min_low_transparent_gateway_audit.mjs and results JSON, exact remote readback at 7921d7863fb12a3c038973a9646e3b35f08e3164. Ran X=256,1024,4096,16384,65536,262144 with T=max(2,floor(B/4)), Y=13, Z=max(Y,ceil(sqrt B)), A=T B in three modes: old uniform T at p>=11; transparent uniform T at p>=13; transparent truncated inverse ceil(A/max(p,Z)) at p>=13. All retain original clocks and source cutoffs. The finite Y=13 gives L_Y=2310, not the growing asymptotic choices. Verify source conservation, original stop mass, every low-block gain and cost, total low budget <=1.5 L_Y(N+executed high incidences), first-high stop origin bound, gateway gain and time bounds, clock periods and moment inequalities for a=8, and high stop reciprocal sums under truncated inverse. Literal parity-GCD checks retained for X<=1024. The last-large gateway diagnostic uses q>=ceil(B/2), not the asymptotic Q, and verifies the capped-mass inequalities, not a numerical spatial variance ledger.

At X262144, B1355, N131072, T338, Y13,Z37:
- Old uniform: S11112, R98554147, low-stop tags p<13=1064, of which18 had no previous q>=13 and1046 have last-large gateway; 11 distinct (stop,gateway) groups,17 clock classes, max low suffix gain36. No top-gateway tag q>=ceil(B/2) in this window. At X16384, however, there were35 such top-gateway tags in one reset clock class, U_*=8, all35 in a class larger than8.
- Transparent uniform: S10763, 29 stops, all at p>=13; R99033865, low portion11633423 and high portion87400442; max low-block gain80 and cost87. First-high stop tags135. All120309 unstopped terminals are twin terminals.
- Transparent truncated inverse: S629 at one stop p>=37, R107069391, low cost12572668 and high cost94496723; three first-high stop tags. Terminal clock moment H3774, U8 (a8), so all629 are in one clock class (H=629*6). All130443 unstopped terminals are twin terminals. At X4096 and65536 the truncated inverse diagnostic has zero stops. At X256 it has five non-twin natural terminals, retained from the earlier inverse run; no claim that all finite windows satisfy no non-twin terminals.
The finite decrease of S under the new rule is not a proof of asymptotic improvement. The top-gateway estimate is empty at the largest tested old-uniform window and nonempty in smaller ones, so it does not explain that window's low-stop population.

## 5. Residual

The new stopping rule removes small-label stops by construction while maintaining an arithmetic prefix deficit, and the truncated inverse version controls terminal virtual dispersion above Z. Separately the old-rule gateway lemma removes small physical clock classes in the top last-large ancestor band. Remaining: the stopped population in Y<=p<Z for the new rule, and physical far variance above Z; or in the old rule, the low-stop tags with smaller last-large q and the physical far coalescences. No global anti-concentration or twin-prime proof. No new branch or main edit.
