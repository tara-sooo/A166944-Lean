# Deficit-band record-depth capacity, the quadratic-log dichotomy for M85, and a projected record-weighted transfer

2026-11-28 JST, Issue #10. Base 1d7517b4aac7f872ba395746680e905a26657900. User requested continued multi-stage research toward M85 and unconditional twin infinitude. This checkpoint derives an unconditional UPPER bound on the number of first-height sinks admitting a short sequence of strict postevent height records, optimizes the terminal roughness split, applies the result to M85 and to a near-square-root twin sufficient condition, and develops an exact Pareto transport and a projected residual theorem for a record-discounted max flow. The latter transfers a new weighted sufficient condition to a prime-cutoff trial graph that excludes every necessarily resetting top label. No new density lower at height R^.4, no M85, no unconditional twin proof, no new Lean compilation or independent specialist review.

Write L=log R, all logarithms natural. M85 remains: H=floor(R^.4), at least c R/L² distinct actual canonical first-H sites, each with an actual ancestor A in [R,2R], 6|A, gain G=A-x<=4H; equivalently age H-3+G/2<=3H-3. All statements about this lower preserve the chosen quantifier (all sufficiently large slabs, or an explicitly unbounded sequence).

## 1. Record deficits: retain the entire descent, not just its last event

Let R^theta0<=H<=C sqrt R for fixed theta0>0,C>0, integer H, and restrict actual canonical paths to gain<=4H at first-H passage. All visited x lie in [R-4H,2R], so x±1 are positive of scale R. Coordinates h=x/2+n, birth h0=3, upward tick increments <=1. Number the completed moving events before first H by j. Their prime, full wait and postheight are p_j,w_j,h_j, and define d_j=H-h_j, d_0=H-3. The calendar implies w_j<=2 qmin(x_source) and w_j<=2p_j. The pre-tick height before a moving event is <=H-1. Consequently
    p_j <= 2 d_j+1,
    d_(j-1)-d_j = w_j-(p_j-1)/2 <= (3p_j+1)/2 <= 2p_j,
    d_(j-1) <= 4d_j+2 <= 6d_j.                              (1)
The first two stronger inequalities, and the weaker last inequality, also appeared in the earlier active-first-record note in a fixed-event-depth application.

Here we use the entire record-minimum sequence. Define mu_0=d_0, mu_j=min(mu_(j-1),d_j). A RECORD event means mu_j<mu_(j-1): its POSTevent height exceeds all preceding postevent heights and the birth height. It need NOT exceed all earlier prefire heights or all earlier physical heights. Write k(A,H) for the number of these strict postevent records before the first H. It is at most the total number of moving events, and may be zero.

A record event has positive net height change from the preceding arrival (or birth): w_j>(p_j-1)/2. Therefore its actual source satisfies
    qmin(x_source) >= w_j/2 > (p_j-1)/4 >= p_j/5    (p_j>=5). (2)
In particular the sources of polynomial-sized record labels are rough at a polynomial scale. This slow-source necessary condition is valid for each actual realization of the key; it is not asserted for all possible histories through that key.

For a sink x reached with gain<=4H, the last incomplete idle has length I=H-h_last<2 qmin(x), because any next actual event would occur within 2 qmin(x) ticks. If qmin(x)<=Q and B=2 floor(Q), with Q an integer or replace it by floor(Q), then mu_last<=d_last=I<B. For the argument below use integer Q>=1, B=2Q, and ell=log(d_0/B). Assume ell>=8 and Q>=R^eta for a fixed 0<eta<theta0, or any specified fixed polynomial lower for Q. In particular d_0>B. The clipped logarithmic potential log(max(B,mu_j)) decreases by exactly ell from birth to the first mu_j<=B, at record events only. Its individual drops are disjoint intervals on the log axis.

Put D_i=2^i B, i=0,...,J-1, including the last possibly partial band, where J=floor(ell/log 2)+1. Assign each record event with landing deficit d_j>=B to its unique dyadic band [D_i,2D_i). The one record which first lands below B (if any) contributes at most log 6 to the clipped logarithmic descent by (1). It is not assigned to a band. At a record assigned to band i the log drop delta_j satisfies
    delta_j = log(mu_(j-1)/d_j)
            <= log(d_(j-1)/d_j) <= log 6,
    delta_j <= 2 p_j/D_i.                                  (3)
For a parameter m>=1, call a band RECORD BAD event one with p_j>=D_i/m; otherwise it is a RECORD GOOD event. This classification depends on landing deficit, not on the earlier fixed top threshold. A good event contributes <=2/m to the log drop. The total log drop from ALL record events assigned to any one band is <=log 12: their disjoint intervals are contained in [log D_i, log(2D_i)+log 6]. This is why repeated events in a band do not multiply the logarithmic capacity. The word "bad" here is only a counting designation, not a claim that the move is invalid.

## 2. A uniform bound on bad record keys in one landing-deficit band

Fix m>=1 at most L^A0 for any fixed A0>0. Assume all D_i>=B>=R^eta, so Y_i=D_i/m is polynomially large uniformly (e.g. >=R^(eta/2) for large R). Every bad record key has p in [Y_i,4D_i+1] by (1), and landing height in the interval H-2D_i<h<=H-D_i (intersect [0,H)). At a moving arrival of sign s=+1 at even absolute clock, -1 at odd clock, the exact pins are
    y = 1-s mod p,    h = b_s mod p,
    b_+=0, b_-=3,    n=h-y/2.
Thus for each p,s there are O(D_i/p+1)=O(D_i/p) possible landing heights, uniformly over this label range. The full source is x_source=y+p-1. By (2) x_source+s=p v and x_source-s=p v-2s have both neighbors p/5-rough; v>1 because x_source is of scale R and p<=2H+3=O(sqrt R). In particular v and p v-2s are p/5-rough.

For fixed p,s the parameter v has interval length O(R/p), at least a fixed positive power of R for the purpose of a uniform upper over a containing interval of that length. An elementary two-form upper sieve gives O(R/(p L²)) possible v. Indeed choose a fixed small polynomial sifting range below Y_i/5 and below p, with ample CRT room in the v interval; for every odd sieving prime ell the roots of v and p v-2s are distinct. The standard Selberg upper used previously follows from CRT, support D_sieve a sufficiently small fixed power of R, quadratic form diagonalization and the lower Euler-product bound for its denominator. Only the usual prime reciprocal and prime reciprocal-square upper estimates are used. Constants can be chosen uniformly for polynomial lower Y_i>=R^(eta/2), p<=C' sqrt R; no assertion of distribution of primes at moduli beyond the elementary progression upper is required.

For each resulting v and landing height, the absolute clock is fixed. Summing p and s,
    # distinct bad record arrival keys in band i
        << R D_i/L² * sum_(p>=Y_i) 1/p²
        << R m/L³.                                         (4)
This counts a superset of actual keys, independent of all earlier histories. Every key has at most one future actual first-H sink, because continuation is deterministic from the physical landing state (and all witnesses under consideration have not hit H earlier). Hence (4) also bounds the number of DISTINCT first-H sinks admitting any successful witness with a bad record in this band. Different witnesses of the same sink may visit different bands; no bound on root multiplicity has been inferred.

## 3. Unconditional short-record upper and density-scale record gain

Let N_act(H,Q,k) count distinct first-H sinks with gain<=4H for SOME actual canonical witness with at most k strict postevent records, and qmin(x)<=Q. Uniformly in the ranges above and k<=L^A0, choose m=max(1,ceil(8k/ell)). The total good-record log drop of such a witness is <=2k/m<=ell/4. The bottom crossing contributes at most log6<=ell/4. Thus at least ell/2 of the log descent must come from bad records. By the per-band log capacity log12, at least ell/(2 log12) DISTINCT bands contain bad record events.

Choose one such witness per sink; there are at most J=O(ell) bands. Charge each bad sink-band incidence to a physical key in that band. By (4), each band can be charged by O(Rm/L³) different sinks even if the chosen witnesses vary. Dividing the aggregate upper by the required number of bands gives
    N_act(H,Q,k) << R/L³ * (1+k/ell).                      (5)
This is a new distributional upper for minimum actual postevent record depth. Unlike the old deterministic depth inequality (6 qmin-1)4^(event_count-1)>=H-2, it counts all distinct sinks admitting unusually SHORT records, uses only positive-net-height record events, and holds uniformly without tracking their ancestry or assuming independent residue queries.

There is a complementary quantitative form usable when a density-scale family of active sinks is supplied. If N>=c_* R/L² distinct gain-budgeted sinks have qmin<=Q, choose m=floor(kappa L) with a sufficiently small fixed kappa>0 depending on c_*, the fixed exponents and an epsilon>0. Count sinks with ANY witness with at least epsilon ell bad bands. Equation (4) summed over bands and divided by epsilon ell shows their number is O(R m/(epsilon L³)). By choosing kappa small, delete at most c_* R/(4L²). Every remaining witness has bad-record log drop <=epsilon ell log12. Choose epsilon small enough and ell->infinity; then at least ell/2 of the log descent is supplied by good records. This yields at least m ell/4=Omega(L ell) good records in every witness. Moreover at least c_1 ell bands each have good-record log drop >=c_2>0, with absolute c_1,c_2: there are J=O(ell) bands and each contributes at most log12, so the bands below a sufficiently small fixed c_2 cannot account for more than ell/4. In each such band (3) forces
    # good records >= c_2 m/2,
    sum_(good record p in band) (p-1) >= c_2 D_i/3.         (6)
The second bound uses p-1>=2p/3 and delta_j<=2p/D_i. These are positive-net-height record events with individual label <D_i/m, not arbitrary completed events. The band property is an actual chronological path condition. This stronger result is CONDITIONAL on the density of active sinks; it is not a new density lower. For Q=H/L^6 rounded down, ell~6 log L and the depth is Omega(L log L). For fixed Q=R^beta, beta<theta=log_R H fixed, ell~(theta-beta)L and the depth is Omega(L²), with positive record progress spread over Omega(L) deficit bands. Different selected sinks cannot share physical states before first H, so (6) also gives corresponding lower counts of distinct actual record keys for a supplied density family.

## 4. Optimize the terminal cutoff: a quadratic-log depth barrier for M85

The main improvement is to choose the roughness cutoff as a function of the record budget, rather than fixing Q=H/L^6.

For any polynomial Q>=R^eta and U>=Q with U=O(sqrt R), count even centers x in [R-4H,2R] with Q<qmin(x)<=U. Pick the least prime p of one neighbor, in (Q,U], and write that neighbor p v, the other p v±2. Both v and p v±2 are Q-rough, v>1. The same uniform two-form sieve gives O(R/(p L²)) centers for fixed p and sign. The elementary dyadic reciprocal prime bound over (Q,U] gives
    # {x:Q<qmin(x)<=U}
          << R [1+log(U/Q)]/L³.                           (7)
No assumption of prime or semiprime factorization of both neighbors, nor a twin-finiteness hypothesis, is needed for this intermediate-roughness upper.

Let 0<=k<=c0 L², with fixed c0>0 chosen small enough in terms of theta0 (for example c0<theta0²/100). Put lambda_k=max(9,sqrt(k+1)), Q=floor((H-3) exp(-lambda_k)/2). Then Q>=R^(theta0/2) for sufficiently large R, uniformly, B=2Q, ell=lambda_k+o(1), and ell>=8. Apply (5) with this Q, and (7) with U=4H (or 4H-1, which makes no difference). It follows that the number of distinct first-H sinks with gain<=4H and qmin(x)<4H admitting ANY witness of at most k postevent records satisfies
    N_nonstationary(H,k) << R/L³ * (1+sqrt(k)),
                       0<=k<=c0 L².                      (8)
Indeed k/ell+ell=O(1+sqrt(k)). Constants are uniform for H in the given polynomial range up to C sqrt R. This is strictly more informative than the fixed-Q depth bound when k is between L log L and L², because the intermediate rough band grows to match the tested depth.

Every center with qmin(x)>=4H is a stationary canonical first-H witness: x even and 3 divides neither neighbor, so 6|x, and no moving label can fire before height H, since every possible label before first H is <=2H+1. If x<R, the number of such boundary centers is O(H)=o(R/L²); otherwise x itself is a birth in the original slab. The use of >=4H is a convenient sufficient stationary cutoff, not a characterization of all zero-gain first-H witnesses.

Consequences for H=floor(R^.4):
* For any k=o(L²), (8) is o(R/L²). Thus a density-scale first-H lower from short-postevent-record witnesses, even with full gain budget 4H, would already imply a density-scale rough-pair lower at cutoff 4H and hence a zero-gain M85 lower.
* Conversely if M85 holds with lower constant c_*, then either its stationary centers qmin>=4H have positive density scale, or at least a positive density-scale family of its remaining sinks has MINIMUM record depth >=kappa_* L², for a sufficiently small fixed kappa_*>0 depending on c_* and the upper constant of (8). To see this, delete all qmin<4H sinks with some witness of k<=floor(kappa_* L²); (8) costs <=C sqrt(kappa_*) R/L²+o(R/L²), made <c_*/4. The retained nonstationary sinks have the stated depth in EVERY successful budgeted witness. The stationary vs nonstationary split can vary with R. If the original lower is assumed only along an unbounded sequence, one of the two alternatives occurs on an unbounded subsequence.
* The intermediate band [H/L^6,4H) alone has O(R log L/L³)=o(R/L²) centers by (7). Combining this deletion, (8), and the previous global-top pruning of 1d7517b4 yields an asymptotically equivalent M85 disjunction: a density-scale stationary lower, OR a density-scale lower on active sinks qmin<H/L^6 whose every budgeted witness has >=kappa_* L² strict postevent records, all top p>=H/sqrt L full waits <sqrt H/L², and all successive top relays gain >sqrt H/L² (integer rounding as in the earlier note). Equation (6) can additionally be imposed after a further small fraction deletion. The dynamic condition is stronger than merely a growing number of events or a long common elapsed interval.

This does not establish either lower branch. It changes the research target qualitatively: a successful M85 approach using only o(log² R) postevent record improvements must break the static roughness barrier itself, whereas a genuinely active proof needs quadratic-log postevent-record complexity at density scale. One cannot infer this lower on the number of records of an arbitrary single nonstationary sink.

## 5. Near-square-root consequence: new sufficient condition for twins

Let H=floor(4 sqrt R/L^B0), fixed B0>=0 (any fixed constant multiple of sqrt R/L^B0 works). If a center x~R is non-twin, at least one positive odd neighbor is composite, hence qmin(x)<=sqrt(2R+1). Use the optimized Q of section 4. In (7) use U=sqrt(2R+1) instead of 4H; if U<Q the intermediate set is empty. Since log^+(U/Q)=O_B0(1+log L+lambda_k), the same proof gives
    N_nontwin(H,k) <<_B0 R/L³ * (1+log L+sqrt(k)),
                      0<=k<=c0 L².                       (9)
This counts all distinct NON-TWIN first-H sinks with gain<=4H and some witness of k or fewer strict postevent records. It does not require assuming finitely many twins in deriving the upper itself.

Hence the following is a sufficient condition for infinitely many twin primes:
    for unbounded R, at least c R/L² distinct actual first-H sinks
    with gain<=4H and some witness k=o(L²).
By (9), the non-twin sinks would be o(R/L²), so the same slabs contain a positive density-scale number of actual twin centers. More quantitatively, any lower exceeding the right side of (9) by a quantity tending to infinity gives unbounded twin counts (with the upper constant accounted for). The new condition permits gain as large as 4H; it replaces the earlier subcritical gain/time or very long terminal idle assumption with a short RECORD-count restriction. It is sufficient, not necessary; no such density lower near the square-root height is proved here.

## 6. Exact Pareto transport for minimum record depth

For computation or proof of a lower on these counts, simple minimum-ancestor transport is no longer enough. Let a physical pre-FIRST-H state be v=(x,h) in the canonical slab. A witness label is (A,M,k), where A is the actual birth, M>=3 is the largest POSTevent height or birth height encountered to this point, and k is its strict postevent-record count. M is NOT updated on idle ticks. A moving edge to postheight h' updates
    M'=max(M,h'),    k'=k+1_(h'>M).
Idle edges preserve M,k, even the final idle to H. Gain at any state is A-x. Thus hard budget B=4H is tested by A-x<=B. For fixed v,M,k, keeping only the smallest A is exact.

More generally at a common physical state, label (A1,M1,k1) dominates (A2,M2,k2) if
    A1<=A2,   M1>=M2,   k1<=k2.                             (10)
Both have the same deterministic actual future until first H or a spatial exit. The first label has no greater future gain at any state, and its record maximum remains at least the second's under the common sequence of moving postheights. Any future new record of the first is also a new record of the second. Hence its cumulative record count remains <= the second's. Discarding dominated labels preserves EXACT reachability with any fixed upper bound on gain and record count and the minimum k of all valid witnesses at each sink. Keep Pareto frontiers under (10) in the physical DAG (decreasing x on moves, increasing h on idles). An equivalent event-to-event graph uses only births and moving arrivals, the deterministic next event or the first-H idle termination; moves strictly decrease x, so process x in decreasing order. That graph does not need to merge idle interiors to be exact for the minimum over witnesses.

A new executed audit confirms that minimum gain and minimum record count are genuinely different objectives, not just a theoretical warning. At R=12000,H=42,B=84, sink x=11970, the minimum ancestor A=12000 has k=1, whereas A=12012 is a valid witness with k=0. This example is for the global min-ancestor vs min-depth distinction; the min-A-only graph happens to preserve k=0 at this particular sink. Across all six tested slab/budget cases, 129 sink instances have different k for the globally minimum ancestor, and the graph discarding all but the smallest ancestor at every physical event state loses the true minimum k at 90 sink instances. The Pareto graph gives the correct minimum k in all 9785 sink instances. No asymptotic bound on the number of Pareto labels is asserted.

## 7. Record-discounted max flow and physical projection of the residual

We now apply (8),(9) to a weighted trial/true criterion using the earlier first-height maximum-ancestor residual method, rather than introducing a new lower-sieve conjecture. Work on the original physical tick DAG with x even in [R-4H,2R], 0<=h<=H, canonical injections at h=3 and first-H sinks; discard edges outside the rectangle. Add only the running POSTevent maximum M as an auxiliary state coordinate (M in [3,H-1]). All physical successors are independent of M. For moving edges update M as in section 6; for idle edges, including the terminal edge, preserve M. At every edge attach weight
    w = L^(-lambda (x-x')/H) exp(-1_(move and h'>M)/K),
with fixed lambda>0, any K>0. This is <=bar w=L^(-lambda (x-x')/H)<=1. The exact augmented max recursion is
    C(v,M)=max(b(v,M), max_(u,M') -> (v,M) w C(u,M')),
where b=1 at canonical births with M=3, else0. Maximum over all M at sink x, denoted C_H(x), equals the maximum actual witness score
    L^(-lambda G/H) exp(-k/K).
The graph is finite, so positive maxima are attained; gain and record count telescope exactly. The rectangle can contain paths from very distant roots with G>4H, but each such witness has score <=L^(-4lambda); we do not call those paths budgeted. A path with G<=4H necessarily stays in the rectangle.

Crucial projection lemma. Let F be ANY nonnegative trial array on augmented states, with positive residual
    r(v,M)=[F(v,M)-(T_true F)(v,M)]_+.
Define d(v)=max_M [F(v,M)-C(v,M)]_+, r_*(v)=max_M r(v,M).
Because the max operator is one-sided Lipschitz in the maximum norm on its incoming terms, rather than needing a sum over all incoming auxiliary states,
    d(v) <= r_*(v)+max_(u->v) bar w(u,v) d(u).
Empty max is 0. Define the physical debt by the exact recursion
    D(v)=r_*(v)+max_(u->v) bar w(u,v) D(u).
Then d(v)<=D(v) in topological order. In particular, writing F_H(x)=max_M F((x,H),M),
    C_H(x) >= [F_H(x)-D((x,H))]_+.
Also D(s) is no larger than the sum of r_*(v) over true physical ancestors of sink s (or a more precise gain-weighted sum), since bar w<=1. Each physical vertex reaches at most one physical sink by unique outgoing edge. Therefore
    sum_x C_H(x) >= sum_x [F_H(x)-D(x,H)]_+
                  >= sum_x F_H(x)-sum_v r_*(v).             (11)
This avoids ANY multiplicative loss from the number of possible running maxima M. The maximum-path debt D is also sharper than summing defects over every incoming physical branch. Exact D may require true suffix routing from residual support, so (11) is a certificate, not an automatically small error estimate.

If F is the exact augmented max flow for a trial physical deterministic graph with the same birth and sink domains, same weights on common physical edges and same auxiliary updates there, missing trial incoming contributions are the only sources of positive residual. For each v,
    r_*(v) <= max_(changed trial u->v) bar w(u,v) max_M F(u,M)
            <= sum_(changed trial u->v) max_M F(u,M).
Indeed compare the trial maximizing incoming term with the true operator on the same array; if it is a common edge (or injection) it causes no positive residual. Thus
    sum_v r_*(v) <= sum_(changed physical u) max_M F(u,M).   (12)
Swap true and trial to obtain the opposite direction with C. The same physical defect bound as the earlier gain-only maximum-flow theorem survives record discounting. No reliance on independent histories or assumed equality of different auxiliary states.

## 8. Remove the necessarily resetting top labels with O(R/L³) error

Use the trial rule retaining all odd primes <=z=floor(2H/3), lambda=13, and arbitrary K>0. All p>(2H+1)/3 necessarily reset to h=0 or3 if fired before first H (the earlier reset-bridge lemma); the trial excludes all such labels, but can still contain smaller reset labels. A changed physical prestate has actual winner p>z, trial idle, p<=2h+3, h>=H/3-O(1).

As in the earlier top-band gain-only transfer, there are O(R/L) distinct changed physical sources: for fixed p,s, O(R/p) spatial centers and O(H/p)=O(1) possible clocks in the height strip; sum over z<p<=2H+3 with reciprocal sum O(1/L). Split them by the existence of a trial witness to that prestate with G<=h/2. If none exists, every weighted score there is <=L^(-13h/(2H))=O(L^(-13/6)); the entire contribution to (12) is O(R/L^(19/6)). If such a low-gain witness exists, the earlier mod2310 certified complete-wait bound W<=17G/8+395/12, also valid for the truncated rule with z>=11, and t=h-3+G/2 show its final idle I>=3h/16-O(1). Therefore qmin(x)>min(z,I/2)>=H/40 for all sufficiently large R. The actual omitted winner p>z divides x+s=pv. Both v>1 and pv-2s are H/40-rough. Uniform two-form upper O(R/(p L²)) times O(1) clocks, summed p, gives O(R/L³) such low-gain keys. The same proof holds for true witnesses (replace truncated rule by actual rule). This extends the earlier top-band transfer to the stronger discount and the record-weighted objective:
    |sum_x C_H(x)-sum_x F_H(x)| << R/L³.                   (13)
All constants uniform in K>0; score <=gain-only score was sufficient. The earlier proof was stated for fixed theta<1/2. Here its arithmetic upper also covers H<=C sqrt R and H>=R^theta0, because v~R/p is still of positive polynomial size and >1, and a fixed small polynomial two-form sieve has adequate interval length. There is no use of pq< R for this single-key estimate. The previous mod2310 complete-wait certificate is inherited, not independently Lean-verified here.

## 9. A new weighted sufficient condition on the simplified trial graph

Let k_x be the minimum postevent record count among gain<=4H actual canonical witnesses of sink x, infinity if none. Since all scores are <=1 and a high-gain witness contributes <=L^(-4lambda),
    C_H(x) <= exp(-k_x/K)+L^(-4lambda),
with exp(-infinity)=0. For the selected class of sinks in (8) or (9), the depth counting bound controls the weighted sum. Put k0=floor(c0 L²), use the bound only for k<=k0 and the trivial O(R) centers above k0. The integral identity exp(-k/K)=int_k^infinity exp(-t/K) dt/K and the bound on the partial counting function give
    sum_(qmin<4H) C_H(x)
       << R/L³ (1+sqrt K) + O(R exp(-k0/K)+R/L^(4lambda)),
for H=R^.4, and
    sum_(non-twin x) C_H(x)
       <<_B0 R/L³ (1+log L+sqrt K)
                     + O(R exp(-k0/K)+R/L^(4lambda))         (14)
at H=floor(4 sqrt R/L^B0). For the integral beyond k0 bound the entire mass by O(R exp(-k0/K)); the sqrt term follows from int_0^infinity sqrt(t) exp(-t/K) dt/K=O(sqrt K). No bounds on long record histories have been extended beyond the certified range of (8),(9).

Choose K=(log L)^2, lambda=13, z=floor(2H/3). The two tails in (14) are o(R/L³). Equations (13),(14) give a concrete new sufficient condition for twin infinitude:
    for unbounded R, sum_x F_H(x) = omega(R log L/L³)
    with H=floor(4 sqrt R/L^B0) in the specified truncated graph.
Here omega means the ratio tends to infinity, not just a positive constant. The true weighted non-twin capacity is O(R log L/L³), and the transfer loses O(R/L³). Thus such a lower would force actual twin centers in those unbounded slabs. The score is a maximum over actual TRIAL birth histories, penalizing both gain and strict postevent records; it is not the earlier single-cap live reward, nor the clipped summed flow. This is a new scalar sufficient target, not an established trial lower. It can be evaluated by the augmented max recurrence and localized certificate (11).

At H=floor(R^.4) a trial weighted lower of order R/L² with the same parameters would, by (8),(13),(14), already supply a density-scale set qmin>=4H. It is therefore a sufficient route to the STATIONARY branch of M85, not a way to bypass the active quadratic-log requirement. This distinction suggests separating future strategies: use the record-discounted trial criterion for a short-record/static or twin breakthrough; use the unweighted hard-budget Pareto/section transport and the previous top pruning if pursuing the deep active branch. Neither is established by the present finite pilot. The weighted sufficient condition demands a stronger type of witness than the original M85, though the near-square weighted total threshold is lower than R/L².

## 10. Executed verification and persistence

All three new audit files were executed as ECMAScript and independently retrieved from their exact commits and the active branch; full text matched. Finite simulations/proxies are not asymptotic estimates. No new Lean compile or independent specialist review.

1. research/lean/negative_min_deficit_record_depth_audit.mjs @11d766942404cd53ffc04cb59eda98751b176760, blob 0c6ad3124b4833d2561499c2ebb5e0227cdba123. Actual slabs R=12000,48000,192000,768000, H=floor(R^.4), proxy Q=floor(H/10), m=1,2,4,8,16. 170004 roots,2176859 completed moving incidences within budget,163476 successful first-H witnesses,871498 strict postevent-record incidences over all examined prefixes,765 active terminal witnesses,3825 band profiles,28888 good and13537 bad record incidences across profiles,13537 local bad-key pin/source checks,729 distinct sink-band charges,1232 independent literal clock scans. All passed. For R768000 there are38 distinct active proxy sinks with minimum record depths in [4,24], max actual depth30. Synthetic integer deficit chains (not MIN trajectories) with log span>8 exercised the large-log descent implication nonvacuously; logarithmic sums used floating tolerances, algebra and calendar inequalities exact integer checks.

2. research/lean/negative_min_record_depth_pareto_audit.mjs @7761020c3f8701193935a435ae21be6ed2f84c09, blob f6ba15cb22b87bacdcee4504a39f6da1ecc131d6. R=12000,48000,192000, H=floor(R^.4), B=2H and4H. Exact comparison of Pareto event graph to separate per-root traversal: 9785 sink instances,363327 label offers,57605 pruned,14218 strict-record and1590 strict-maximum dominance instances; maximum Pareto frontier 11 in the largest 4H run. All minimum-depth maps exactly agree; global min ancestor differs at129 sink instances; min-A-only graph fails depth optimum at90. This validates (10) structurally, not a bound on asymptotic frontier size.

3. research/lean/negative_min_record_weighted_projected_residual_audit.mjs @d6106d3e85e2dce73c8b2692be3b43213ee31a2b, blob 5c80dde4436744541daa84f9efc06b250f71d8f7. Actual tick graph, R=12000,48000,192000, H=floor(R^.4), lambda=13,K=(log log R)^2,z in {7,floor(2H/3),floor(1.5H),2H+3}. Simultaneous exact-structure trial and true max recursions, true operator on trial array, projected residual and maximum-path physical debt. Floating weights (tolerances, not directed-rounding certification). 6548508 physical-state inequality checks,35425 sink checks,80425 changed-key incidences,2810809 states with multiple trial M values,34302 nontrivial projected-debt savings over summing augmented residuals. All passed, full cutoff exact agreement, max violation 0 in these tests. R192000,H129,z86: trial weighted mass3868.020065, true3057.016433, raw defect924.866186, raw lower2943.153879, localized max-path lower3057.015979. z7 has negative raw lower but localized lower2915.249126. These finite residual values illustrate the certificate, not a trial lower at H~sqrt R or a proof of asymptotic density.

## 11. Source ledger and remaining problem

- Previous global-top pruning 1d7517b4aac7f872ba395746680e905a26657900, research/2026-11-28-min-negative-global-top-relays-and-rough-anchor-packing.md; previous active-first-record-and-deficit note and near-square first-height reset-bridge note reopened at pinned base. The new record-minimum descent and optimized counting argument use the earlier event deficit inequalities and standard two-form upper, but are not a claim that a new external sieve theorem was obtained.
- Prior maximum-ancestor and residual transfer, research/2026-11-28-min-negative-height-section-localized-and-max-flow.md §3, reopened at 1d7517b4. Earlier mod2310 paper certificate (complete waits W<=17G/8+395/12) inherited as used there; no new Lean check. New max-path residual projection and transfer (11)-(13) use the same physical changed-key cost despite the added record maximum. No fresh high-level distribution input.
- No changes to core b0e26798535b2c997f1383c1dc37bbe560aac938, main or sibling branches. No M85 or unconditional twin proof. Further research can use the explicit trial weighted sufficient condition, or the genuine active branch with its now quantitatively large record-depth/deficit-band requirements. The central unresolved issue is a lower on actual/trial reachability at the target heights, not merely another upper on candidate keys. The new upper estimates clarify why short local HIGH extensions and few postevent records cannot alone establish a genuinely active M85 lower.
