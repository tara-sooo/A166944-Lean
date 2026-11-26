# Hypothetical infinite MIN worlds IX: rational clock locking and transverse crossing costs

2026-11-26 JST. Independent continuation of [524df93](https://github.com/tara-sooo/A166944-Lean/commit/524df930d14ee83d03258699cb618d8da8afcb7a). Sources: [III clock capacity](https://github.com/tara-sooo/A166944-Lean/blob/ae36ba7e6002e69244233f89fbd810c04a68bbea/research/infinite-orbit/phase_graph.md), [VI recovery ledger](https://github.com/tara-sooo/A166944-Lean/blob/00f533d998b0cc87f48850b95476e41583e68539/research/infinite-orbit/recovery_budget.md), [VII inverse resonance](https://github.com/tara-sooo/A166944-Lean/blob/1ca1058926f239104c7961d31d67d224fcef139e/research/infinite-orbit/deep_inverse.md), [VIII charged reverse](https://github.com/tara-sooo/A166944-Lean/blob/524df930d14ee83d03258699cb618d8da8afcb7a/research/infinite-orbit/charged_reverse.md). Sibling preflight direct [7b426da time-height localized upward supply](https://github.com/tara-sooo/A166944-Lean/blob/7b426daaea1e966b1ee35414baa036e5ce3c6092/research/2026-11-26-min-direct-time-height-localized-upward-source-capacity.md) and unified [eb16cdf four-form reset guard](https://github.com/tara-sooo/A166944-Lean/blob/eb16cdf4b2377c1dbda40ced0aaea7463a5d2d7b/research/2026-11-26-min-unified-reset-four-form-guard.md). The new coordinate tracks a moving rational line in clock/horizon space, rather than a fixed ordinary deficit height. We allow all high waits and arbitrary multiplier size. Paper deductions and finite exact MIN diagnostics, not a Lean proof or external novelty claim.

## 1. Corrected slope and quantized transverse coordinate

In a physical event block with even pre-horizons in [X,lambda X), lambda>1 fixed, put B=floor sqrt(lambda X+1). Each complete event has p odd eligible, g=p-1, 1<=w<=2p<=3g. The canonical envelope H/2<=t<=3H+3 is preserved; it may also be imposed on arbitrary intermediate states without asserting ancestry. Write a post-state (J,n), side s=n mod2, adjusted deficit x=2n-J-6s, and
    A=J+2s, C=n-2s, mu=C/A = 1/2+x/(2A).
By VII the selected p divides both A and C. On any high event p>=5, x is a multiple of 2p, and nonnegative ordinary deficit gives x>=-6. Thus x>=0, with x=0 precisely the adjusted reset class. Consequently
    1/2 <= mu <= 3+3/X <=4
for X>=3. This is exact for high post-states, including resets.

For any reduced positive rational a/b, define the transverse coordinate
    Z_(a,b)(J,n)=b n-a J-2(a+b)s=b C-a A.
At every high post-state p divides Z. In particular if p>=T and |Z|<T then Z=0, so the state lies on the exact corrected rational line
    n=(a/b)J+2(1+a/b)s.                              (1)
Equivalently a tube |n-(a/b)J-2(1+a/b)s|<T/b contains no off-line high post-states. A fixed O(1) corrected-width tube around any fixed rational slope is therefore exactly resonant for sufficiently large T. If b is odd, reduction of Z=0 modulo 2 forces s=0 (J even, n mod2=s). If b even, both sides are not automatically feasible; actual clock parity, horizon divisibility and earliest selection must still be tested. The exact reduced denominator of mu is b=A/gcd(A,C). The distinct-label collision states from VII have bounded b; bounded b does NOT imply a collision, and large ordinary deficit does NOT imply bounded b.

## 2. Clock alignment between selected rational states

Choose ANY actual list of high complete events with T<=p<=B (T>=5, tending to infinity), whose corrected reduced slope denominators b are <=Q, with Q an integer>=1. They may include fast, weak, long, reset and deep nonreset clocks. Select the entire list in the same physical block, retaining the actual relays across gaps; no independent phase choices. Let F be selected gain, U full complementary gain, G=F+U total block gain, k selected event count. For consecutive selected post-states i,j, write E for the gain of all intervening unselected events and W for their time, so 0<=W<=3E,
    J_j-J_i=E+g_j, n_j-n_i=W+w_j.
If their slopes are equal mu, (1) gives the exact relation
    w_j-mu g_j = mu E-W+2(1+mu)(s_j-s_i).            (2)
Hence |w_j-mu g_j|<=4E+10. This is stronger than the ordinary deficit budget in a moving line: when E is small, the wait/gain ratio must approximate the corrected slope, even if ordinary deficit is growing linearly with J. In particular if E<=M_R for a fixed low-only relay, the error is bounded independently of p and the multiplier. A fixed-slope mixed run of high post-states on the line has w/g=mu+O_R(1/T) after the first event. It cannot contain both a fast w<=g/4 and a long w>=p-2 ending event after the first for large T. This does not forbid a long event followed by a fast event through a larger relay.

For different slopes, subtract the two corrected line equations using mu_i as reference:
    (mu_j-mu_i)(J_j+2s_j)
      = W+w_j-mu_i(E+g_j)-2(1+mu_i)(s_j-s_i).
Since 0<=W+w_j<=3(E+g_j), 1/2<=mu_i<=4, and E+g_j>=2, we obtain
    |mu_j-mu_i| <= 9(E+g_j)/X.                      (3)
Two distinct reduced rationals with denominators <=Q differ by >=1/Q² (integer cross product). Thus EVERY change of selected slope needs
    E+g_j >= X/(9Q²).                               (4)
In particular, with any bounded low relay and B=O(sqrt X), fixed Q cannot change in a high/low-only resonant run for large X. More generally, there are at most S<=9 Q² G/X slope changes along the whole selected list, because the consecutive post-to-post gains are disjoint.

Define the absolute clock mismatch
    D_clock=sum_selected |w_i-mu_i g_i|.
A single mismatch is <=4g_i. Pay the first selected event by 4B; for changes pay <=4B each; for the same-slope edges use (2) with disjoint relay intervals. Then
    D_clock <=4U+10(k-1)+4B(1+S),                  (5)
for k>=1 (empty list trivial). This is unconditional. In the locked-scale regime
    18 B Q² <= X,                                   (6)
(4) implies E>=X/(18Q²)>=B>=g_j at each switch. Its mismatch <=4g_j<=4E can be paid by its OWN actual relay instead of a separate boundary. Thus the sharper estimate is
    D_clock <=4U+10(k-1)+4B.                        (7)
Moreover S<=18 Q² U/X. These do not require a common slope on the full list or a small ordinary deficit. For square-root-scale B, (6) holds eventually for Q=o(X^(1/4)), or Q<=c X^(1/4) with sufficiently small constant. Equivalently requiring gcd(A,C)>=K X^(3/4) with large enough fixed K implies a denominator bound in the locked regime, since A<=lambda X+B+2. Such gcd concentration is a hypothesis on a population, not a consequence of deep deficits.

## 3. Fast and nonpositive high clocks need complementary gain on resonances

Let F_fast denote gain of selected clocks with 4w<=g. Because mu>=1/2, |w-mu g|>=g/4 for each. Under (6),
    F_fast <=16 U+40(k-1)+16B.                      (8)
For selected clocks with adjusted deficit x>=kappa X and nonpositive ordinary drift 2w<=g (kappa>0 fixed), mu>=1/2+kappa/(2(lambda+1)) for large X because A<=(lambda+1)X. Therefore their gain F_deep_down satisfies
    kappa F_deep_down/[2(lambda+1)]
        <=4U+10(k-1)+4B.                            (9)
The same argument with a smaller positive gap applies to w/g below the actual slope by any fixed margin. For long selected clocks w>=p-2=g-1 on slopes mu<=1-delta, delta>0, mismatch is at least delta*g-1, hence their total gain F_long_low obeys
    delta F_long_low <=4U+11k+4B.                    (10)
This last estimate is only about slopes below 1 by a fixed margin. No prohibition of long clocks on high slopes mu>=1 follows.

Since k<=F/(T-1), B=o(X), in a macroscopic block with F=Theta(X), U=o(X), Q satisfying (6), these three mismatched populations have o(X) gain. Thus a survivor concentrating its high events on small-denominator deep slopes and using little complement cannot repeatedly supply macroscopic fast gain or nonpositive ordinary drift there. Its wait/gain ratio is asymptotically locked in gain-weighted L1 to its corrected slope. It may instead occupy states with large denominators, use a macroscopic complementary population, or grow its ordinary deficit on a resonant slope. This is not a general prohibition of alternating long/short high trajectories; most actual high states need not satisfy the denominator cap.

## 4. Canonical anchor, precursor and tagged extension

At the original odd canonical root H0=2M-2, t0=M+2, t0 odd, the corrected slope is EXACTLY (t0-2)/(H0+2)=1/2. The root is a sentinel for (2)-(4) (not a selected event). Start the selected list at the original root with all actual prior events included in U. Replace Q by Qstar=max(2,Q). If 18 B Qstar²<=X and H0>=X, even the first event can be charged by its actual pre-entry relay, by (2) if same slope and by (4) otherwise. Thus
    D_clock <=4U+10k,     F_fast<=16U+40k.           (11)
There is no N B initial credit when summing (11) once over each full original lifetime. Deep and long-low analogues of (9)-(10) have the same zero-credit improvement. This is an original-lifetime tagged statement; a core-only application requires actual entry boundaries or their costs. It does not imply that U is omitted waiting mass.

There is an additional stronger precursor lower bound near the canonical slope. Every nonreset with reduced denominator b<=Q has 2a-b>=1, hence
    x=(J+2s)(2a-b)/b >= X/Q.                        (12)
If the actual cumulative gain from the root is G0, the canonical envelope d'<=6+5G0 gives
    G0 >= (X/Q-6)/5.
Thus within a short original lifetime of total gain H_life one necessarily has b>=X/(6+5H_life) for every high nonreset. For H_life=X/polylog, this already excludes fixed-denominator deep nonresets. If a selected nonreset immediately follows a selected reset (or the root sentinel) on the selected list, the intervening unselected gain E plus final gain g must supply d'-d_previous>=X/Q-6, so
    E >= (X/Q-6)/5-B.                               (13)
This stronger entry/switch charge uses the special denominator 2 of the reset slope and actual ordinary deficit, not the general Farey spacing. Such intervals are disjoint on each selected list; can sum the positive part over reset-to-nonreset transitions, including first entry from the root. For Q=O(1) this is a macro precursor per affected original tag, for growing Q it is not necessarily macro. In the regime Q=O(X/H_life) and B=o(H_life), it is Omega(H_life) for tags actually making such entries. This supplements the newest unified canonical guard (no independent extra credit for the same events). Neither low-denominator dominance nor these entries are forced by the currently established unified hypotheses.

## 5. A diagonal crossing toll without any denominator cap

There is a separate use of the integer transverse coordinate, even when slopes are arbitrary. Fix the diagonal rational a=b=1. Write L=n-J-4s at a high post-state. Then p|L, and L=0 requires s=0 and n=J exactly by parity. Take any consecutive selected high post-states with T<=p_i,p_j<=B, arbitrary waits and actual relay E,W (could contain any other events). The exact difference is
    L_j-L_i = W+w_j-E-g_j-4(s_j-s_i).
Using 0<=W<=3E, 1<=w_j<=2p_j gives
    -(B+2+E) <= L_j-L_i <= B+5+2E.
If L_i,L_j have strict opposite signs, their difference has magnitude >=p_i+p_j>=2T. Consequently
    E >= (2T-B-5)/2.                                (14)
For B<=(2-eps)T and fixed eps>0 this is Omega(T). A high/low-only mixed list with fixed low cutoff R has E<=M_R, so no direct sign crossing between nonzero diagonal coordinates in a sufficiently large narrow band. It must either visit an EXACT diagonal state in the selected list or use a substantial other relay. This is not a proof that the entire trajectory stays on one side; zero vertices are permitted. On one actual selected list, strict opposite-sign adjacent pairs have disjoint relays, hence their count times the positive part of (2T-B-5)/2 is <=U. This transfers directly to tagged lists without treating shared physical events as independent gain.

The direction is constrained further by clock type. For a long ending event w_j>=p_j-2=g_j-1,
    L_j-L_i >= -E-5.
Thus a downward sign/zero transition involving at least one nonzero coordinate (L_i>0,L_j<=0 or L_i=0,L_j<0) costs E>=T-5. For a fast ending event 4w_j<=g_j,
    L_j-L_i <= 2E+4-3g_j/4.
An upward sign/zero transition (L_i<0,L_j>=0 or L_i=0,L_j>0) costs 2E>=T+3(T-1)/4-4. These are exact pointwise inequalities, not a claim that every diagonal crossing alternates between these two event classes. They distinguish a change of corrected time/horizon ratio from an ordinary deficit drop; a crossing can take place while the ordinary deficit is increasing. The finite audit tests (14) including genuine strict crossings; the directional refinements are paper deductions from the same exact difference formula.

## 6. Reproducible finite diagnostics

Final audit [85fc20e](https://github.com/tara-sooo/A166944-Lean/blob/85fc20e5c08674d60de924752c29cf27f0d3fc3d/research/infinite-orbit/rational_clock_audit.mjs), blob 43b40fd966d26fb3298e51b2544590bab770064d, exact remote readback. Run node research/infinite-orbit/rational_clock_audit.mjs. Actual ECMAScript in the available runtime, not separate Node. Final assertions pass. X=4096,16384,65536,262144, [X,4X), T=ceil(sqrt X/2), B=floor sqrt(4X+1), Q=1,2,3,4,8,16, both all high and positive-adjusted-only selections. No safe endpoint condition. 27,648 sampled canonical starts, 461,080 targeted exact reduced rational arrival starts (denom<=8, shortest and longest feasible wait), plus 44,075 targeted starts within a few multiples of the diagonal (correct parity). Targeted states obey envelope and exact MIN selection, not established canonical ancestry. In total 532,803 start incidences, 529,696 actual finite stops, 3,107 upper exits, zero event-cap unresolved, 13,484,128 actual event incidences. 1,347 independent literal tick gcd controls.

- 3,365,168 selected event/configuration incidences, 2,911,261 fast (4w<=g), 298,528 long (w>=p-2). Not distinct canonical events; targeting deliberately includes shortest waits.
- 311,938 consecutive selected pairs: 304,972 equal reduced slopes, 6,966 different slopes; 23,188 same-slope ending-fast and 204,482 same-slope ending-long incidences. 15,380 equal-slope zero-relay checks.
- 3,053,230 whole-block alignment and deep nonpositive aggregate checks, 2,773,276 deep nonpositive incidences (x>=X/4,2w<=g). 513,307 locked-scale block checks, 581,872 selected incidences therein. No slope change occurred in those conservative locked-scale finite configurations, so the positive switch-charge branch of (7) was not exercised there. The general (3)-(5) have actual switch controls. In locked-scale scans 194,472,186 fast gain was counted across overlapping source/configuration incidences, NOT a distinct physical resource.
- 29,860 canonical anchor controls, 4,368 with the anchor-locked condition. No canonical nonreset high with denominator<=16 in the sampled paths; consequently the low-Q nonreset entry branch of (13) is not exercised by that sample. 12,607 canonical positive-adjusted high events with their unrestricted actual denominators checked (12) and the canonical gain bound. No claim of a uniform exclusion of low-denominator nonresets from canonical ancestry.
- 115,951 consecutive high pairs in the narrower band [T,floor(1.5T)], regardless of wait or denominator; 15,707 diagonal zero events; 763 strict opposite-sign pairs, all pay (14). The targeted diagonal starts produced the strict crossings; not a claim about canonical crossings.

Representative genuine deep same-slope long-to-fast pair, X=4096, corrected slope 7/8:
    first pre (H,t)=(5040,4333), p=71,w=142,s=1,
    first post (J,n)=(5110,4475), adjusted x=3834;
    last pre (H,t)=(5208,4588), p=41,w=4,s=0,
    last post (J,n)=(5248,4592), adjusted x=3936.
Relay E=98,W=113. Equation (2) gives 4-(7/8)*40=-31=(7/8)*98-113-2(1+7/8). Ordinary deficit grows from 3840 to3936 while the high clock changes from long to very short. Both events and relay follow actual MIN from a specified intermediate state; canonical ancestry not established. This is a positive control for the complementary resource alternative, not a contradiction.

Representative strict diagonal crossing, X=4096,T=32,B=48:
    post (4698,4749), p=47,s=1,L=47;
    next selected post (5248,5166), p=41,s=0,L=-82.
Relay E=510; (14) demands >=5.5 (integer E even). Actual ordinary deficit rises from4800 to5084. This controls the distinction between crossing a moving line and decreasing d. Intermediate-state origin, no canonical ancestry.

The finite test uses denominator caps and windows as above; it does not validate asymptotic dominance, bounds on actual U or the short-lifetime unified mass. The analytic theorem, not the sampled maxima, gives (5)-(14).

## 7. Residual world

The previous deep survivor can no longer be made into a small-denominator resonant high population with both little complementary gain and macroscopic fast clocks. Same-slope states impose exact clock alignment, changes cost horizon gain, and narrow-band strict diagonal crossings cost actual relay gain even without denominator caps. However arbitrary large-denominator high states, many complementary events, resonant long/positive-drift growth, or diagonal zero vertices remain possible. Next: investigate actual gcd/denominator distribution of high post-states, especially the complementary large-denominator regime, and whether small-denominator entry/crossing costs can be forced at many scales; combine with height-localized flux only with actual disjoint resource accounting. No all-constraint infinite model, general uncapped run bound, Lean verification or finite-twin contradiction. Main and sibling branches not modified.
