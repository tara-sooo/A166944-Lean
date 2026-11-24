# Rough-anchor arrival caps and signed deletion of relative-large labels

2026-11-25 JST. Continues 996c6b23a20a415491595c6dde18d715b7507a6d on the SAME research/min-cycle-forest-2026-11-24 branch. Original deterministic and sieve deductions, exact finite source replays. New OPTIONAL accounting rule, not an estimate under the unchanged low-only cap. No Lean compilation; no proof of twin-prime infinitude. The long small-relative-label high-state remainder and mass stopped under the enlarged cap remain open.

## 1. Setup and a different treatment of giant triggers

Use canonical MIN: N=X/2 odd original sources M in [X,2X), initial C=2M-2, t=M+2, h=6, individual cutoff K(M)=floor((7M-1)/4), B=ceil(sqrt(7X)). At each executed event label p<=B, least eligible prime r(C)<=p, wait 1<=w<=2r(C), gain p-1, h'=h+2w-(p-1)>=0. All actual horizons and times lie in windows of length O(X). We use the established uniform per-prime bound
    S_p=sum_(eligible even C in the window) r(C)=O(X/log^2 p)
for p>=11. Finitely many smaller primes obey the same bound with an enlarged absolute constant, since r<=p and the horizon window has O(X) states. No new external literature search.

The previous note removed the cost of two W-cell exits and a growing-factor gain-limited continuation from each continued low-height start under a mass cap. Its giant-trigger remainder requires a new label l>64s(p+q+H+W) after two known exits and limited further gain. A naive three-prime CRT count is not the previous two-prime estimate: p q l can exceed X, so the progression length cannot be replaced by X/(p q l) uniformly. The further gain offset also varies. No uniform triple-prime sieve saving is claimed.

Instead add an arrival-state cap, which bounds the source multiplicity at these events independently of their preceding depth. Choose integers D>=1, J>=4, H>=11D, T=ceil(B log^2 B). Call an executed event a rough anchor if
    p>=11, h<=D p, r(C)>=p/(J+4).
All tags at the same attained physical V(t,C) are stopped if their actual active mass is >=T and EITHER h<=H OR at least one incoming executed event of that active group is a rough anchor. Examine all arrivals at the horizon before this test, including root injections. The rule is group-wide, not a stop just for the anchor donor. A group with no actual incoming anchor witness need not stop merely because some hypothetical incoming event could have been an anchor. A stop ends the path before its next event. There is no new execution choice and no change to K(M). This changes the stopped population; one cannot retain the old S_lowstop as the only stop mass. Write S for the total mass stopped by the UNION rule. Every tag stops at most once. The original no-twin natural-terminal cost lower bound applies to every unstopped root.

For the preceding giant trigger, the earlier bound h<=16s(p+q+H+W), together with l>64s(p+q+H+W), gives h<l/4 and r(C)>l/8. It is a rough anchor for the present D,J. Thus the giant trigger is now one of the events whose cost can be controlled, without multiplying three congruence moduli. The following bound includes all rough anchors, not only the first giant trigger.

## 2. Unconditional weighted rough-anchor cost

At an anchor the postheight obeys h'<= (D+3)p+1. For fixed projected key (p,C), eligibility fixes its unique clock residue mod 2p; the possible event time n lies between C/2 and C/2+Dp/2+2p. Hence there are O(D+1) possible actual clocks, even when many previous t lead to the same event. The number of eligible C with r(C)>=p/(J+4) is at most (J+4) S_p/p. Consequently
    sum_(candidate anchor event keys (p,C,n)) p
        <= O((D+1)(J+4) X sum_(11<=p<=B prime)1/log^2 p)
        = O((D+1)(J+4) X B/log^3 B).
The last estimate follows from elementary prime counting and partial summation; for example split at sqrt B, and use the lower bound log p>=log B/2 above it. This is a sum over all candidate clocks, not only the actual graph.

Every executed anchor event has a single landing V; its actual source tags all arrive there before either an accounting stop or natural termination. If this group does not accounting-stop, its total active mass is <T by the new rule, so the anchor-event incidence count is <T. Its r-cost is <=p. If the group does stop, each anchor incidence can be charged to the stopping source tag, at cost <=B per tag, including when a group also meets the low-height condition. Hence total weighted anchor cost
    R_anchor <= O(T(D+1)(J+4) X B/log^3 B + B S)
             <= O(X^2 (D+1)(J+4)/log B + BX).
We used X asymp B^2. No bound on the number of large group merges or on the mass of the stopped arrival groups is required for this cost estimate. In particular the final incoming event to a stopped group is counted, rather than assuming its mass <T. This is why imposing the cap at its LANDING is sufficient for the preceding executed cost. The estimate applies at all depths.

## 3. All low arrivals, low departures, and bounded-gain continuations

All executed events landing at h'<=H have negligible total cost under the same union cap. For fixed (p,C), their arrival clock lies in an interval of length H/2 at spacing 2p. Thus O(1+H/p) possible clocks. Again if the landing group continues its mass is <T; if it stops, each tag contributes at most B once. Sum the r-cost, not p, using S_p:
    R_lowarrival <= O(T sum_(p<=B prime) (1+H/p) S_p + B S)
                 <= O(T X [B/log^3 B + H+1] + BX).
Here sum 1/(p log^2 p) converges. All arrivals are included, regardless of the previous height, including reset events from arbitrarily high states.

For departures from h<=H, every p>2H+20 automatically qualifies as an anchor: h<p/2, 4r>=p-1-h>p/2, and D>=1,J>=4. Other nonanchor low departures have cost <=2H+20. There are O(X(H+1)) candidate low V states, each continuing with <T tags. Their nonanchor cost is O(T X(H+1)^2). Thus the union of all low-arrival, low-departure, and anchor events has cost o(X^2) for the slow choices below. These arguments alone already give the signed reduction in section4, independently of the previous two-exit theorem.

There is also a stronger deletion using continuations. For each continued actual anchor incidence of label p, start a diagnostic marking window at its landing state, of scale A=(D+5)p. Charge subsequent executed events before the next low state, anchor, accounting stop, or natural terminal, while cumulative horizon gain g since landing is <s A and the next label l<=64s A, with s>=1. The next anchor event itself is counted in R_anchor rather than charged in the previous window. The last included nonanchor event can overshoot the gain cap by at most 64s A. Thus each window costs <=100s A by r<=1.5(l-1), regardless of the number of internal steps. This is a per-incidence majorant; allowing overlapping windows could only enlarge the bound. At a continued landing the actual incoming anchor incidences are <T, so summing over the same candidate keys,
    R_anchorwindows <= O(s(D+5) T (D+1)(J+4) X B/log^3 B).
If a window has pre-gain g<s A but its next label exceeds 64s A, then its preheight <=(D+3)p+1+5g<=6s A. Hence h<l/2 and nonnegative postheight forces r>l/8; it is itself a new anchor. The arbitrary oversized-jump trigger is therefore charged as another anchor, rather than treated as unmarked solely because of its size. A window may end through long gain g>=s A, and the portion beyond that cap is not controlled by this budget.

One may mark ALSO the two-exit and bounded-gain prefixes from each actual low start in the previous note. The new stopping rule only truncates trajectories from their original source, and continuing low starts still have mass <T, so that prior hypothetical-start count is unchanged as an upper bound. If a new anchor stop occurs midway, it only shortens the marked prefix. There is no need for high-state multiplicity bounds inside those earlier low-start prefixes. Take the union of the marked events, counting each actual tag-event at most once; its cost R_M is bounded by the sum of the separate upper bounds.

Concrete parameter sequence (rounded, with fixed minimum values for small B):
    H=floor((log log B)^(1/4)),
    W=largest even primorial <=(log log B)^(1/8),
    f=(log B)^(1/4),
    D=J=floor((log log B)^(1/8)), J>=4,
    s=(log log B)^(1/8).
Eventually H>=11D; all parameters tend to infinity. The new anchor-window normalized cost is O(s(D+5)(D+1)(J+4)/log B)=o(1), and low-arrival/departure terms after division by X^2 are O(1/log B+(H+1)^2 log^2 B/B+1/B)=o(1). The earlier low-start two-exit/extension bound is o(X^2) with these H,W,f,s. Therefore
    R_M=o(X^2).
No use of eta->0, finite-time infinite-CRT peak convergence, or full high-excursion lifetime hypothesis. In the enlarged-cap process, every first giant trigger of the previous mark is included in R_M, as are all subsequent rough anchors and their gain-limited windows. The unmarked events need not all occur in one uninterrupted window; marked events can recur after an earlier unmarked portion.

## 4. Signed global ledger eliminates the remaining comparable-label events in cost

Partition EVERY unmarked executed source incidence into:
    small-relative: D p < h,
    comparable: D p >= h.
All unmarked events have h>H and h'>H (both low departures and arrivals were marked). Since H>=11D, a comparable label is >=11. Because its event was NOT an anchor, r(C)<p/(J+4). Integers p,r,J give (J+4)r<=p-1. The exact signed change and wait inequality imply
    h-h'=(p-1)-2w >= (p-1)-4r >= J r.
Thus every remaining comparable-label event has NEGATIVE height drift and its r-cost is <=(h-h')/J. This includes labels much larger than the current height if they can meet the stated constraints; no separate probability law is needed.

Let R_s denote total unmarked small-relative cost, R_d unmarked comparable (downward) cost, R_all=R_M+R_s+R_d. On each original source path (truncated at any stop), height begins at 6, remains nonnegative, and its total negative height variation is at most 6 plus total positive variation. This is a per-source identity, so it remains true after summing over merged trajectories with their actual source multiplicities, including stopped tags. Every positive increment is at a marked or small-relative event, and is <=4r. Hence
    J R_d <= 6N+4(R_M+R_s),
    R_all <= (1+4/J)(R_M+R_s)+6N/J.
This is the new signed elimination. Unlike an estimate based on the full unmarked gain, it does not require a bound on the number of comparable events or a new sieve for their particular clocks. Taking J->infinity and R_M=o(X^2), one gets
    R_all <= (1+o(1)) R_s + o(X^2).
No prior upper bound on R_s is needed in this algebra. The term (1+o(1))R_s is retained explicitly, rather than silently treating R_s/X^2 as bounded; it is also bounded in this canonical window by the per-source elapsed/gain inequalities and h>=0, giving R_all=O(X^2), since each source's total selected gain <=O(X) and r<=1.5(p-1).

On no-twin windows the previous cost lower bound gives R_all>=cX(N-S) with a uniform c>0. Consequently
    R_s >= (1-o(1)) cX(N-S) - o(X^2).
In particular R_s=o(X^2) and S=o(X), or a sufficiently strong joint strict deficit, would contradict the no-twin hypothesis. The residual r-cost now concerns only interior high-state events with p<h/D, after deletion of all the marked portions. The new rule increases the possible stop mass S, and there is NO bound S=o(X) here. Nor is R_s shown small. Thus this is a reduction of the high-height analytical target, not a proof that the enlarged-cap process has small total cost or a completed proof. The original weighted far-coalescence route and LOW phase limit remain separate unresolved routes.

## 5. Exact finite diagnostics and persistence

Saved research/min_rough_anchor_signed_remainder_audit.mjs and research/min_rough_anchor_signed_remainder_results.json with exact remote readback at f73f4cc1e6e463d02c7a0a8e5ec0ce81fd0a6eea. Earlier variant (without marking low arrivals and fixed threshold r>=p/8) preserved at 45f622aa16b946012224e0123d84d88ffb4c3d4c. Exact integer SPF and canonical MIN, horizon-order active groups, individual cutoffs. X=4096,16384,65536,262144, diagnostic cap T=max(3,floor(B/8)), (H,D,s,J)=(24,2,1,4) or (48,4,2,12). These finite parameters differ from the asymptotic sequence. Stop at group V if h<=H or any actual incoming anchor and mass>=T. Track every executed anchor incidence until landing, separately count continued/stopped anchor cost, start/truncate its gain-limited window, mark low departures and low arrivals; then partition all other events by D p<h. The audit does NOT add the earlier two-exit prefixes (the proof permits the additional union). Verify candidate clock cap per projected anchor key, postheight bound, all incidence conservation, stop/terminal conservation, anchor-window and stopped-anchor cost budgets, negative drift bound on unmarked comparable events, telescoping variation bound and final J R_all<=(J+4)(R_M+R_s)+6N. No numerical evaluation of the asymptotic sieve constant.

At X262144,H48,D4,s2,J12,B1355,T169: N131072, 16168 stopped tags (7834 low,15066 anchor,6732 overlap),114904 natural twin terminals,3440576 executed source incidences. Total cost94358254; anchor69769218 (4449505 on stopped arrivals), additional anchor windows20052471, nonanchor low departures3975619, nonanchor high-to-low arrivals55969, so marked93853277, unmarked small-relative504977, unmarked comparable zero. At H24,D2,s1,J4, total94664609, marked91379603, small-relative3285006, comparable zero. The earlier fixed-threshold audit at the same X,H24,D2 (without low-arrival marking) had comparable cost29979 and associated height loss308058; its J=3 weaker signed inequality passed. Thus the final comparable-event bound has no nonzero comparable incidences in these diagnostic cases, and the earlier variant exercises the underlying sign mechanism but not the final larger J nonzero case. No oversize window trigger appeared in either final diagnostic; that implication is proved in section3 and checked conditionally in code. These finite proportions are not asymptotic bounds. The much larger actual analytic T is not used for these diagnostics, so the finite stopped mass is not an estimate for the no-twin window. No Lean compilation.

## 6. Next target

The rough-anchor arrival cap supplies an arbitrary-depth cost deletion, including giant jumps and bounded subsequent travel, without three-prime modulus loss. The signed budget reduces all remaining comparable-label costs to a vanishing fraction of the small-relative plus marked costs. Further work must estimate long high-state stretches with labels small relative to the current height (p<h/D), and bound the mass at the enlarged low/anchor stop set, preferably jointly. A possible use of the former is to partition by height scale and exploit low-prime barriers without counting large downward jumps as independent cost. This is a concrete residual, not an asserted tail bound. No main edit, no new branch, no twin-prime proof.
