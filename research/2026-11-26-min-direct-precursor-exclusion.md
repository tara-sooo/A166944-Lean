# Short-run precursor exclusion and an inverse-linear weighted A1 tail bound

Continuation of [4777ea7](https://github.com/tara-sooo/A166944-Lean/commit/4777ea7b8210741af70ef1b862c6fb4c32bbdba7). The preceding tail bound balanced the total capacity of long low-label runs against the count of sufficiently large preceding A1 events. Restricting the recovery allocation to its lower levels gives a stronger property: a short low-label run immediately following ANY A1 cannot pay these levels, even when the preceding A1 differs from the mark whose recovery is being tracked. A near nonreset precursor is likewise excluded. This removes the balancing term and improves the weighted tail from square-root to inverse-linear decay. No twin-prime contradiction or Lean kernel verification.

## 1. Model and lower recovery intervals

Use adaptive MIN with even horizon H, event label p, waiting time w, gain g=p-1, ordinary deficit d=2t-H and adjusted deficit D=d'-6I (side I=0 even/1 odd). Put x=d+3, x'=d'+3. The ordinary update is d'=d+2w-g, so every event can decrease x by at most g (indeed g-2). For p>=5, D is a nonnegative multiple of 2p; a nonreset has x'>=2p+3. Label3 never decreases d.

A1: p>=47, p>=5d+15, D=2p; A0: same low-deficit test, D=0. At p>=47 the remaining events are B. Near/far use the fixed square-band classes of 8b30078. Consider a finite contiguous canonical event block with pre-horizons H>=4097, gain G, all labels<=C, and N actual canonical visits in its tick interval (start,end]. Let R>=47, T>=48. Mark all A1 p>R and p>=T, with weight W_T equal to the sum of their labels, counting occurrences. Empty marked sets cause no difficulty.

Every mark p has pre x<=p/5, post x'>2p. Allocate all real levels
    y in (p/5,p]                                              (1)
to their first subsequent downward crossing (x'<y<=x), or leave them pending if no such crossing occurs in the block. This lower interval has length 4p/5. At each fixed level a new marked crossing cannot occur until the preceding assignment at that level has been paid; thus the pending intervals at any instant have disjoint interiors. One can maintain finitely many half-open intervals with the ordinary remove-on-downcross update. At an event the allocated length across all marks is at most its actual ordinary decrease; total pending length at the endpoint is <=2C (even C suffices for (1)). A pending level is at most the current plateau x before its first downward crossing.

By the near-label geometry of 850c00f, for any near event of label s at or after a mark p, s>=(1-eta)p, where eta=2/floor((A-1)^(1/4))<=1/4 if all pre-horizons are >=A>=4097. For the mark itself this lower bound is immediate. Hence a later near nonreset has post x'>=2s+3>=3p/2+3 and cannot itself pay any level in (1). All nonreset payments are far.

## 2. New precursor exclusion theorem

A low run is a maximal contiguous sequence of events in the block with labels <=R, allowing endpoints cut off by the block. Let its total horizon gain be L, its initial x be x0. Every subsequent plateau in this run has x>=x0-L, by summing the ordinary decrease bound (increases do not invalidate this inequality). Suppose a nonreset event in this run pays a level y belonging to mark p, so p/5<y<=p and the event's post x'<y. Necessarily L>x0-y.

The initial low run of the block cannot pay any marked level, because all marks are high labels p>R and assignments only go forward. For any other paying low run its immediate preceding high event occurs at or after the mark whose level it pays: the mark is not inside the low run. There are three relevant precursor types.

1. Preceding high event is A1, with label q. If it is the mark itself then x0=2p+6I+3>2p>=2y. If it is a later A1, y is still pending in its pre-state, hence y<=x_pre<=q/5. Consequently q>=5y and x0=2q+6I+3>=10y+3. In either case x0>=2y, so
       L>y>p/5.                                             (2)
   This pending-level argument is the key new observation: the preceding A1 need not be the mark p, and there is no need to count preceding A1 by a lower bound on q or to solve a recursive tail inequality.

2. Preceding high event is a near nonreset (whether A1 or B). By the geometry above, x0>=3p/2+3, so
       L>p/2.                                               (3)
   The inequality uses y<=p. No assumption on the preceding near event's multiplier h is needed.

3. Remaining possibilities are a high reset or a far high nonreset B. The latter classification follows because high labels exceed R>=47, and the A1 and reset types have already been accounted for.

Thus every low run paying a nonreset part of (1) is either preceded by a reset or far high nonreset B, or has gain >p/5 for EACH mark p whose level it pays. This is a per-run supply restriction, not a restriction just on the first recovery after a mark. It allows arbitrary intervening high events and arbitrarily repeated visits to the same deficit level.

Fix integer 1<=l<=P_R with 4l<=T/5. Call runs long if L>=4l, otherwise short. Since p>=T, (2)-(3) exclude every A1 and every near nonreset as a precursor of any short paying run. The number of short paying runs is at most N+1+B_R, where B_R counts all far B events with p>R: each run has a distinct preceding event; each high reset has label>=7 and the earlier normalization supplies a distinct canonical visit except one possibly pending at the endpoint. It is also valid to count only far high nonreset B here and below. Each short run pays at most its actual total downward length, at most its gain <4l. Therefore
    total short low-run nonreset payments <=4l(N+B_R+1).       (4)
The same canonical reentry may be charged again for a direct reset payment below; the explicit coefficient C+4l accounts for this and no disjointness is assumed between those two charges.

## 3. Finite inverse-linear tail inequality

Use the horizon CRT barriers with period P=P_R in the integer coordinate H/2 and the mean-square parameter V=V_R from 78b1212. Put n=G/2. Recall the long-run bound of 4777ea7:
    G_long <=16(n+P)V/l,                                    (5)
where G_long is the total horizon gain of all low runs with L>=4l. Proof: each such run's index interval has length >=2l and no horizon barrier, so at least half its starting positions have moving average f_l=0; these positions are disjoint between low runs. The periodic zero proportion is <=mean (f_l-1)^2<=4V/l. Multiplication by the two coordinate-conversion factors gives (5). If l=P, every low run has integer length <P because the period contains a barrier, and G_long=0.

The first-downcross allocation of (1) has total demand (4/5)W_T. Direct decreasing reset payments are <=C(N+1); high nonreset payments are all far B and <=C B_R. Long low-run nonreset payments are <=G_long, short ones are bounded by (4), pending <=2C. Consequently the exact finite inequality is
    (4/5)W_T <= G_long+(C+4l)(N+B_R+1)+2C.                  (6)
In contrast to the former tail inequality, there is no l*G/T term from preceding A1 and no l*n_near term from preceding near nonresets. There is no sparsity assumption in (6).

For T<=C choose
    l=min(P_R, floor(T/24)).
For T>=48 this is a positive integer, 4l<=T/6<T/5. If l=P_R, G_long=0; otherwise l>=T/48 and (5) gives G_long<=768(n+P_R)V_R/T. In either case C+4l<=7C/6. We obtain the explicit finite bound
    W_T <=960(n+P_R)V_R/T
            +(5/4)*[(7/6)*C*(N+B_R+1)+2C].                 (7)
If T>C then W_T=0. All constants are universal for the stated near definition and pre-horizon lower bound. This finite estimate is valid even when the full primorial is smaller than the desired smoothing scale.

## 4. Macroscopic tail, occurrence distribution, and moments

Take crossed [X,lambda X], lambda>1 fixed, on an infinite canonical ray. Choose any enlarged cutoff of 78b1212, largest odd prime R with
    P_R exp(-gamma*pi(R))<=sqrt X,
    0<=gamma<2 log(pi/2).
Then P_R=o(X), R=Theta(log X), V_R log^a X=o(sqrt X) for every fixed a>0. G=O_lambda(X), C=O_lambda(sqrt X). Equation (7) proves, uniformly for 48<=T<=C,
    W_T = O_lambda(X V_R/T + sqrt X*(N+B_R+1)).             (8)
This improves 4777ea7's O(X sqrt(V_R/T)+sqrt X*(N+B_R+1)) in its nontrivial tail range T/V_R->infinity. The earlier sqrt balancing is no longer needed; the new upper bound applies even for T of order C and at all enlarged cutoffs. If R>=T, W_T simply denotes all marked A1 p>R, and the bound is still valid but may be weak.

In the sparse branch N,B_R=o(sqrt X), for every fixed K>=1 (once K V_R>=48), the weighted tail at T=K V_R is O_lambda(X/K)+o(X), with implied constant independent of K. The occurrence tail M_T satisfies M_T<=W_T/T, hence
    M_T=O_lambda(X V_R/T^2 + sqrt X*(N+B_R+1)/T).          (9)
Since the prior mean-square joint theorem gives m_f=Omega(X/V_R) far marks under these sparsity assumptions, the fraction of far marks above K V_R is <=O_lambda(K^(-2))+o(1) for fixed K (and the corresponding bound with o(1)/K for growing K). These are distribution bounds on actual occurrences and label weight on a single ray; not an assertion of a limiting distribution or a lower bound on the total mark weight.

For a more quantitative weighted statement define M_a=sum_{A1,p>R} p^(1+a) (all marks, with multiplicity). Write L_exc=C(N+B_R+1)+2C. The exact layer-cake identity is
    M_a=a integral_0^C T^(a-1) W_T dT,                    (10)
for a>0, because each mark contributes p*integral_0^p a T^(a-1)dT=p^(1+a). Use W_T<=47G/46 always (each mark label>=47 and gain p-1) for T below V_R, and (8) above V_R (eventually V_R>=48, V_R<C; if V_R>=C the trivial bound is enough). This gives, for fixed 0<a<1,
    M_a=O_(lambda,a)(X V_R^a + C^(1+a)*(N+B_R+1)).
At a=1 it gives
    sum_{A1,p>R} p^2
       =O_lambda(X V_R*(1+log^+(C/V_R))
                     +C^2*(N+B_R+1)).                   (11)
The reset/high-B error is retained, even in sparse windows, because it need not be negligible relative to the new smaller main scale. These are moment bounds for the same marked population; no assumption of independent deficit or horizon residues is introduced.

## 5. Diagnostics and limitations

[Audit 0722005](https://github.com/tara-sooo/A166944-Lean/blob/072200541ad72f493c1846990c70d33b35302402/research/min_direct_precursor_exclusion_audit.mjs), blob 3fb2eeec799e5505495a7dd90e17c145889c68c9. Exact remote readback. Run node research/min_direct_precursor_exclusion_audit.mjs 120000 180. Actual ECMAScript function executed in tool runtime, not a separate Node process.

59,998 odd canonical roots through 120,000, 1,265,607 actual MIN events, 12,529 A1, 59,989 stopped within the cap and 9 unresolved at 180 events. 726,455 full/suffix block-cutoff incidences, 223,928 marked blocks, 225,555 mark incidences, 3,288,645 allocation checks, 9,427 positive payment checks, 3,489,890 low-run capacity checks, 2,768,449 exact small-period horizon barrier checks, 223,928 finite tail inequalities and 151,320 closed-form inequalities. Diagnostic R7/11/13/17/47/71, T48/96/151/251/401; the small R values test geometric bounds counting all other far high nonresets as exceptions instead of imposing the p>=47 classification. The audit includes 19,520 arithmetic controls for the precursor exclusion inequalities. No actual paying near-precursor sample was observed; that part of the theorem follows from the proved geometry, not empirical validation of such a sample.

Constructed NEW actual canonical CRT root with 12,979 decimal digits, first event word 10039/6709/4513/7. The first three are even events with adjusted deficits 2p, the last is an odd label7 event at wait1. Post ordinary deficits 20078/13418/9026/9022. 15,140 literal BigInt GCD ticks, 13,028 stage/residue checks, adaptive eligibility verified. The CRT avoids other neighboring small factors at the first three stages, ensures the winning labels, and excludes competitors for the final tick. For T10000 and R7/11/13/17 the last event pays four units of the lower interval of mark10039, in a short low run preceded by far B4513. For R7000, all three recovery events are in a single long low run immediately following A1, gain11226, with 1014 units of the lower interval paid and 7017.2 pending. The R7000 witness checks the exact finite inequality using observed long-run gain, not enumeration of its enormous primorial. Five witness controls with translated conservative lower horizons and preserved small-period residues; four short paid B runs, one long paid run, two prior-A1 payment checks. All assertions passed. Allocation uses exact fifth-unit integers; V_R formula evaluated with floating-point tolerance. The arithmetic controls are not simulated MIN trajectories. No observed macroscopic infinite-ray crossing, external novelty claim, Lean kernel verification, or proof of twin infinitude. Main and sibling branches unchanged.

Next: use the necessary length L>p/5 for low-run recovery following A1 to study how much of the long low-run gain can actually be devoted to deficit decrease rather than intervening increases, or combine the scale-resolved count with a sharper gap distribution for horizon barriers. The inverse-linear bound is still compatible with a substantial supply of low-run recoveries at p=O(V_R), and neither sparsity hypothesis follows from finite twins. No stopping invariant has been established.
