# Exact inverse clock reachability and negative-deficit cutsets

2026-11-25 JST. Continues 4532c6572778fe3e53e60ce88ecfd81e39fe4638 (local nonreset repeat counterexample and canonical scan) and 842e743d7219abf6ad143288fe22ea3f321f36e4 (upward cutsets). New: exact one-tick inverse rule including waiting states, a finite complete obstruction to canonical ancestry of the synthetic repeat, periodic families of such unreachable histories, and band-adaptive downward crossing support and monotone peeling. No general repeat exclusion or energy upper bound.

## 1. Exact one-tick inverse rule

Fix the same odd-prime cap B and deterministic MIN rule. State (t,C) means the state AFTER tick t, including stationary waiting ticks. In the forward rule from (t-1,D), let s=t mod2 and p be the least prime factor of gcd(t-2s,D+2s-1) if at most B, or 0 if none. Since D even this gcd is odd. The output horizon is D if p=0 and D+p-1 otherwise. Within the original prefix gate this is exactly the event rule. Canonical root m odd has (t,C)=(m+2,2m-2). For reachability from such roots all states satisfy C<=2t; a terminal twin stops the actual prefix. The unrestricted tick rule may be regarded as making that terminal stationary, but we never infer actual occupation after terminal or cutoff.

For target (t,J), inverse predecessors (t-1,D) are EXACTLY:
- stationary D=J if the tick at (t,J) selects no prime;
- jumping D=J-p+1 for each odd prime p<=B dividing gcd(t-2s,J+2s), provided the MIN test at (t,D) selects precisely p;
- in either case retain only D even, D>=2, D<=2(t-1), when searching ancestors of canonical roots.

Necessity follows by substituting J=D+p-1 in the forward condition. Sufficiency is the direct forward test. No choice of previous selected-event time is needed. Tick decisions at a fixed deficit d=2t-D depend only on the divisors of d+1 (even s=0) or d-5 (odd s=1), since the gcd is gcd(t,d+1) or gcd(t-2,d-5) up to sign. Jump candidate divisors at the target are factors of 2t-J-6s. Thus bounded-deficit inverse certificates can be expressed by finite congruence conditions on t, even at arbitrarily large horizons.

For original roots in [X,2X), H=4B, a target clock t0 and horizon C0, restrict reverse times to >=max(X+1,t0-H-2)+2 and horizons to >=2max(X+1,t0-H-2)-2. Report canonical roots m in [X,2X), m odd, t0-(m+2)<=H. Monotonicity makes this restriction complete. For a nonterminal target under the gate it is exactly the original roots reaching that state in their actual short prefixes; a twin encountered at a smaller horizon cannot reach the target. At the particular targets below, which all have r>0, independent forward unit-tick scans agree exactly. State count in reverse is a count of clock states, not canonical roots or selected events.

## 2. Synthetic repeat is globally unreachable from a canonical root

B=678. Start from target post-state (97712,195362) of the selected31 event in the previous synthetic example. Reverse entire tree without time or horizon window truncation, apart from D>=2 and nonnegative deficit. The complete levels are:

t=97712: J=195362.
t=97711: J=195362,195332.
t=97710: J=195362,195332.
t=97709: J=195362,195332.
t=97708: empty.

Seven states, six edges, none canonical. At both last states the stationary edge is blocked by selected3 and no jump candidate survives the MIN test. This is a complete nonreachability certificate, not a bounded nearby-root scan. It also excludes the synthetic pre-state (97711,195332), one of the seven. Independent direct enumeration of ALL even D with J-B+1<=D<=J confirms all predecessor lists at those seven states. In contrast the later state (97764,195498), d=30, before the selected137 repeat, has 57 genuine original ancestors in X65536,H2712. The final (97957,195634) has the same 57 ancestors. Their reverse searches visit 11728 and12420 clock states respectively, max width48. All these roots independently replay to the target by original forward rule. Consequently the low-deficit state itself is reachable, but NONE of its canonical histories can pass through the dead selected31 state. The all-threshold repeated-launch absence in the original canonical scan is not contradicted by this example, and not proved in general. The known canonical state (88113,176186) has 13 roots, including 88031; independent reverse/forward agreement.

## 3. Infinite periodic families of dead histories

Let L be the product of all primes <=500 (including 2). Shift t to t+hL and C to C+2hL for any nonnegative integer h. This preserves deficit and parity. All prime divisors needed for each of the seven reverse-state tests are <=500: nonzero target deficit minus 6s has absolute value <=90, and MIN tests at candidate predecessor horizons have absolute gcd bounds <=180+1, by section 1. In the complete 26-event synthetic trajectory, each tested forward tick has instantaneous deficit at most416 (last pre-event tick), hence all prime divisors of the fixed deficit expressions have size <=500. These are elementary finite bounds, independent of the size of the translated clocks. Divisibility by all these primes is unchanged by the shift; so the exact seven-state tree and all 26 forward events persist for every cap B>=500. The dead tree remains free of canonical states. This proves infinitely many local repeated-launch examples at P31 whose given first large-event state has no canonical ancestry. It is a periodic obstruction, not a positive-density claim for canonical repeated launches. One may choose the usual growing B in translated dyadic windows once B>=500. Audit uses BigInt at shifts h=1,2,17 and B=500,10000,1000000 (207-digit period); normalized reverse tree and forward word equal original at all three shifts.

## 4. Downward crossings: two independent arithmetic supports

Original all-odd prefixes as in previous notes: dyadic X,N=X/2,B=ceil(sqrt(7X)),H=4B,late slab [2B,4B),G=2H+B+6, u=log B, ell=1+log u. All recorded horizons in [2X,7X), deficit <=12B+6, total selected gain<=G, actual selected wait w<=2r(C)<=2p. Reset means actual post-deficit 6s, not a virtual canonical point. Define P=ceil(B/u^1/8), Q=ceil(B/u^1/4), Y=max(17,ceil(B^1/8)), eps=u^-1/8. For sufficiently large B, Y<Q<P.

A nonreset event p whose deficit falls from d to d' crosses integer level lambda downwards when d'<lambda<=d. p=3 cannot decrease, so p>=5. Then d'=6s+2pk>=2p, and d-d'<=p-3, giving
    lambda-p+3 <= d' <= lambda-1,  p<lambda/2.
For fixed p,s,lambda there are O(1) possible phase k (indeed at most one in the interval), and p|J+2s. Thus O(X/p) labeled physical post keys per p at that level, without restricting pre-times. Partition events with p<P into:
  near: Q<=p<P, ANY actual wait;
  rough: Y<=p<Q and actual w>=eps*p;
  other: p<Y, or Y<=p<Q and w<eps*p.
The near band has candidate support per level O(X ell/u) by prime reciprocal bound on [Q,P). It pays no roughness factor, so includes short-wait downward events. For rough class, r(C)>=eps*p/2, implies the two quotient forms in C+-1=pj,pj+-2 are free of odd prime factors <=B^1/64 eventually. Uniform two-form Selberg bound from earlier notes gives O(X/(p u²)) possible C per p/sign; phase constraint at a level is O(1). Summing reciprocals on [Y,Q) gives O(X/u²) rough candidate post keys per level. These envelopes count labeled POST states, not distinct pre-times or tags. They are uniform across all relevant levels, and so total key-level support satisfies
    S_near=O(XB ell/u),    S_rough=O(XB/u²).          (1)
The raw phase envelope can be streamed by adding +1,-1 to difference arrays for levels [d'+1,d'+p-3]; no storage of all potential keys required.

## 5. Actual descending cutsets and monotone removal

Each time an original tag selects p>=P and enters a nonreset state, begin an excursion at its post-state with deficit d0>=2P. End it before the next selected p>=P or actual reset (or original prefix termination). If its deficit ever falls by D=ceil(P/4) before that end, take the first such recorded post-state and assign, for each integer lambda in [d0-D+1,d0], the LAST downward crossing of that level before or at that state. Existence by the deficit endpoints. Every assigned event is nonreset and selected p<P; different excursions along one root are disjoint. A repeat from prior high nonreset to new high nonreset with predeficit<=P must contain such a drop (the immediately previous high event is nonreset and no intervening reset). No assumption about repeat existence needed. This broad drop class also includes many actual partial descents which are not repeats.

Group assigned roots in near/rough classes by (J,v,p,lambda). Each root appears at most once per key-level, since horizons strictly increase and excursions are disjoint. Other assignments split into small and short-wait classes. Their total assigned level count is <= corresponding actual full selected gain, by d-d'<=p-3; short-wait half-clock is <=O(eps) times selected gain. This does NOT make short-wait gain small; it can account for much of the descent.

Set h_near=floor(u^1/2), h_rough=floor(u^3/2). For an arbitrary retained original family, iteratively remove a root if any of its assigned excursions has >=D/3 levels in CURRENT thin near/rough groups (mass<=their band threshold). Charge just those witnesses of one triggering excursion. At first charge a group has <=h active tags, and the counts only decrease, so lifetime charges<=h per group. Therefore
    #deleted <=3(h_near*S_near+h_rough*S_rough)/D
             =O(X ell/u^3/8)=o(X).                  (2)
Original late linear clock loss<=B per removed root, hence o(XB). At the fixed point every remaining drop has either >=D/3 other witnesses (small or short-wait), or >D/3 actual retained thick near/rough witnesses. This holds with recomputation of counts and even if some earlier roots have already been removed. Thick witnesses at different levels need not be different physical states. This is a genuine root-pruning result but not a bound on all drop or repeat energy. No prevalence of covered class inferred from finite diagnostics. Root deletions preserve LOW destination accounting; arbitrary event-only masks still need previous transfer conditions.

## 6. Actual upstream energy for rough descending groups

Let E_down,rough^full be the projected quadratic energy of all full unclipped waits of actual nonreset negative-drift events Y<=p<Q,w>=eps*p (including crossing event at prefix end), with their actual weight w/(2r(C)). This is NOT the late-slab energy. At each fixed predecessor horizon C the number n_C of such tags is <=2U(C)/eps, since r<=p. Each event covers <=p-3<=2r/eps levels. Distinct labeled post keys partition the actual tags at C. If n_{alpha,lambda} counts assigned witnesses, and n_alpha all actual rough tags at that key, then sum_lambda n_{alpha,lambda}² <= n_alpha * sum_lambda n_{alpha,lambda} <=(2r/eps)n_alpha². Thus
    sum_{rough alpha,lambda} n_{alpha,lambda}² <=8 eps^-3 E_down,rough^full.
By Cauchy and (1), total assigned rough level count is <= sqrt(8 eps^-3 S_rough E_down,rough^full).
No analogous bound for near keys with arbitrary short wait is asserted. This supplies an actual earlier energy lower bound if many rough descending witnesses occur, not the desired late upper bound; no conclusion about final quadratic energy of thick groups without another estimate.

## 7. Verification

Standalone research/min_clock_negative_cutset_audit.mjs, exact readback f8c65d79b7296b51df7ff298959e89aa52f731d3 (initial full 12-run audit), updated dce07d9292f71d6fc302c1063e5d4996e19b15e3 blob fc269a944870a4d9ca1c334786039d121030609c (adds BigInt translation test, successfully executed). Run node research/min_clock_negative_cutset_audit.mjs 1024 4096 16384 65536. Four X windows x three modes executed in available JS runtime. All original MIN paths, literal parity-GCD comparison at X1024, actual last downcrossing per level and independent lastness check, arithmetic support, rough second moment, thin/thick and lifetime pruning. Independent inverse direct scan of all even predecessor horizons initially had a parity bug in the lower endpoint, corrected and rerun; inverse/forward root list matches for all three reachable targets. No global nonreachability claim based merely on failed nearby-root scans. Exact remote readback confirmed both audit versions. All finite diagnostics natural original prefixes, no previous masks, no cumulative energy reduction.

Largest X65536,B678,N32768,794415 selected events. Analytic P537,Q425,D135,319 high nonreset blocks,91 drops,12285 levels:364 small,11921 short,0 near/rough (finite eps .791). No repeat, no thin removal. Diagnostic P85,Q43,D22,eps1/8, thresholds2/4: 29758 high nonreset blocks,3133 drops,68926 levels (1632 small,15016 short,42780 near,9498 rough). Initial thin170,thick52108. Nine roots peeled,3124 drops remain:809 other-dominant,2315 thick; min thick level fraction .72727. Near/rough used1572/284 groups, max mass215/119, second moments3394896/640262, rough full energy1311942.21. Wide P43,Q22,D11: 53950 blocks,4952 drops,54472 levels (5934 small,8846 short,38099 near,1593 rough),38 roots peeled,4903 drops remain (1524 other,3379 thick), max group176/42. Finite thresholds do not demonstrate the asymptotic regime or solve the remaining short-wait gain. No repeat in any mode, so the implication from repeat to drop is mathematical and not positively exercised. Prior exact original all-threshold scan to X2^20 remains unchanged.

## 8. Remaining

Local repeated-launch examples are demonstrably unrepresentative of canonical histories; the exact inverse rule can seek a reachable counterexample or certify other dead states. Large descending excursions can be localized to thick actual earlier groups or small/short-wait descent, but neither gives the entire required energy estimate. Need control of arbitrary short-wait negative drift histories and thick group formation/late persistence. No bound on general canonical repeat, no Lean compile, main unchanged, twin-prime conjecture OPEN.
