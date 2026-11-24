# First physical saturation: short-clock large-parent collisions and a stronger shallow-ancestry bound

2026-11-24 JST. Continues 53b71dc6c8a39f884f11ffa6c3ffabb1a3c44fb6 on the SAME research/min-cycle-forest-2026-11-24 branch. New paper deductions and exact finite audit, no Lean compilation. The aggregate deep-ancestry estimate and twin-prime infinitude remain open.

## 1. Shallow ancestry: geometry beats the reverse branching bound

Retain canonical MIN, original odd M in [X,2X), dyadic X divisible by four, N=X/2, B=ceil(sqrt(7X)), t0=M+2, C0=2M-2, K(M)=floor((7M-1)/4). Use the preceding note's first-heavy selected-key absorbing process (fixed LOW7 L=210, cap tau=ceil(B log^2 B), stop before executing the high event).

At a stopped key (p,C), any root with at most h executed high events has total gain at most h(B-1)+(h+1)L, by the LOW-only barrier, regardless of repeat labels or physical merging. Its initial horizon lies in [C-h(B-1)-(h+1)L,C]. The initial horizons are spaced by 4. Thus the number of distinct such roots at ONE key is at most
    U_h <= 1+floor((h(B-1)+(h+1)L)/4).
As the number of stopped keys is <=N/tau, the number of shallow stopped roots is <= (N/tau) U_h. For any fixed 0<epsilon<2 take h=floor(log^(2-epsilon) B). This is O(N/log^epsilon B)=o(N). The same bound divided by the total stopped mass follows directly since every stopped key has mass >=tau. If the cap is B log^(3-epsilon0) B, the depth exponent can be increased to 3-epsilon0-epsilon for epsilon>0 with positive exponent. This improves the log B/log log B reverse-factor bound in the parent note. No chronology or independence is needed for this part; it is a geometry bound on distinct roots, not on reverse path count.

## 2. Two exact intermediate groupings, with original source mass

Consider ANY absorbed canonical MIN process which stops all tags at some selected keys (p,C) before executing their next event, including the previous process. It must preserve original cutoff tags and never reinsert stopped roots. Process C in increasing order. At each horizon C distinguish:
    V(t,C): all active original tags arriving at the physical state (t,C), including canonical roots injected there and tags which will terminate there.
    A(n,p,C): all active tags at C whose actual next MIN event is at time n with selected prime p (within each tag's cutoff).
Compute A even when the event will not be executed because its selected key stops. V groups are disjoint at a fixed C. A groups partition the tags with an actual next event. If A is executed, all its tags arrive together at V(n,C+p-1); different selected labels reaching that V and a possible injected root form disjoint incoming classes. At a given V, the incoming class of a label q is uniquely the earlier A(t,q,C-q+1) (if executed); it cannot split by predecessor horizon. These are exact partitions; different arrival times may share the same A.

Fix integer kappa>=2. Mark a tag at the FIRST group of size >=kappa which it encounters, scanning V then A at each C. The tag is marked only once, even if group masses later decrease because of original cutoffs. This is a diagnostic marking, NOT a second stopping/deletion process; the underlying absorbed paths do not change. At a first A mark, the tag's own predecessor physical group V has mass <kappa (otherwise it would already have been marked). At a first V mark, its incoming clock class has mass <kappa, or it is a newly injected root. Therefore a fixed parent V of an A can contribute at most kappa-1 newly marked tags; a fixed incoming A class of a V can do likewise. This is how candidate-state counts can legitimately yield original-source counts, unlike multiplying by unrestricted full fibre mass.

For an arrival state V(t,C) produced by prime q, the exact previous-event congruences give
    even t: q|C, t=0 mod 2q;
    odd t: q|(C+2), t=q+2 mod 2q.
At a fixed C, a single q can occur on only one side (q odd); its arrival times form a progression with spacing 2q. A canonical root at C, if any, has t=(C+6)/2 odd. A clock class A(n,p,C) has all its predecessor times in the interval of length <=2r(C) ending just before n, by the exact reverse clock interval. Thus any two of its distinct parent times differ by <2r(C).

## 3. NEW unconditional source bound on four rare first-saturation types

Put Q=ceil(B/log^alpha B), z=ceil(log^beta B), kappa=ceil(log^delta B), with positive fixed exponents and sufficiently large B. A top arrival means it has a witness tag produced by a prime q>=Q. A root arrival has a witness canonical root. Witnesses may have been previously marked; the tag counted below is always newly marked. Assume Q>2z+6 and Q^3>7X+2, which eventually hold.

(A1) Short-clock top-top: a first mark at A(n,p,C) with r(C)<=z, at a parent time having a top witness, where another DISTINCT parent time has a top witness. The two witness labels must be distinct, since a fixed q's time progression has spacing 2q>2z. The tag itself need not have arrived via a top label; count every newly marked tag at a qualifying parent time.

Count all possible pairs of arrival states with common C and times u,v=u+d in the O(X) time interval, 0<|d|<2z. For fixed distinct q,q'>=Q, parity sides, and d, the two congruences on C give one CRT class mod qq'; the two time congruences give at most one class mod 2qq'. Each coordinate has O(1+X/(qq')) possibilities. As qq'<=B^2=O(X), this is O(X/(qq')) per coordinate. The number of candidate parent-state pairs is therefore
    P_A1 = O(z X^2 (sum_{q>=Q} 1/q^2)^2)
         = O(z X/log^(2-2alpha) B).
Here and below prime sums are over primes <=B; use the standard prime counting upper bound and partial summation, sum_{q>=Q}1/q^2=O(1/(Q log Q)). In a deterministic MIN path, a given pair of parent states can be in at most one common clock class at that C (the next event is unique, independent of source cutoff if it exists). Each parent contributing newly marked tags contributes <kappa such tags. Charging each newly marked parent to at least one witness pair bounds the total A1 tags by 2(kappa-1) P_A1. Multiple candidate witnesses only overcount.

(A2) Short-clock root-top: a first mark at A with r(C)<=z, at one of a pair of distinct parent times, one having the canonical root witness, the other a top witness. If root time is t0=(C+6)/2 and top arrival time u, then |u-t0|<2z and nonnegative post-height 2u-C<6+4z. The top label q divides the height on even u or height minus 6 on odd u, in fact 2q divides it. By Q>2z+6, the only possibilities are even reset height 0 or odd reset height 6. The latter has u=t0 and is excluded. Thus u=t0-3 and q|C. Counting possible C for each q gives
    P_A2 = O(X sum_{q>=Q}1/q)
         = O(X (1+log(B/Q))/log Q)
         = O(X log log B/log B).
Again the number of newly marked tags at the qualifying parent times is <=2(kappa-1) P_A2. Root presence is a witness; no assumption on the entire parent fibre size is made except the first-mark rule.

(V1) Different top incoming classes: a first mark at V(t,C) with at least two distinct incoming labels >=Q, for a tag belonging to a top incoming class. (Other small incoming classes may exist; their tags are not included in V1.) The two labels divide both the same parity-corrected t and C coordinates. For each pair the CRT count is O((1+X/(qq'))^2), so candidate vertices number O(X/log^(2-2alpha) B). There can be at most two distinct top incoming labels at one vertex because Q^3>7X+2. Each top incoming A class of a newly marked tag has <kappa tags. The total V1 tags are O(kappa X/log^(2-2alpha) B).

(V2) Root plus top incoming class: a first mark at V where a canonical root is injected and a top incoming class exists, counting only the root and tags in top incoming classes. Then t=(C+6)/2 and q|C+2. There are O(X sum_{q>=Q}1/q) possible vertices; at most two top incoming classes per vertex. Each class of newly marked tags has <kappa tags. The total V2 tags are O(kappa X log log B/log B).

Take alpha=beta=delta=1/4. Then all four types combined contribute
    O(X/log B + X log log B/log^(3/4) B)=o(X).
Overlap can be removed by priority A1 over A2, V1 over V2. This is a genuine unconditional upper bound on original tags at their FIRST saturation, not just a count of candidate vertices or of representative demotions. It works for arbitrary prior depths, arbitrary previous saturation of other tags and any absorbed process preserving the actual dynamics. It does NOT bound all tags visiting those vertices later, nor all newly marked tags at a vertex with a small incoming class. For A1/A2 short means small minimum eligible factor, not merely a short observed wait of the counted tag; the bound on all arrival time differences needs the exact common reverse interval.

The remaining first-mark types are clock saturation at r(C)>z, short-clock saturation at parents without the stated top/top or root/top witness pair, and vertex saturation in the other incoming classes (in particular small/mixed classes). For example if all parent times of a short clock class have top witnesses and at least two are distinct, all newly marked tags there are covered by A1. A single parent time cannot generate a first mark at A, because its V mass would already be >=kappa.

## 4. How this relates to projected selected-key stops; variable capacity extension

At a stopped key (p,C), tags which are STILL unmarked after examining the final proposed A groups belong only to A groups of mass <kappa. The number of possible n in the whole time interval for this p at C is O(1+X/p)=O(X/p). Hence there are O(kappa X/p) such tags per stopped key. Under the previous uniform cap tau=B log^2 B, for p>=Q their total over all stopped keys is
    <= O((N/tau) kappa X/Q)
    = O(X log^(alpha+delta-2) B).
For alpha=delta=1/4 this is O(X/log^(3/2) B). Combining section 3, all but o(X) of the tags stopped at top keys must have a first saturation of one of the REMAINING types, at any preceding point or final proposed clock group. This does not bound the total mass of stops at smaller p.

A useful extension to much smaller stop labels: choose any Y=Y(B) tending to infinity with 11<=Y<=B, set kappa=ceil(sqrt(log Y)), and stop at ALL selected keys, including low primes, with capacity
    tau_p = ceil(B log^2 B), p<Y,
    tau_p = max(ceil(B log^2 B), ceil(X log Y/p)), p>=Y.
There is no LOW grouping in the cost estimate here. By the improved uniform per-prime arithmetic bound S_p=O(X/log^2 p) in the parent note,
    R_pre <= sum_p (tau_p-1) S_p
          = O(X^2/log B + X^2/log Y)=o(X^2),
because sum_{p>=Y}1/(p log^2 p)=O(1/log^2 Y). Thus absence of all twin terminals would again imply N-o(X) stopped roots. For any stopped p>=Y, unmarked mass divided by total mass is O(kappa/log Y)=O(1/sqrt(log Y)), so over all such stops the unmarked tags are o(X). In particular take Y=ceil(log B), which makes the first-saturation reduction apply down to logarithmic selected labels, not only near B. The kappa here is <=O(log^(1/4) B), so the rare-type bounds of section 3 with Q=B/log^(1/4) B, z=log^(1/4) B still apply. The two thresholds Y and Q serve different purposes: Y is the cutoff on STOP labels, Q the cutoff on LARGE PARENT labels in the collision bound. This variant permits stops at p<Y as well, and their total mass has not been bounded. It has not been used in the finite audit below. It is a valid alternative cap and partial reduction, not an additional assumption that stops at low labels are negligible.

## 5. Exact finite audit

Executed the JavaScript function body in the current runtime and saved it as a Node.js program with complete JSON output:
    node research/min_first_saturation_merge_audit.mjs 256 1024 4096 16384 65536 262144
Six windows completed. Fixed LOW7, selected-key cap max(2,floor(B/4)) as a deliberately low finite diagnostic (NOT the asymptotic cap). Three modes (kappa,Q,z)=(8,max(11,ceil(sqrt B)),31),(32,same Q,31),(8,max(11,ceil(B/log^(1/4) B)),31). The small-window diagnostics may violate Q>2z+6; the corresponding geometric tests are conditional on the indicated size inequality, and the exact mass ledger always holds. Each mark is permanent, V before A. Incoming class counts are reconstructed from each tag's actual last selected prime (0=root). For A, top/root witness pairs use tags in that exact proposed clock class. Top/root qualifying parent times are identified before counting newly marked tags. The code checks that a newly marked A tag has predecessor V size<kappa, a newly marked V tag has incoming class size<kappa, the exact once-only partition of tags, the local clock interval, absence of same-q close pairs when Q>z, the reset identity when Q>2z+6, and the candidate-count bounds on newly marked tags. For X<=1024, 4663 literal parity-GCD clock decisions match (798+3865). Total R and stopped/terminal counts agree with the earlier first-heavy audit at the same cap.

At X=262144, B=1355, N=131072, cap338, 30 stop keys, 11112 stopped roots, 119960 actual twin terminals, no bad terminal. R_pre=98554147, 3620133 executed events. Largest physical and proposed clock group masses 334 and 357 respectively.

First marks among ALL 131072 roots, mode kappa8,Q37,z31:

| type | all roots | stopped roots | stopped at p>=Q |
|--:|--:|--:|--:|
| never marked |19658|65|24|
| A1 short top pair |757|52|23|
| A2 short root/top |6565|650|366|
| other short clock |39833|4066|1894|
| clock r>31 |37302|3883|1862|
| V1 top pair |1005|94|23|
| V2 root/top |6139|578|260|
| other physical |19813|1724|740|
| total |131072|11112|5192|

The four rare-type finite counts here are NOT in the asymptotic near-top Q regime (Q37 instead of B/log^1/4 B). For mode kappa8,Q827,z31 the all-root rare counts A1/A2/V1/V2 are 0/334/0/199; no stops with p>=827 in this window. In mode kappa32,Q37, the corresponding total stopped roots with no first saturation are 469, among p>=37 stops 141. Full results include observed witness pair/vertex counts and exact bounds. The finite audit tests structure and highlights that other short clocks and long clock groups account for many stopped roots. It does not establish asymptotic dominance of any type.

Script and JSON committed and read back exactly at 1d874e6e528739184954d4fe65c0aa5019f973b5. All files on existing branch; main unchanged.

## 6. Remaining mathematical task

The first-saturation construction handles the original source mass at arbitrary ancestry depth without assuming uniform weights. Four types are now unconditionally negligible, and the variable capacity version forces prior physical/clock saturation for almost all stops with p>=Y. The remaining types, especially short-clock mergers involving smaller previous labels and high-r(C) clock classes, need a bound that holds for the newly marked mass; counting only large-large distinct incoming label vertices misses these. In the next proof attempt, focus on the ratio of previous label to r(C): if two arrivals of the SAME previous q merge in a clock class, then q<r(C) by the spacing condition. For distinct previous labels, exact CRT permits a sum of candidate pairs weighted by the short acceptance interval. Splitting by previous q and r(C), with appropriate caps and using the already proved sieve for rough keys, may allow a quantitative bound on more of the remaining types. No such bound on all remaining types, nor on the stops with p<Y, is proved here. The no-twin contradiction has not been closed.
