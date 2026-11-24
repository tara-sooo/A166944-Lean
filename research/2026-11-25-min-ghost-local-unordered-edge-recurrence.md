# Local recurrence of unordered high transition edges, without discovery locality

2026-11-25 JST. Continues d0540e88f4136aeba9d6bd5d1fc1a2d6478fb17e on the SAME research/min-cycle-forest-2026-11-24 branch. New unconditional weighted bound for a second traversal of the same unordered pair of high labels within a bounded gain span, regardless of their first-discovery times, ranks or first-to-current spans. Both orientations and shared middle events are covered. A pathwise local simple-graph consequence follows. Original paper proof and finite structural diagnostics, no external literature search or Lean compilation. The full signed peak convergence and actual physical far-coalescence upper bound remain open.

## 1. Setting and local edge recurrence

Use the common independent CRT ghost, conditional on the common initial clock parity, with infinite odd-prime alphabet or a finite initial segment. A selected event of odd prime r adds r-1 to the even gain g; its completed preceding wait w<=2r. Through integer time U the exact tick-history law bounds the conditional first-selection hazard of unused r>=z0=ceil(sqrt(2U)) by 2/r^2. All freshness refers to the original trajectory.

Choose HIGH cutoff A>=5 and LOW primorial L=L_A=2 product_(3<=ell<A)ell. Consecutive HIGH events have intervening LOW gain d even, 0<=d<L. Restrict to the prefix whose POST-gain is <=2U, which includes every positive attained peak and its predecessors. Its total selected label weight is <=3U. In the following assume z0>max(7,L+3), which holds for the stated asymptotic parameters.

A qualifying edge is a pair of consecutive HIGH events with both labels >=z0. Its start and end positions are the PRE-gains of those two events. The labels must be distinct: if both were p, the even difference p-1+d would be in [p-1,2p-2) for p>L+3 and could not be 0 or +/-2 modulo p. Identify the unordered edge by its smaller label l and larger label r. The orientation is either l->r or r->l. All intervening events of a different edge pair, including arbitrary smaller HIGH labels and LOW events, are allowed.

For K>=2 define a local recurrence endpoint as the target of a qualifying edge which has an earlier occurrence of the SAME unordered edge such that the span S from that earlier edge's start pre-gain to the later edge's end pre-gain satisfies
    S <= K l.
The preceding occurrence of the same unordered edge, if any, minimizes this span, so it suffices to use that occurrence. Count each qualifying later edge once, with weight equal to its target label (not necessarily r). Denote the total by W_edge(U;K). The later target is necessarily repeated, since both labels were present in the earlier edge. Edges may share a middle event. Neither first-discovery locality nor any bound on the time spent between the two edges is assumed.

## 2. Difference certificate independent of the first gains

For the two edge occurrences write G_r,1,G_r,2 for the two respective pre-gains of r and G_l,1,G_l,2 for l. These are ordered nondecreasingly for each label, with equality possible only when the two edges share that event. The horizon eligibility condition implies
    G_r,2-G_r,1 = m r+a,
    G_l,2-G_l,1 = n l+b,
    a,b in {-2,0,2}.
The even gain makes m,n even. For a shared event use m=0,a=0 or n=0,b=0. For distinct occurrences of a label the pre-gain difference is at least its jump p-1>4, so its coefficient is positive and therefore at least 2. Uniqueness follows from p>4.

Within each edge, G_r-G_l equals l-1+d if the orientation is l->r, and equals -(r-1+d) if r->l. Let d_1,d_2 be the intervening LOW gains. Subtract the two within-edge equations. If both orientations agree, m r-n l=e, where e=d_2-d_1+b-a for l->r or e=d_1-d_2+b-a for r->l. Here m,n>=2, as the same directed edge cannot share an event.
If the orientations are l->r then r->l, we obtain
    (m+1)r-(n-1)l = 2-d_1-d_2+b-a.
Here n>=2 (the two l events are distinct), even when the two r events are the same.
If the orientations are r->l then l->r, we obtain
    (m-1)r-(n+1)l = -2+d_1+d_2+b-a.
Here m>=2, even when the two l events are the same.

In all cases there are POSITIVE integer coefficients j_r,j_l with
    j_r r-j_l l=e, |e|<=2L+6,                         (1)
    j_r<=S/r+2, j_l<=S/l+2.
Indeed each same-label difference is in [0,S], each offset has magnitude <=2, and the coefficient adjustments have magnitude at most 1. The span includes at least one completed gain jump of each of l,r: this is immediate for separate occurrences, and in the shared-event case the two edges form a three-event word with both jumps before the third event. Hence r-1<=S, and r<=K l+1. In particular j_r<=K l/r+2, j_l<=K+2. All actual j_r r and j_l l are O(U), since S<=2U, r,l<=2U+1. The certificate (1) contains NO first gains, discovery times or ranks; it is necessary for the pair of selected labels itself. It is not a claim that every integer solution produces a valid clock trajectory. The argument works for arbitrary events between the two edge occurrences.

## 3. Global edge multiplicity above root

Fix selected distinct labels l,r>=z0, a direction and an even LOW gain d<L. The two pre-gains of an edge must be related by their fixed intervening gain l-1+d or r-1+d. Specify the two actual eligibility signs +/-1. The first pre-gain of the edge is then fixed in one residue class modulo l and one modulo r, using the fixed horizon coordinates. By CRT it lies in one class modulo lr and, because it is even and lr odd, one class modulo 2lr. The interval [0,2U] has length 2U<2lr since lr>=z0^2>=2U. Thus at most one such start pre-gain occurs, and gains strictly increase at events. This holds pathwise for every choice of coordinates, with no independence assumption.

There are two directions, L/2 possible even d and four sign pairs, hence at most 4L actual edges of the given unordered pair in the entire capped prefix. This includes all local recurrence endpoints of that pair, even when their certificates differ. Their total target weight is at most 4L r. This multiplicity bound is independent of K, the time since discovery, and the number of nonqualifying intervening events. It requires the root-scale product inequality; it is not asserted at the lower diagnostic thresholds used below.

## 4. Latest discovery probability bound

Use dyadic bands S0<=l<2S0 and R0<=r<2R0, both based at z0 so R0>=S0. A qualifying witness needs R0<=2K S0+1. At the later of the two original first selections, the earlier label is known and the new one is unused. Assign a certificate ticket only when the candidate is actually selected for the first time at the tick. We count all possible (1) with the appropriate positive coefficients, |e|<=2L+6 and positive targets O(U), including ones unrelated to actual future edges. No conditioning on future edge recurrence is used. A fixed positive integer O(U) has O(1) distinct prime divisors >=z0 by the product bound. The expectation bound for previously selected distinct stock in [B,2B) is O(U/(B log B)) by the conditional first-selection hazard and elementary prime counting.

Larger r discovered later: for each known l enumerate j_l in [1,K+2] and e, O(K(L+1)) choices. Candidate r divides j_l l+e=j_r r>0, with O(1) prime factors >=z0. The quotient determines j_r. Weight each certificate by 2R0 (an upper bound for r), and multiply by fresh hazard <=2/R0^2. Expected ticket weight per tick, after averaging over the stock of l, is
    O(K(L+1) U/(R0 S0 log(2U))).

Smaller l discovered later: for each known r enumerate j_r<=2K S0/R0+2 and e. The band feasibility R0<=2K S0+1 implies the number of coefficient choices is O(K S0/R0) (the additive constant is absorbed). Each positive target j_r r-e=j_l l has O(1) candidate l>=z0 and determines the quotient j_l. Weight by 2R0 and hazard <=2/S0^2. The conditional expected ticket weight per known r is
    O((K S0/R0)(L+1) R0/S0^2)=O(K(L+1)/S0).
Averaging over the known r stock gives the same per-tick bound as in the first case.

Sum over the U ticks. Every unordered pair that has ANY qualifying local recurrence has at least one of these certificates assigned at its later first selection; the actual pair satisfies all restrictions used at assignment. For each such selected pair, all its local recurrence target weights together are <=4L r by section3. Thus pathwise the realized weight in a band rectangle is <=4L times its total assigned certificate weight. There is no need to charge the same discovery repeatedly for each actual witness; this uses the global multiplicity bound. Taking expectations gives
    E W_edge,[R0,S0] <= O(K(L+1)^2 U^2/(R0 S0 log(2U))).       (2)
Summing the geometric series over both bands (dropping the ratio restriction in the final series only, since impossible bands have zero weight), and using z0^2>=2U, proves
    E W_edge(U;K) <= O(K(L+1)^2 U/log(2U)).                   (3)
The bound is uniform for K>=2 and finite initial segment/infinite alphabet; trivial W_edge<=3U remains available. No roughness or record condition is required, and there is no separately imposed upward-ratio cap. The ratio restriction needed for the smaller-latest enumeration follows automatically from the span condition. In particular L<=log^(1/8) U and K=floor(log^(1/2) U) (at least2) give E W_edge/U=O(log^(-1/4) U). This reaches the square-root scale even if both endpoints have long first-to-current spans and are widely separated in discovery time and rank. It is not an estimate for all far-discovery edges, since local recurrence of the unordered pair is required.

## 5. Local simple-graph consequence and signed application

Mark every local recurrence endpoint in the original capped prefix. Consider ANY gain window of width <=K z0, and all qualifying edges entirely contained in that window (both start and end pre-gains inside). If an unordered pair occurs at least twice there, its second and subsequent occurrences are marked, because the span from the earlier start to the later end is <=K z0<=K l. Its immediate preceding occurrence of that pair, if different from the chosen earlier one, has an even smaller span. Thus after removing the marked edges from the list for accounting, the remaining edges are simple as UNORDERED edges within EVERY such gain window, simultaneously. For a window with h distinct labels among qualifying edges, there are at most h(h-1)/2 remaining edges. More explicitly, in any contiguous HIGH word using only h distinct labels >=z0 and wholly contained in such a gain window, its event length M satisfies
    M <=1+h(h-1)/2 + number of marked internal edge endpoints.
This includes arbitrary LOW paths between high labels. It is a combinatorial restriction, not a global bound on the number of distinct labels visited per window. We do not assert that deleting a marked edge yields a legal new trajectory.

For the prior signed shadow/record erasure scan, the retained positive ordinary repeated steps p>=z0 (eventually p>=10L+14) have preceding-LOW corrected change a_i^+<=2w_i<=4p. Therefore the sum of their positive changes at the marked endpoints is at most 4 W_edge. The expectation is o(U) for the stated choices of L,K. Delete these contributions once along with previous positive-step deletions; keep the original scan's disjoint negative credits unchanged. The earlier reduction remains valid:
    E[(D(U)-[R_new-C_shadow-C_other-Nminus]_+)_+]=o(U).
In particular a retained residual positive edge above root must either be the FIRST occurrence of its unordered pair or have span from the preceding occurrence's start to its own end >K min(p,q), regardless of first-discovery time or ranks. For common parameters satisfying previous discovery-rank bounds one may choose even slower L<= (log log U)^(1/4); the present estimate still vanishes. This adds a different deletion, including both orientations, to the existing conditions. It does not show that the first occurrence of a widely separated pair is rare enough in aggregate, nor bound the number of distinct pair traversals across all windows. The full signed limit and physical far-coalescence upper bound remain open.

## 6. Finite audit and persistence

Saved research/min_ghost_local_unordered_edge_recurrence_audit.mjs and research/min_ghost_local_unordered_edge_recurrence_results.json; exact remote readback at 509bcf63ce25f5dc2ca134ee4f45c05f96cac4f0. Run node research/min_ghost_local_unordered_edge_recurrence_audit.mjs 256 1024 4096 16384 65536. Executed script logic in the available JavaScript runtime, not separate local Node or Lean. Fixed pseudorandom common CRT phases, finite alphabet <=4U, 128 paths per U except64 at largest. A5,L6,K12, diagnostic base=max(7,floor(z0/16)), and require both labels >L+3 for tested distinct-edge pairs. The lower diagnostic threshold is for nonvacuous arithmetic tests, not an application of the root-scale hazard or the CRT multiplicity theorem below root.

For each qualifying diagnostic edge store its unordered pair, orientation, signs, LOW gain, start/end pre-gains and each label's pre-gain. For actual local recurrences compare with the preceding edge of that pair and verify the even same-label coefficients including shared events, positive adjusted coefficients and exact certificate (1), coefficient/ratio bounds, and positive divisor target in the corresponding later first-discovery order. Check that the later target is repeated. Count first-discovery rank gap >3 and both first-to-current gain spans >K times the respective label (diagnostic thresholds). For edges whose labels are both >=z0 check uniqueness of each directed signature and the 4L multiplicity bound. For each start edge check that any later recurrence within a gain window of width K*base is marked and the unmarked edges have count <=h(h-1)/2. This uses diagnostic edges and the deterministic local graph implication, not the probabilistic deletion below root. The audit verifies actual certificates, not the full hypothetical ticket budget of (2).

Across the five windows: 2507 distinct-event qualifying diagnostic edges, 137 edges with both labels >=z0; 73 actual local recurrence checks (2 same direction,71 reversed,71 sharing a middle event). 53 larger-latest and20 smaller-latest certificates (6+6+18+22+1=53); 20 with first-discovery rank gap>3 and 13 with both first-to-current gain spans>K times own label. All 2507 window checks pass. At U65536,N64:5138 events,281 diagnostic edges,19 root edges,1 local recurrence (reversed/shared, rank gap>3, target weight43, zero positive corrected change), maximum diagnostic pair multiplicity2. No local recurrence with both labels >=z0 was observed in the entire suite, so the certificate and graph tests are exercised mainly at the lower diagnostic threshold; no estimate of asymptotic constants or numerical evidence of the rate is inferred. All assertions pass. No Lean compilation.

## 7. Next target

The difference certificate removes discovery data from local recurrent edges and combines with CRT multiplicity to pay for every traversal of a certified pair. The remaining large-label residual can include new unordered edges, or long-separated re-traversals. A useful next step would control local paths visiting many distinct edges via higher-order arithmetic relations, or obtain a signed bound for those first edge traversals. Rank separation itself has not been proved to carry a globally nonoverlapping gain cost. No new branch, no main edit, no twin-prime proof.
