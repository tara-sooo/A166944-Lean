# Two-stock transition divisor tickets at the latest first selection

2026-11-25 JST. Continues cb3b0cc13ca3bdd68bcb0ff77b4c24f78ed62555 on the SAME research/min-cycle-forest-2026-11-24 branch. New unconditional weighted bound on consecutive high transitions with a repeated target, including BOTH endpoints already selected long ago. No deletion of a known prime or artificial restart of its hazard. The estimate works at polynomial scales with no first-span or intervening repeat-rank restriction. Original mathematical derivation and finite common-CRT structural audit; no external search or Lean compilation. The full signed-peak and physical far-coalescence limits remain unresolved.

## 1. Exact relation and the gain-capped prefix

Use the common independent CRT ghost, conditional on common initial time parity, for the infinite odd prime alphabet or any finite initial segment. A selected label p increases the even relative gain by p-1; its completed preceding wait w<=2p. Let U>=2 be the integer observation horizon and z0=ceil(sqrt(2U)). The exact tick-history law gives conditional hazard <=2/p^2 for a fresh p>=z0 at any tick through U. Fresh always means first selection since the original time zero.

Let A>=5, L=L_A=2 product_(3<=ell<A)ell, with L<=log^(1/8) U for the eventual asymptotic applications. A HIGH event has label >=A. Consecutive HIGH events may have arbitrarily many LOW events between them, but their intervening LOW gain d is even and 0<=d<L. Use the prefix of events through U whose POST-gain is <=2U; it contains every positive attained peak and its earlier prefix. The sum of event weights p in this prefix is <=3U, since p<=1.5(p-1). In particular all selected labels in this prefix are <=2U+1.

Consider consecutive HIGH events q,p in that prefix, with p repeated, q and p both >=z0. The q event may itself be fresh or repeated. For sufficiently large U, q=p is impossible in such a pair: the consecutive equal-label pre-gain difference is p-1+d, even, with p-1<=p-1+d<2p-2 for p>L+3. No even integer in this range is 0 or +/-2 modulo the odd p. Thus the two labels are distinct.

Write u_q,u_p for their respective FIRST pre-gains in the original path. Write G_q,G_p for their current pre-gains. The eligibility signs give
    G_p=u_p+m p+a,  G_q=u_q+n q+b,
    a,b in {-2,0,2}, m>=1, n>=0,
    m<=(2U+2)/p, n<=(2U+2)/q.
For q fresh use n=0,b=0; for q repeated n>=1 by gain growth. These representations are unique for p,q>=7 because offset differences have magnitude <=4. In fact m,n are even by gain parity, but the upper bound below overcounts all integer strides. Since G_p=G_q+q-1+d, we have the exact identity
    m p-(n+1) q = u_q-u_p+b-a-1+d.                  (1)
The first selection of either label can be arbitrarily far in the past. We do not require a short return interval, local stride difference, or small number of intervening high events before the current pair.

## 2. Assign tickets at the latest first-selection tick

Take dyadic bands p in [P,2P), q in [Q,2Q), P,Q>=z0. Only bands with lower endpoints <=2U+1 matter. At each tick through U, condition on the exact selected-label and quiet-tick history before that tick. At this point the pre-gain u and all earlier selected labels, their first pre-gains and first-selection ticks are known. For any actual pair (1), the LATER of the two first selections is a fresh label at a specific tick, and the other label is already known. Use that tick for ticket assignment. Only assign tickets when pre-gain u<=2U; an actual witness in the gain-capped prefix satisfies this.

Case P-latest: at the first selection of p, q is known with u_q. Enumerate n in [0,(2U+2)/Q], a,b in {-2,0,2}, and even d in [0,L). The candidate fresh p must divide the fixed integer
    M=(n+1)q+u_q-u+b-a-1+d,
and M=m p>0. Discard M<=0, including zero; it cannot give a valid witness with m>=1. Each positive M is O(U) because u,u_q<=2U and n q<=O(U), q<=2U+1,L=o(U). Thus it has O(1) distinct prime divisors >=P>=sqrt(2U), by the product of its distinct prime factors. For a particular candidate p, m=M/p is determined. We may overcount all tuples failing the other gain or chronological conditions. There are O((L+1)U/Q) tuples per known q. A candidate fresh p contributes ticket weight p, times conditional hazard <=2/p^2, so its conditional expected ticket weight is <=2/P. Summing the O(1) divisors, tuples and known q's gives per-tick conditional expected ticket weight
    O((L+1) U K_Q(s)/(P Q)),                      (2)
where K_Q(s) is the number of previously selected distinct q labels in [Q,2Q). No probability assertion is made about their later known-label selections.

Case Q-latest: at the first selection of q, p is known with u_p. Enumerate m in [1,(2U+2)/P], a,b and d. The candidate fresh q must divide
    M'=m p+u_p-u+a-b+1-d,
and M'=(n+1)q>0. Again discard nonpositive values; the actual relation is strictly positive even if q is fresh at the observed pair. Each positive M'=O(U) has O(1) distinct prime factors >=Q, and for each candidate q, n=M'/q-1 is determined. The ticket weight is the TARGET p<=2P, not the currently fresh q; its conditional selection probability <=2/q^2<=2/Q^2. Summing O((L+1)U/P) tuples per known p yields per-tick conditional expected ticket weight
    O((L+1) U K_P(s)/Q^2).                        (3)
These two cases exhaust all actual pairs. Assign tickets only if the candidate label is actually selected for the first time at the designated tick. A ticket can be identified by (p,q,m,n,a,b,d), with first pre-gains determined by the actual discovery history. Each actual pair has its exact tuple included; distinct actual pairs cannot consume the same tuple, because the tuple fixes G_p and gains strictly increase. Thus realized total p-weight injects into the assigned ticket weight. Counting all a,b separately rather than only their difference avoids any ambiguity here. This is not an assumption that the prospective return positions occur on the future path.

## 3. Expected weight in rectangles and mixed product regions

The exact fresh hazard and the elementary prime-count bound pi(x)=O(x/log x) imply uniformly in the tick s
    E K_Q(s) <= 2U sum_(Q<=q<2Q prime) 1/q^2
              = O(U/(Q log Q)),
and similarly E K_P(s)=O(U/(P log P)). This does not assume independence of the selected stock and its first pre-gains. Insert these estimates in (2),(3) and sum the at most U ticks. The expected realized total weight W_[P,Q] of the stated pairs in the two bands satisfies
    E W_[P,Q] <= O((L+1) U^3/(P Q^2)
                    * (1/log Q+1/log P))
               = O((L+1) U^3/(P Q^2 log(2U))).      (4)
The absolute implied constants are uniform over the bands, since both lower endpoints are >=sqrt(2U), and the cap on gain bounds every divisor target by O(U). The first term in (4) comes from the P-latest case, the second from the Q-latest case. In particular no factor for enumerating BOTH strides is needed: the other stride is determined by the positive divisor target.

For arbitrary lower thresholds P0,Q0>=z0 (and P0,Q0>L+3), sum (4) over the geometric bands P=2^i P0, Q=2^j Q0 up to 2U+1. Writing W(P0,Q0;U) for the total p-weight of such pairs with p>=P0,q>=Q0, we obtain
    E W(P0,Q0;U) <= O((L+1) U^3/(P0 Q0^2 log(2U))).          (5)
The sum vanishes when either threshold exceeds 2U+1. This holds for both infinite and finite initial-segment models. No expectation of the unrestricted gain is needed. For L<=log^(1/8) U and P0 Q0^2>=U^2 (with both thresholds >=z0), the normalized expectation is O(log^(-7/8) U), hence the weight is o_prob(U). For example, with suitable ceilings and the root lower bound where necessary, the following (target exponent, predecessor exponent) pairs are covered:
    (2/3,2/3), (3/4,5/8), (1/2,3/4), (9/10,11/20).
More generally fixed exponents alpha,beta in [1/2,1] satisfying alpha+2beta>=2 work. The asymmetry reflects weighting by the repeated target p. This extends the comparable or upward fresh-to-known estimates to KNOWN-to-KNOWN transitions at these scales, independently of the first-return spans. The earlier short consecutive-return support result at U^(2/3) only excluded short cycles such as p,q,p with restricted intervening labels; the present result controls adjacent high transitions q,p between distinct already known labels even when neither label's prior return interval is short. It bounds total weights, not the probability of any occurrence.

There is also a scale-uniform product version. For H>=1 let W_product count such pairs with p,q>=z0 and p q^2>=H U^2. Use bands from z0. Any contributing band must have P Q^2>=H U^2/8. For each Q the sum of 1/P over such P is O(Q^2/(H U^2)), including the case where the lower band threshold z0 is larger. Therefore the sum of 1/(P Q^2) over contributing bands is O(log(2U)/(H U^2)), since there are O(log U) Q bands. Substituting in (4) gives
    E W_product <= O((L+1) U/H).                    (6)
For H=log^(1/4) U and L<=log^(1/8) U, the normalized bound is O(log^(-1/8) U). Thus all scales above root satisfying this product gate can be removed simultaneously, not merely a fixed rectangle chosen in advance. The additional logarithmic loss compared with a single rectangle on the boundary P0 Q0^2=U^2 comes from summing Q bands; (6) does not yield sublinearity for H=1 with growing L. These are upper bounds on the actual pair weights, not just on rough or positive steps.

## 4. Signed record application and remaining scope

Use the prior high-poststate backward scan, with corrected height J=2s-g_post-6chi. At high event p the preceding-LOW corrected increment a_i satisfies
    a_i <= 2w_i-(p-1)+5L+6.
For p>=z0 eventually p>=10L+14, so a_i^+<=2w_i<=4p (and a_i^+>0 requires w_i>p/4). The weights in (5),(6) therefore bound the sum of all positive corrected increments at the indicated transitions, including the subset retained by disjoint backward record erasure. This applies before any record filtering and includes q repeated. We may delete these increments once from the earlier R_res while retaining the unchanged negative credits C,Nminus:
    E[(D(U)-[R_new-C-Nminus]_+)_+]=o(U).
For the scale-uniform product gate with H=log^(1/4) U, a remaining positive retained repeated high step must either have one of the consecutive high labels below z0 or have p q^2 < H U^2, in addition to the previous conditions. Fixed rectangle deletions (5) can also be applied, for example both labels >=U^(2/3). Any finite union costs o(U); the statement does not use an unproved countable uniform union over arbitrary rectangles. This is a genuine known-to-known deletion, but it leaves repeated transitions at smaller mixed scales, such as both labels near sqrt U, and the earlier small-label and long-gap record residual. The theorem does not imply the full signed peak limit eta->0 or the independent physical far-coalescence upper bound.

## 5. Finite audit and persistence

Saved research/min_ghost_two_stock_transition_divisor_audit.mjs and research/min_ghost_two_stock_transition_divisor_results.json; exact remote readback at c0265edb625418dc69cb9d1cdfef0fed3075ebdb. Run node research/min_ghost_two_stock_transition_divisor_audit.mjs 256 1024 4096 16384 65536. Fixed pseudorandom CRT coordinates, finite initial alphabet of odd primes <=4U, 128 paths per U except 64 at U65536, A5,L6. The program was executed in the current tool's JavaScript runtime; no separate local Node or Lean compilation was performed. Diagnostic base=max(7,floor(ceil(sqrt(2U))/8)) is deliberately below the analytic root bound, to exercise actual both-repeated transitions. Also separately count at root and ceil(U^(2/3)). No empirical estimate of the asymptotic constants or finite-to-infinite error is asserted.

At every fresh label >=base within the gain-capped prefix, enumerate tickets in both roles against each previously known label >=base. Enumerate one stride, all offsets and allowed LOW gains, compute the positive divisor target, and if divisible by the selected fresh label derive the other stride. Filter parity, gain cap and relation; store distinct tuple keys. For every actual qualifying consecutive high pair with repeated target, verify exact first-to-current strides, LOW gain bound, identity (1), positive divisor target in the appropriate latest-discovery case, and that the distinct ticket was previously assigned (and not consumed). Check per-path weight budget and total realized weight<=3U at the three thresholds. Record exact preceding-LOW corrected positive increment. The diagnostic cases below root are structural arithmetic tests, not applications of the analytic fresh hazard.

Across the suite 629 actual pair checks, 245 with both labels repeated, 131 P-latest, 498 Q-latest. All 629 distinct tickets were found and consumed once. At U65536,N64: 4500 events (4499 capped), 4 qualifying pairs above diagnostic base45, all both repeated, 3 P-latest and 1 Q-latest, 3 with long target wait. Total target weight916, total positive corrected increment562, 533936 candidate tickets. The candidate weight at base is 74644512, much larger than realized weight; it is an overcount used for the proof. Across the suite at root there were 3 actual pairs, all fresh predecessor, and no actual pair with both labels repeated. At ceil(U^(2/3)) there were no actual pairs. Thus nonvacuous both-repeated structural tests occur at the lower diagnostic thresholds, not in the asymptotic range of (5). All assertions passed in the executed runtime. No Lean compilation.

## 6. Next target

The latest-first-selection divisor argument removes the requirement that the immediate predecessor be fresh. Both labels can have long, unrelated first-return histories. A potential next step is to exploit the actual preceding time/gain relation in a pair to reduce the remaining stride count, or to replace the root-scale hazard by a local discovery/exposure bound without conditioning on future return success. The principal residual still contains smaller-scale known-to-known runs, for which (5) is too large, and signed cancellation is not yet controlled globally. No new branch, no main edit, no twin-prime proof.
