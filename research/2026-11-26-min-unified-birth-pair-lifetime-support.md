# True birth pair keys, lifetime harmonic envelope, and arithmetic thin-sector payments

2026-11-26 JST. Continues [590c13723c1a](https://github.com/tara-sooo/A166944-Lean/blob/590c13723c1ad5ff49553e06ad6f64d22f74921c/research/2026-11-26-min-unified-compatible-birth-transport.md) and [673f23837f86](https://github.com/tara-sooo/A166944-Lean/blob/673f23837f86cc5af8732aa01bd45923f5c04f3f/research/2026-11-26-min-unified-massive-word-partition.md). Independent heads verified unchanged at preflight: prime-root 1a4005f2f336ede61cca1a9656c158a559338b72; stable-heavy e1ad9e2b434c652699e1bc9a0797887631e0ea6d. New: reindex the exact remaining compatible backward charge by its true first meeting and BOTH incoming branches, bound it by a lifetime-weighted harmonic envelope without future trajectory comparison, count separate arithmetic supports of root/wait, jump/wait and jump/jump births (RESET and non-RESET), and pay new thin sectors including small secondary branches in high-high mergers. The sufficient objective is no larger than the previous one. No final upper contraction, no Lean compilation.

## 1. Frozen quantities

Retain original completed gain-stopped MIN prime-root paths, dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B. Each tag M is prime in [X,2X), origin C0(M)=2M-2, total gain <H, deficit in [0,6+5H], wait w<=2r<=3g, g=p-1. Under finitely many twins all tags eventually reach T, W_all>=N(T-6)/2. Same grids P_j, count m=Theta(u/ell), P_max<=B^.25, a=u^.25, c_a=3(1+2/a), tau>=1/log ell tends to zero. Keep ALL original masks of 590c137, including old compatible payments, old ancestry and root-gap exclusions, and its old projected destination thin mask. No original population, rank, trajectories or pair fractions recomputed.

Use the exact backward charge B_rem of 590c137, obtained from the compatible clock by resampling its per-tag source contribution uniformly over all b original members of its physical source exit slot. At a source crossing of n_k atoms, per ordered pair per atom the sum over the two focal sectors is <=c_a P/b; the per-tag total assigned compatible wait <=c_a P n_k. Every positive source has b>=b_min=H/[512 L0 B u ell³ sqrt(tau)], with L0 largest even primorial<=ell. Thus b_min=B^(1-o(1)). The old pair masks include first-meeting parent >tau b, larger incoming branch >tau b/d_* (d_*=ceil(20u/ell)), first meeting at least D_s/2 earlier in prehorizon than source (D_s=floor(T/(u ell^6))), and root separation >tau b u. The old routing chooses larger incoming branch member and a genuine original completed event on that member. We only REINDEX surviving charges by true birth U and the unordered pair of incoming branches. Keep their original orientation, amounts and old destination payment decisions; do not pay or reintroduce a previous paid charge. Forward defect D_all,rem remains unchanged. Thus exact sum of all new birth-key amounts is B_rem before the new masks.

## 2. Lifetime harmonic envelope

At true meeting U=(t,J), each incoming branch i is an actual distinct true predecessor or the singleton injected root. Let A_i be the FULL original tag set entering U via i, b_i=|A_i|. These include all original visits, even tags that terminate at U; including terminals only relaxes upper bounds. The original source-induced branch sets in 590c137 are subsets of A_i. Define nonincreasing lifetime count for x>=J:
    L_i(x)=# {M in A_i : 2M-2+H>x}.
This uses only original roots, not future MIN words. A tag contributing at source boundary K must satisfy K<its terminal horizon<2M-2+H. Also K>=J+D_s/2 by the old ancestry mask (the weaker K>=J suffices). Since C0(M)<=J for all M visiting U, all L_i vanish for x>=J+H.

For a fixed grid P and a fixed source boundary K>=J, the deterministic common continuation from U can cross K at most once, at one actual departure slot. Even if some tags stop, no tag reaching K follows a different continuation while present. Write x_i,x_j for the numbers of members of the two birth branches in that source slot. They satisfy x_i<=L_i(K), x_j<=L_j(K), and x_i+x_j<=b, the full original source population. The total surviving ordered-pair charge at this atom with these two incoming branches is <=2 c_a P x_i x_j/b, since a pair must have one tag in each branch and the per-atom ordered charge is <=c_a P/b. The two orientations give factor two, and all extra masks only reduce it. Since b>=b_min, this is bounded by
    2 c_a P F(L_i(K),L_j(K)),
    F(x,y)=xy/max(b_min,x+y), F(0,0)=0.
Here F is nondecreasing in each variable: in xy/b_min region it is obvious, in xy/(x+y) region derivative y²/(x+y)²>=0 (and symmetrically). The same source K cannot supply multiple different true slots for this fixed birth, by determinism. No assumption that distinct birth keys have disjoint contributing tag populations is needed because exact pair charges were partitioned first.

Summing the grid K and averaging over the SAME m grids yields, for exact birth-pair charge Bbar(U;i,j),
    Bbar(U;i,j) <= 2 c_a mean_P [ P sum_{K multiple P,
                             J<=K<J+H} F(L_i(K),L_j(K)) ]           (1)
                  <= 2 c_a [ integral_J^(J+H) F(L_i(x),L_j(x)) dx
                             + P_max F(b_i,b_j)]                   (2)
                  <= 2 c_a(H+P_max) b_i b_j/max(b_min,b_i+b_j).       (3)
The integral bound uses monotonicity and a left-endpoint Riemann estimate with at most one extra P F(b_i,b_j). One can improve (1) by K>=J+D_s/2 and by actual original terminal horizons instead of C0+H, with identical proof; we use the relaxed root-only lifetime counts for a simple independent upper envelope. In particular the charge is O(H min(b_i,b_j,b_i b_j/b_min)). Unlike the older one-branch destination capacity, this accounts for BOTH branch sizes and is small when one is tiny or both are far below b_min. It is a per-key upper bound; do not sum all harmonic envelopes and infer a small global total. The finite envelope can be very loose. No reverse implication from a large branch size to a large charge.

## 3. Exact arithmetic supports of true birth pair keys

At U=(t,J), s=t mod2, define k=(2t-J-6s)/2. If an incoming branch is a jump labelled p, its predecessor is exactly (t-1,J-p+1) and the exit conditions give p|t-2s, p|J+2s, k>=0 integer with p|k. Thus at fixed p,J,t there is at most one incoming p branch. Distinct incoming jump branches have distinct p,q. The only incoming wait predecessor is (t-1,J). A root injection at M has U=(M+2,2M-2), s=1, no possible incoming jump since p|M and p<=B<M. Its other branch must be wait, and by the old root-injection argument M=1 mod6 and the recorded arrival of that wait is even RESET at t=M-1. Both branches cannot be wait; there cannot be two different injections at one U. These exhaust pair types, even when there are more than two incoming branches at U.

The RESET condition is k=0 whenever an incoming jump is involved. All J in a common interval of length O(X) and k=O(H) (from the deficit slab). For fixed p, RESET jump/wait pair key count O(X/p): J+2s multiple p, t=(J+6s)/2, two parity choices. Non-RESET jump/wait count O(XH/p²): for each J and s, positive k is a multiple of p and at most O(H); t determined by J,s,k. Here p<=B<<H. For fixed distinct p,q, RESET jump/jump count O(X/(pq)), with both dividing J+2s. Non-RESET count O(XH/(p²q²)): positive k multiple pq, so if pq exceeds the slab bound there are no keys; otherwise count O(H/(pq)) choices of k. Since pq<=B²=O(X), the +1 in the count of J values is absorbed. No +1 is needed for strictly positive multiples k. These are upper support counts without roughness or assumption of independent primes. Root/wait count <=N, since U determined by M. This counts true birth AND pair of predecessors, not destination projection or all possible future source words. For fixed J,t there may be multiple pairs; each is explicitly accounted by its labels and type.

## 4. New thin masks by pair arithmetic

Let Q=B/u. Elementary reciprocal-prime upper bounds give sum_{3<=p<=B}1/p=O(ell) and sum_{Q<=p<=B}1/p=O(ell/u). For the latter use the upper bound pi(x)<<x/log x in the short multiplicative interval [B/u,B], by partial summation or O(log u) dyadic blocks with log x~u. No prime-tuple estimate. At each exact averaged birth-key charge, pay the entire key if it is at most the applicable ABSOLUTE cutoff in this table:

| key type | ordinary label cutoff | exactly one high incoming label (>=Q) | both high |
|---|---|---|---|
| root/wait | H/ell | not applicable | not applicable |
| RESET jump/wait p | H/(u ell²) | H/ell² | not applicable |
| non-RESET jump/wait p | p/(u ell²) | p/ell² | not applicable |
| RESET jump/jump p,q | H/(u ell³) | H/ell³ | H u/ell³ |
| non-RESET jump/jump p,q | pq/(u ell³) | pq/ell³ | pq u/ell³ |

In the jump/wait row "one high" means the sole jump label is high. The later departure terminating the wait is NOT an incoming jump label. Use disjoint sectors rather than adding separate payments of the same charge. For root/wait the total <=NH/ell=O(NT/ell). For the reset single jump ordinary sector, the support estimate yields O(XH/(u ell²) sum 1/p)=O(NT/ell); nonreset is the same after cancelling p against p². In the high single sector the factor u gain in the cutoff exactly cancels the factor 1/u in the reciprocal sum. For reset double jumps ordinary, sum over unordered distinct p,q of 1/(pq)<=O(ell²), so total O(XH/(u ell³) ell²)=O(NT/ell); nonreset similarly cancels one pq. In the one-high and two-high sectors reciprocal sums are O(ell²/u) and O(ell²/u²); their larger cutoffs still have the SAME O(NT/ell) total. The finite union of masks therefore pays O(NT/ell)=o(NT). In particular no extra log factor from number of grids, and no comparison of an actual wait mask to a raw boundary mask. All cuts apply AFTER old frozen projected destination payment, so exact remaining measure B_pair,rem<=B_rem.

These absolute thresholds are independent of the long ancestry capacity H. In some sectors the harmonic envelope gives all-mass exclusion, without evaluating the true exact charge:

* root/wait: b_injected=1. Equation (3) gives <=2 c_a(H+P_max) b_wait/b_min. For large X, 2 c_a(H+P_max)<=24H, so all such keys with b_wait<=b_min/(32 ell) are payable by H/ell. The old selected incoming branch lower cutoff was only tau b_min/d_*. The new root-specific cutoff is stronger in that sector for default tau and indeed throughout the allowed parameter regime. We do not pay all root injections.
* RESET with two high labels: all keys with min(b_p,b_q)<=u/(32 ell³) are payable by H u/ell³, even if the other branch is arbitrarily huge. Both branch populations of a residual RESET high-high key must exceed this growing threshold.
* non-RESET with pq>=H/ell: both p,q>=Q eventually since each <=B and H=Theta(B²/u^.25), so use pq u/ell³ >=H u/ell^4. All such keys with min(b_p,b_q)<=u/(32 ell^4) are payable. Also if p,q>=B/u^(1/16) then pq>>H, so non-RESET impossible by the old slab restriction. The product condition pq>=H/ell only gives an all-mass bound within that nonreset band, not the entire high-high nonreset sector.
* In any sector one may apply (1)-(3) to pay keys whose envelope is below the table cutoff, including small total product b_i b_j or short overlap of remaining root horizons. This yields a valid subset of the exact-charge thin masks, with the same total budget. It requires no enumeration of future source pair continuations for the decision once the true birth branches are given.

These are additional masks on birth PAIR charges, not on entire original waits or the old projected destination group. Old and new measures have different key domains, so only total comparison is asserted after reindexing. No assertion that the resulting heavy pair key support is empty.

## 5. Sufficient route and remaining gap

Under finitely many twins, 590c137 already proves
    NT/2-o(NT) <= B_rem+(3+o(1))D_all,rem.
Since exact birth reindex conserves the charge and the new thin masks pay o(NT),
    NT/2-o(NT) <= B_pair,rem+(3+o(1))D_all,rem.
Thus sufficient:
    liminf_(dyadic X) [B_pair,rem+3D_all,rem]/(NT)<1/2.    (4)
This follows from the prior sufficient inequality, because B_pair,rem<=B_rem and forward defect unchanged. The hybrid route can use the identical backward replacement with its old massive and moderate defect terms. The new content is the branch-product and lifetime capacity and new arithmetic support payment, not a new absolute contraction bound. Remaining birth charge includes large root/wait keys, reset and nonreset jump/wait keys, and double-jump keys above their corresponding caps. No proof that the remaining birth plus forward defect objective is small. In particular a bound on high-high alone will not suffice, and the finite audit shows substantial jump/wait mass. Main and source branches unchanged; no Lean compilation.

## 6. Audit

[Standalone audit](https://github.com/tara-sooo/A166944-Lean/blob/54a323116f6d7efa88099a9757197b09c82f57d0/research/min_unified_birth_pair_support_audit.mjs), exact remote readback verified. Seven runs passed in available ECMAScript runtime (four ordinary, three focus). Reproduce: node research/min_unified_birth_pair_support_audit.mjs 1024 4096 16384 65536. Derived from the final 0a91fc5 compatible-birth audit. Original finite T=min(8B,floor(X/2)) ordinary or floor(B/2) focus, grids [6,30,210], wheel6, eta=.25, b_min substitute cut=3 ordinary/2 focus, finite word lengths as before, raw 9P cell cap. Future-room mask instead of actual entropy. Retains prior finite pair masks (including only two gain units of recent trim), exact source and pair conservation, then records canonical unordered incoming predecessor pair for each routed charge. Independently scans all original true states to reconstruct full incoming root sets at every charged birth. Tests actual incoming divisibility and root injection type, RESET/nonreset split, exact reindex conservation, per-grid discrete lifetime envelope (1) with root upper endpoints and coarse bound (3), using finite c_a=9. Illustrative finite thin cutoff H*.02; NOT the analytic table or prior projected thin mask. The audit does not exercise the high-high case at its diagnostic threshold B/2; analytic high-high support/threshold claims follow by the proofs, not empirical counts. No independent sieve verification, integral numerical check (2), cumulative previous masks, literal gcd oracle or Lean test.

| X/mode | distinct birth-pair keys | incoming prime congruence checks | root type checks | lifetime-envelope checks |
|---:|---:|---:|---:|---:|
|1024|45|48|4|92|
|4096|213|227|22|515|
|16384|811|866|55|1979|
|65536|3241|3443|232|7869|
|4096 focus|145|154|16|262|
|16384 focus|701|737|54|1403|
|65536 focus|2981|3134|236|6723|

Largest ordinary X65536: 5709 roots,140255 completed events, no diagnostic T reaches, 591309 unordered pair checks and 984691 ordered route checks inherited. P=6 distinct 3241 birth keys: 232 root/wait,2575 jump/wait,433 RESET double jump,1 nonreset double jump. Exact charges by these types 35506.776330,968149.822232,129649.657214,505.594634 respectively, total1133811.850411. The discrete lifetime upper envelope summed over these keys is286291480.788322 versus constant envelope298047601.579983: valid but very loose, not an upper contraction. Finite illustrative thin 1615 keys pay79634.930045. P=30 total940148.802407 (root31110.580847,wait-jump802745.670689,double106292.550870), P=210 total907925.048821 (root28460.574583,wait-jump777371.019163,double102093.455076). Largest focus:2886 reaches,75256 events, P=6 2981 keys and total243431.889009 (root12493.069336,wait-jump200740.920687,double30197.898987). Both ordinary/focus largest include a positive nonreset double-jump key; no B/2 high-high birth across any of seven runs. No numerical inference of final sufficient inequality or proof of twin primes.
