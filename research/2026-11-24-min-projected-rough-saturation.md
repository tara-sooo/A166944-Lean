# Projected first saturation: clock compression and two-prime rough-transition sieve

2026-11-24 JST. Continues 2ccbaa46cd33f135d0a5b0d6a6f4b319e8aadd80 on the SAME research/min-cycle-forest-2026-11-24 branch. New elementary deductions using the established upper-bound sieve, exact finite audit; no Lean compilation. Transfer of previously concentrated mass and twin-prime infinitude remain open.

## 1. Exact same-parent clock compression

Retain canonical MIN, original odd M in [X,2X), N=X/2, dyadic X divisible by four, B=ceil(sqrt(7X)), t0=M+2, C0=2M-2, K(M)=floor((7M-1)/4), pre-event horizons C in [2X,7X). Let r(C) be the minimum odd eligible factor. All groups below retain original source tags and individual cutoffs.

For a proposed clock group A(n,p,C) (whether executed or stopped), let ell be the last eligible clock at C strictly before n, in the periodic extension, and w=n-ell<=2r(C). All parent arrival times lie in [ell,n). For a fixed preceding selected prime q, their times lie in exactly one class modulo 2q: either q|C and the times are 0 modulo 2q, or q|C+2 and they are q+2 modulo 2q. These divisibility sides cannot both hold. Thus the number m_q of DISTINCT parent arrival times in this clock group produced by q satisfies
    m_q <= ceil(w/(2q)) <= ceil(r(C)/q).
In particular m_q>1 implies q<r(C)<=p, as in the previous note. At the first physical/clock saturation at level kappa, each previously unmarked parent physical group contributes <=kappa-1 newly marked tags, so the total newly marked tags whose last label was q is <=(kappa-1)ceil(w/(2q)). This is a local bound, not a multiplicative contraction along all paths. The same physical parent group can have several incoming labels, and label changes without mergers can decrease q. One cannot telescope the ratios r(C)/q along arbitrary trajectories.

## 2. Project the merging groups to selected high keys

Fix LOW7, L=210. Partition the high-event path at every selected p>7, ignoring the intervening LOW-only prefix; its gain is even and <L by the established barrier. Use ANY absorbing process that stops at selected keys, retains original cutoffs and never reinserts tags, including the first-heavy process with cap tau from the previous notes.

A projected group G(p,C) consists of all active original tags at C whose actual next selected event is p>7, within their cutoffs, even if the group will be stopped before executing that event. For each tag in G with a preceding high key (q,D), write
    C=D+q-1+g,  0<=g<L, g even.
For a fixed (q,D,C), g is unique; any intervening clock times or low words do NOT create new incoming classes. This class is a subset of the earlier executed group G(q,D). The alternative initial class consists of tags with no preceding high event, at most A=floor(L/4)+1 distinct canonical roots (their initial horizons are in [C-L,C], spaced by 4). This gives a disjoint exact incoming partition of G(p,C). The necessary congruences are
    p | C+sigma,    sigma in {-1,1};
    q | C-g+eta,   eta in {0,2}.
If q=p>L+3 then these imply p divides g-1+sigma_current-sigma_previous, an odd nonzero integer of absolute value <p, impossible. Here sigma_previous is the side at D. Therefore adjacent high labels equal to a sufficiently large p are impossible, even though arbitrary low clocks intervene.

Mark every tag at its FIRST projected high group of mass >=kappa, independently of the absorption rule (marking does not stop or reweight). If a tag in an incoming class (q,D) is newly marked, the whole preceding group G(q,D) had mass <kappa; otherwise the tag was already marked there. Hence at most kappa-1 new marks per incoming class, regardless of chronology and whether other classes have large previously marked mass. This bound even holds for the TOTAL new marks from the same preceding key across ALL successor p at a fixed C (the subsets are disjoint). If G has only one noninitial incoming class and no initial class, no new mark is possible: that preceding group would have had mass at least the current mass. This eliminates the need to count same-q multiple arrival times when estimating first growth of PROJECTED mass. It does not assert physical and projected saturation coincide.

## 3. New unrestricted-time projected top-band and comparable-label deletion

Let Q=B exp(-sqrt(log B)), rounded up, and kappa=ceil(log^(1/4) B). For sufficiently large B, Q>L+3. Standard prime counting and partial summation give
    H_top=sum_{Q<=p<=B}1/p=O(1/sqrt(log B)), H_all=sum_{7<p<=B}1/p=O(log log B).
For distinct p,q, fixed g and signs above, the congruences give at most O(1+X/(pq))=O(X/(pq)) possible C, since pq<=B^2=O(X). All constant factors in L, signs, parity are harmless.

New marks at a key with current p>=Q:
- from a preceding class q, p!=q, count its candidate (p,q,g,C) and charge <=kappa-1 new tags;
- from initial classes, there are O(X H_top) possible (p,C) and <=A new tags each.
Total O((kappa+A) X H_top (1+H_all))=o(X).

New marks at a key with ANY preceding class q>=Q (even one whose tags were all marked earlier): choose a top witness class. For each other class (q',D'), with q'!=q, the two congruences on C give O(X/(qq')) candidates. Include every possible g,g' and parity side. Charge <=kappa-1 new tags in the counted class, and likewise for new tags in the witness class if it has another class. For q'=q with distinct D,D', the same one-prime congruence gives O(X/q) candidates; g,g' have finitely many choices. For an initial class paired with the witness, also O(X/q) candidates and <=A new roots. A witness with no other class cannot generate new marks. When p is not specified, sum NEW tags across different current p using the cap on the previous class, or the bound A on initial roots at C. No extra factor counting possible current p is needed. Total again O((kappa+A) X H_top (1+H_all))=o(X). This includes mixed-scale preceding labels and arbitrary clock gaps. It is strictly a result about first projected marks, not all source mass passing those transitions.

Comparable adjacent high labels: for any Y tending to infinity with Y>L+3, and fixed multiplicative factor F>=1, sum 1/(pq) over distinct p,q>=Y with p/F<=q<=Fp. Dyadic prime bands and the elementary prime count bound give O_F(1/log Y): each band has harmonic mass O(1/log P), and each band pairs with O_F(1) neighboring bands. Thus the total newly marked tags whose own preceding label q and current p are both >=Y and comparable is O_F(kappa X/log Y). This is o(X) if kappa=o(log Y), even with Y far below B. The same argument bounds newly marked tags in either of two distinct comparable preceding classes, without fixing current p. It does NOT cover other unrelated incoming classes just because such a comparable pair exists.

## 4. New two-prime sieve: rough current OR rough predecessor witness

This is stronger in a different direction, addressing expensive clock horizons rather than only top selected labels. Put
    H=exp(sqrt(log B)), Z=ceil(H), z=floor(exp(sqrt(log B)/10)),
    kappa=ceil(log^(1/4) B).
Call a high key (p,C) rough if r(C)>=Z. This requires p>=Z. Eventually Z>L+3 and z<Z.

For fixed distinct primes p,q<=B, suppose C is subject to the two congruences of section 2, and the current key is rough. When pq<=X/H, the possible even C form a progression of step 2pq with interval length N0=O(X/(pq)), and can be embedded in a consecutive interval of length comparable to X/(pq)>=H. Write C+sigma=p h. On this progression h and p h-2sigma are integer linear forms in the progression index, with slopes 2q and 2pq. All odd primes ell<=z except p,q give two DISTINCT forbidden residues, since both slopes are invertible modulo ell and the two forms differ after scaling by the fixed constant -2sigma. Roughness forces these forbidden residues to be avoided. Omit p,q from the sieve; the effect on the local product is uniformly bounded (odd primes, at most two omissions). The same dimension-two upper-bound sieve as in the prior merge-mass and first-heavy notes (Ford, Sieve Methods, Spring 2023, Theorem 2.4) gives
    O(X/(pq log^2 z))
candidates, uniformly in the two primes and shifts. The residue count error is O(2^omega(d)) per squarefree d; the available interval has length >=H and the chosen sieve level z is H^(1/10) up to rounding, so the usual remainder O(z log(2z)) is negligible. In particular log^2 z is comparable to log B. No lower-bound sieve or prime-pair distribution conjecture is used.

When pq>X/H, both primes exceed X/(BH), which is comparable to B/H (since B^2~7X). The unsieved count O(X/(pq)) suffices: the harmonic sum of primes in this band is O(1/sqrt(log B)), so the total candidate count here is O(X/log B). For pq<=X/H, summing the sieved count over all primes gives O(X (log log B)^2/log B). All fixed choices of g, sides and signs cost a constant depending on L. Hence
    total possible (p,q,g,C) with distinct p,q and rough current key
        = O(X (log log B)^2/log B).
The identical estimate holds when instead the preceding key (q,D) is rough: D=C-q+1-g is a fixed translation for the given q,g; divide its eligible neighbor by q and sieve the resulting two forms on the progression of step 2pq. It also applies to two DISTINCT preceding labels q,q' with gains g,g', when one of their keys is rough, and without imposing the current p congruence: divide the rough preceding neighbor by its selected prime q, and the progression for C has step 2qq'. The two-root argument and split at X/H are unchanged.

For a SINGLE prime rough key (p,D), the same sieve with progression step 2p gives O(X/(p log B)) possible D, because X/p>=cB>>H. This handles q'=q with different preceding D/D' (g,g' fixed), and a rough predecessor paired with initial roots. Summing over the prime gives O(X log log B/log B). Rough current keys with only initial roots, or new marks from initial roots, are similarly bounded by A times the single-prime count. Repeated adjacent high label p=q cannot occur when either key is rough, by section 2.

Now apply the exact new-mark cap on preceding classes from section 2:
(a) At any rough CURRENT key, charge newly marked tags in each preceding class to a candidate (p,q,g,C), and initial tags to the single-prime count.
(b) If there is ANY rough preceding witness class, count all new marks at the current key, even those in nonrough classes. Charge each newly marked nonwitness class to a pair with that witness, and any newly marked witness class to another class (or initial class); if there is no other class no first mark is possible. Same-label distinct keys use the one-prime count. If the current p is not fixed, sum over its groups using the total cap from each preceding class at C, or A for initial roots. Multiple witness choices only overcount.
Together the number of original tags first marked in either (a) or (b) is
    O((kappa+A) X (log log B)^2/log B)
      = O(X (log log B)^2/log^(3/4) B)=o(X).
This does NOT require a bound on ancestry depth, physical height, clock gap, or total unmarked occupation. It is a source-weighted result about FIRST projected saturation. It addresses a substantial class of long-clock projected mass growth even when the selected p is much below the top band. The arithmetic threshold Z grows subpolynomially in B.

## 5. Consequence for first-heavy stopping and precise remaining obstruction

Use the earlier uniform projected high-key cap tau=ceil(B log^2 B), with LOW7 grouping. Its executed prefix cost is O(X^2/log B), and no twin terminals would imply N-o(X) stopped tags. Every tag stopped at such a high key is marked at level kappa by the time it stops, since tau>=kappa. Therefore on a hypothetical no-twin window all but o(X) roots must have FIRST projected saturation at a key for which BOTH the current key and EVERY preceding high-key witness are nonrough (r<Z), and neither current nor preceding witness label is in the broad top band p>=Q. The last assertion uses the union of sections 3 and 4. The witness requirement is stronger than just the tag's own preceding key. This result concerns only the first level kappa, not the first saturation of the much larger threshold tau.

In particular only o(X) tags can first acquire projected concentration at a rough stop itself; the rest of a potentially large rough stopped population must have been marked earlier. The theorem does NOT imply their mass at rough stops is o(X): already marked tags can be transported through many rough keys. A proof still needs to bound the migration and subsequent growth of these cheap-origin clusters, or to show that enough roots escape final saturation. One cannot drop the earlier mark and apply kappa to an already concentrated incoming class. If marking only rough keys, intervening nonrough events need not have small selected labels, so the fixed LOW gain bound cannot be assumed between such keys. These are the next specific obstructions, not resolved by the present sieve.

## 6. Exact finite audit

Executed the saved JavaScript function body on six dyadic windows, exact integer arithmetic within range:
    node research/min_projected_rough_saturation_audit.mjs 256 1024 4096 16384 65536 262144

All original sources and cutoffs, LOW7, diagnostic absorbing cap max(2,floor(B/4)), independent projected marking. Four modes: kappa=8 or32 with Q=max(37,ceil(sqrt B)), Z=31; kappa8 with Q=max(37,ceil(B/log^(1/4) B)), Z31; kappa8 with Q=max(37,ceil(B exp(-sqrt(log B)))), Z=ceil(exp(sqrt(log B))). These are finite diagnostic thresholds (the large-B size conditions of the paper proof are not imposed on all small windows). Each group is partitioned by its actual previous high key (q,D), or initial class; the code verifies all gain and divisibility conditions, the impossibility of q=p when q>L+3, original previous mass consistency, cap on new marks from every preceding class, absence of first marks from sole noninitial class, exact stop conservation. At every proposed clock group it also verifies m_q<=ceil(w/(2q)) for all preceding labels (including LOW) and q<r for m_q>1, using the actual last eligible clock rather than only 2r. Literal parity-GCD checks at X256/1024: 4663, as in preceding audit. R, events, stops and twin counts match the parent diagnostic.

|X|proposed clock groups|groups with a multi-time same-q parent|maximum distinct same-q times|
|--:|--:|--:|--:|
|256|291|9|2|
|1024|1200|34|3|
|4096|5513|199|3|
|16384|22367|821|6|
|65536|91475|3525|7|
|262144|379092|14319|7|

At X262144, B1355, N131072, cap338: 3,620,133 executed events, R=98,554,147, 30 stop keys and 11,112 stopped tags, 119,960 twin terminals, 0 bad terminals. 14,844 (group,q) incidences with m_q>1; 6,394 of the 14,319 groups have a single preceding label and no root. Maximum observed ratio r/q in these incidences = 1021/3, maximum distinct same-q times 7 (not necessarily same group). The count 278,607 same-q witness tag incidences is a sum over groups, not distinct roots or new marks.

At kappa8,Z31:
|first projected mark category|all roots|stopped roots|
|--:|--:|--:|
|never marked|18525|0|
|rough current only|23763|2192|
|rough preceding witness only|34521|3392|
|both|22944|2526|
|neither|31319|3002|
|total|131072|11112|

Among the 4,835 tags stopped at a current rough key, 4,770 were already marked BEFORE reaching that key, and only 65 were newly marked there. With kappa32 the corresponding split is 4697 and 138. This illustrates why a first-mark theorem cannot be used as a theorem about all rough stopped mass. At kappa8,Q827,Z31, the all-root count of first projected marks involving top current or preceding label is 3,894. In the wider diagnostic mode Q93,Z15 the corresponding count is 51,937; neither is an asymptotic verification of the bound. All threshold modes and examples of clock compression are preserved in JSON.

Script and JSON committed and read back exactly at d008d9185bd21ff7d1dcfc63132fa9e8c2ee9beb. No new branch; main unchanged.

## 7. Next concrete proof target

Use the cheap-origin result to study the transfer of already concentrated clusters. Track incoming mass increments at projected high keys across a hierarchy of mass levels, or bound the population that can move from a nonrough first saturation to a rough selected key before its original cutoff. The exact preceding-key class partition controls a new level if its earlier class mass is below that level, but the count above has a linear kappa loss and cannot directly take kappa=tau. One promising intermediate calculation is to measure, per rough stop, how much of the mass was injected from each lower-level class, and how much was transported intact. A rigorous inequality must preserve original source tags and pay for the larger incoming masses; repeating the small-kappa argument would not establish the needed bound. The full concentration estimate remains open.
