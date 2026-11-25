# Event-index discovery packing and abundant log-scale two-label recoveries

Continuation of [8798cf0](https://github.com/tara-sooo/A166944-Lean/blob/8798cf0def95997805cc5e91a4a30cba6c84b68e/research/2026-11-26-min-direct-discovery-word-packing.md), on the independent direct-arithmetic branch. Two results: (i) event-index CRT compression with unrestricted known waits and a budget for long/new waits, applicable to whole clusters, and (ii) an absolute-scale construction showing why an all-start-state power-saving bound for *all* rapid low-band A1 recoveries cannot hold. Paper deductions with finite diagnostics; not Lean-verified and no novelty or twin-infinitude claim.

## 1. Relative event clock and reconstruction

At a state (t,H), even H, d=2t-H>=0, let par=t mod2. An event at n=t+w, I=n mod2, e=1-2I, with label p has p|H-e and p|n-2I. It follows that
    p | F=d+2w+1-6I.
For any given odd prime p and side I, the positive first clock wait is the unique integer w in [1,2p] satisfying
    2w=-d-1+6I mod p,   w=I-par mod2.                   (1)
The two congruences are coprime. For a known prime p with known residue of initial horizon H0 mod p, let g be the accumulated gain. If H0+g=1 mod p, the possible side is I=0; if H0+g=-1 mod p, I=1; otherwise p has no clock at this plateau. The residues are distinct. This determines its next hit via (1), without the absolute H0 or t0. Among known eligible primes the candidate is the lexicographically least (wait,label). If the actual next event uses a known label, it necessarily equals this candidate, even if unknown labels could also fire but do not win.

Fix initial horizon H0 in [A,A+G], even initial deficit 0<=d0<=D, integer label cutoff R>=S>=3, event budget K>=j>=1. Require R^2<=A+1. Count actual adaptive prefixes whose first j distinct labels >S are discovered by event K, with every selected label up through the jth discovery <=R. No restriction on labels after this prefix. All labels under consideration are eligible throughout; larger unknown competitors may eliminate some candidate starts but do not invalidate the upper bound. Every event wait <=2R by (1), d<=D+4RK, and every discovery defect is odd nonzero and satisfies |F|<=D+4RK+3 (use the cumulative elapsed time including the current wait). Set
    P_S=prod odd primes<=S,
    Q=pi(R)-pi(S),
    b=floor(log(D+4RK+3)/log(S+1)).
For each fixed candidate wait there are at most b possible new prime factors >S of F. No requirement that all factors of F are eligible, unlike the tick-prefix condition in 8798cf0; only R^2<=A+1 is needed for reconstruction of the retained labels.

Specify d0, par0, initial H0 mod P_S, and j strictly increasing discovery event positions in [1,K]. Start with all odd primes <=S known. At every nondiscovery event reconstruct the earliest known (wait,label) by (1). At a discovery there are two possible codes:
* short: record wait w<=W and prime p among the <=b candidate factors of F; I=(par+w) mod2;
* long: record p in (S,R] and side I; (1) reconstructs w with no explicit wait data.
In either case reject an event that does not beat the earliest known candidate, when one exists; set H0=e-g mod p and add p to the known list. Update g+=p-1, d+=2w-(p-1), par=(par+w) mod2. Actual prefixes are reconstructed uniquely; not all reconstructions need be actual. Each code restricts H0 to one CRT class modulo 4P_S prod of the j distinct new primes, using H0=2par0-d0 mod4.

If at most h of the first j discoveries have wait>W, the number of distinct starts is at most
    (D+2) binom(K,j) [P_S+G/(4(S+1)^j)]
      * sum_{ell=0..min(h,j)} binom(j,ell)(W b)^(j-ell)(2Q)^ell.       (2)
Use 0^0=1; impossible branches contribute zero. For a prefix with j discoveries whose total discovery wait is <=U, encode the positive waits as an ordered composition of sum <=U; there are binom(U,j) possibilities. This gives the alternative upper bound
    (D+2) binom(K,j) binom(U,j) b^j [P_S+G/(4(S+1)^j)].               (3)
Known waits are not included in U. More generally choose up to h discoveries to encode by label and side and bound the total wait of the remaining ones by U. The sum in (2) can be replaced by
    sum_{ell=0..min(h,j)} binom(j,ell) binom(U,j-ell)b^(j-ell)(2Q)^ell. (4)
For (4) long/short are merely code types; an actual prefix may have multiple codes, which only increases the bound. Binom(U,k)=0 for k>U and binom(U,0)=1. The finite audit separately exercises (2) and (3); (4) follows from the same composition count, not a separate audited experiment. These bounds apply to an arbitrary contiguous cluster as well as a single recovery. Fixed H0,d0 specify t0, so distinct start ticks on one ray are also counted. Overlapping prefixes and merging of different roots are allowed for the state count, not multiplicities of root tags.

## 2. Asymptotic extension

Take fixed lambda>1, H0 in [X,lambda X], D=O(log^C X), S=floor(a log X), 0<a<1. Let R=O(log^r X), r>=1, K=floor(log^beta X), beta>=1, j=ceil(theta log X/log(S+1)), theta>0. Use W=O(log^gamma X) with 0<=gamma<=r and h<=eta j, 0<=eta<=1, or the composition budget U=O(j log^gamma X) for the non-long discoveries. Assume a+theta<=1. PNT gives P_S=X^(a+o(1)); b=O(1), Q<=O(log^r X). The binomial positions cost X^(theta(beta-1)+o(1)). The short discovery choices cost at most X^(theta gamma(1-ell/j)+o(1)), the long choices X^(theta r ell/j+o(1)), uniformly ell. For (4), use k log(j/k)<=j/e to bound binom(U,k) by exp(k log(U/j)+O(j)); k=0 is trivial. Sum and choice of type cost exp(O(j))=X^o(1). Thus (2) or (4) bounds the start count by
    X^[1-theta(2-beta-gamma-(r-gamma)eta)+o(1)].                      (5)
When a+theta>1 replace the leading 1-theta by max(a,1-theta) before adding the position/type costs. If the allowed label band has fewer than j primes the count is zero.

At balanced R~.5 log X, a=.05, theta=.4, beta=1.1, gamma=.1, eta=.25, (5) is X^(.77+o(1)), below the previous conditional far-A1 lower count exponent 9/11. This permits total elapsed time up to 2RK=O(log^2.1 X), with arbitrary known waits and up to a quarter of discoveries long. It does NOT force j discoveries or the stipulated budget for the A1 population. It allows clusters containing several A1 marks if their labels satisfy the R cap; for an enlarged polylog cap r>1 the long-label cost in (5) grows. Example r=2, beta=1.1,gamma=.1,theta=.4,eta=1/8 yields exponent .775, permits elapsed O(log^3.1 X), and includes labels up to O(log^2 X). The smaller long fraction and discovery-count assumption are not automatic.

For a completed recovery after p, gain G_rec>=p+3+2T_rec (ordinary deficit drop at least p+3), where T_rec is actual elapsed time. By the previous per-prime time capacity, if G_rec>C_S(T_rec)+(j-1)(T_rec+R), then j discoveries are forced. Combining with (2)/(4) is valid under the corresponding event/long-wait budgets, even when the elapsed-time bound from K alone is too large for the old tick coding. This does not show that the previously required many far-A1 marks meet the condition. The old bound on total disjoint recovery time or gain, O(X), cannot by itself force polylogarithmic duration/event count for Omega(X^(9/11)) marks; it allows average scale X^(2/11). In particular there is no lower bound on the number of distinct high labels merely from a rapid recovery when p is of order log X. Section 3 gives actual witnesses at that absolute scale.

## 3. Controlled absolute-scale construction with two recovery labels

We refine the finite CRT word method of [A1 gain share](https://github.com/tara-sooo/A166944-Lean/blob/8798cf0def95997805cc5e91a4a30cba6c84b68e/research/2026-11-26-min-direct-a1-gain-share.md) by allowing many roots in an interval of prescribed absolute size, rather than choosing an arbitrarily huge CRT lift. Use arbitrarily large primes p=31 mod60 (Dirichlet). By PNT in the fixed reduced progression 1 mod60, select primes s,q with
    .67p<s<.70p,    .67s<q<.70s,
    s=q=1 mod60.
All distinct; s,q are constant fractions of p. Let a0=p,a1=s,a2=q, and shifts g0=0,g1=p-1,g2=p+s-2. Impose H0=0 mod4 and at each of the three pre-horizons H_i=H0+g_i:
    H_i=1 mod a_i;
    H_i != +/-1 mod f for every other odd prime f<=3p+6.             (6)
These conditions are locally compatible. At f=3,5 all shifts vanish mod f, and H0=0 works. For any unselected f>=7 there are at most six forbidden residues. At each selected prime f=a_i the forced residue H0=1-g_i mod f avoids the forbidden residues for the other two stages for all large p:
* at p the stage1 value is 0 mod p; stage2 is s-1 mod p, neither +/-1;
* at s the stage0 value is 2-p mod s, neither +/-1 since p/s is bounded away from integers; stage2 is 0 mod s;
* at q the stage0 value is 3-p-s mod q, neither +/-1 since (p+s)/q lies in a compact subinterval of (3,4); stage1 is 2-s mod q, neither +/-1 since s/q is bounded away from integers.
The stated ratios follow directly from .67,.70; the fixed shifts by 1,2,3,4 cannot affect these exclusions for large p.

With H0 sufficiently large (e.g. H0>=p^2), these residues force precisely the first three events (p,s,q), all even-side, with waits
    w0=(3p-7)/2, w1=(3s-2p-1)/2, w2=(3q-2s-1)/2.
Start at the canonical tick t0=H0/2+3, deficit6. w0 is odd (t0 odd); w1,w2 are positive even because of the mod4 conditions. For each stage, the even-side defect d+2w+1 reaches 3a_i at the stated wait. At even ticks the defect is 3a_i mod4 (a_i odd); the preceding multiple of a_i in this mod4 class is -a_i, which is not reached among future positive even-side defects. The odd-side selected prime cannot fire since H_i=1 mod a_i. All future defects through the prescribed event have absolute value <=3p+6. Thus (6) excludes every competing raw gcd factor through that event, and the raw gcd at the selected tick is exactly a_i (the only possible extra factor of 3a_i is 3, excluded by (6)). Eligibility holds. Direct substitution gives post deficits 2p,2s,2q. The first event is A1 since p>=47 and pre d+3=9<=p/5. Since 2s+3>p and 2q+3<p for large p, the first recovery to d+3<=p is exactly the second following event; its elapsed time w1+w2=O(p). It uses just the two distinct labels s,q.

## 4. Abundance in a prescribed horizon interval

Let c=(12/5)log 2, X=2^ceil(12p/5), so log X=c p+O(1), p~.6011 log X. Balanced cutoff R is the largest odd prime with P_R<=sqrt X; by PNT and the ratio of consecutive large primes tending to 1, R~.5 log X. Hence p>R, s,q<R for all sufficiently large p. All these p marks are far from square (p=O(log X), opposite cofactor of the selected neighbor is of order X/log X). They have initial post deficit 2p=O(log X) and recover in O(log X) ticks using only two labels <=R. Both labels exceed S~a log X for e.g. a=.05.

We can actually obtain X^(1-o(1)) distinct such starts in [X,2X] before the first mark. Choose Y=floor(p/10). First impose all restrictions (6) at odd primes f<=Y, H0=0 mod4 and the three prescribed residues at p,s,q (>Y). The resulting modulus is
    L0=4psq P_Y=exp((.1+o(1))p).
For each unselected f<=Y let A_f be the number of allowed residues (>=f-6 for f>=7, >0 for 3,5). There are B0=prod_{f<=Y, odd prime} A_f distinct allowed residue classes mod L0, each containing N=X/L0+O(1) integers of [X,2X), uniformly. For the remaining primes Y<f<=3p+6 other than p,s,q, each forbids at most six residues mod f. Inside any such progression, L0 is coprime to f, so each residue excludes <=N/f+1 candidates. A union bound excludes at most
    6N sum_{Y<f<=3p+6} 1/f + 6 pi(3p+6) = o(N),
uniformly over the residue classes. Indeed the reciprocal sum is O(1/log p) by the upper PNT bound and f>Y, and N is exponential in p. No independence assumption for the remaining exclusions. Therefore all classes together contain at least
    (1-o(1)) X B0/L0
      >= c0 X/[p^3 (log p)^6] = X^(1-o(1))                         (7)
actual roots, with an absolute c0>0 for sufficiently large p. The product lower bound follows from the ordinary prime Mertens product: for f>=7, (1-6/f)/(1-1/f)^6 has a positive convergent product (log terms O(1/f^2)); factors 3,5 contribute positive constants. Also psq<=p^3. This use of PNT in fixed AP and Mertens is classical and independent of prime-tuple conjectures. A weaker X^(1-o(1)) result follows from elementary prime counting and the reciprocal-prime sum bound O(loglog p). In fact even a single allowed small residue class with Y=alpha p for any fixed small alpha>0 would give X^(1-alpha/c+o(1)) starts.

Each admissible H0 gives a distinct canonical root M=H0/2+1 and a distinct post-A1 start (H0+p-1, deficit2p), lying in [X,2X+O(log X)]. Thus for infinitely many X there are X^(1-o(1)) distinct actual far-A1 recovery start states of log-size p>R, whose recovery takes O(log X) ticks and uses only two labels <=R. They do not meet the large-p hypothesis or high-discovery requirement of the previous packing bound, regardless of the small elapsed time. In particular any uniform bound O(X^delta), delta<1, on ALL such recovery starts, across canonical roots, is false. This is not a lower bound for their occurrences on ONE fixed trajectory: the roots vary, and their post-mark states may lie on different rays. The abundance does not prove the sparse-window hypotheses, a macroscopic infinite trajectory, or finite twins. It strengthens the earlier finite-word obstruction by explicitly locating it at p comparable to log H, precisely the balanced cutoff regime.

The construction itself only uses composite selected neighbors and excludes small competing factors, not primality of H_i±1. It does not impose the nonterminality of every later plateau after the third event. It is compatible with a finite or infinite number of twins.

## 5. Why this changes the next target

The latest packing estimates can discard clusters with sufficient distinct discoveries and short discovery-wait budget. The log-size, few-label recovery population cannot be discarded by a power-saving count over all start states: (7) gives a counterexample. The old support-barrier identity (gain<2 prod used primes) does still apply to each recovery or cluster; if all its labels <=R and only k new labels beyond S occur, gain<2P_S R^k. At S~a log X and polylogarithmic cluster gain this bound alone does not force any high discovery. If repeated copies of a fixed word occur on one ray, the earlier support-repetition budget forces intervening outside-support gain; a useful next goal is to control how those charges overlap across many varying supports, or to count the frequency of the same two/three-label log-scale recovery families along actual canonical rays. A second direction is a deterministic upper bound on large first-return or far-B supply in the nonsparse branches. Neither sparsity follows from finite twins; none of (2)-(7) contradicts the necessary count on a fixed ray. No closing stopping invariant.

## 6. Diagnostics and preservation

[Event-index audit fae71c6](https://github.com/tara-sooo/A166944-Lean/blob/fae71c68ca6c1b272f3816ae16d525c5f541a3f8/research/min_direct_event_discovery_packing_audit.mjs), blob 26f5af472a06840a3791b825f42e3dca8137e77b. Run node research/min_direct_event_discovery_packing_audit.mjs 6000. Actual ECMAScript executed in tool runtime (not a separate Node process). 288271 abstract starts, 2998 odd canonical roots through6000,32651 actual canonical events (180-event cap; not all termination asserted);2769155 exact clock comparisons,366193 independent literal GCD ticks sampled;265295 reconstructions,1257566 reconstructed events;33631 known high reuses,594526 low known events,156261 long known waits,485397 short-coded discoveries,144012 long-coded discoveries;109458 mixed prefixes,133308 total-wait prefixes,223127 code groups,17900 exact BigInt CRT spacing comparisons,14 global capacity tests,1358386 support capacity checks. 8193 mixed-coded prefixes have elapsed time >K*W and at least one long known wait; max elapsed318. No completed A1 recovery in this small scan; separate scale-controlled witness below. All assertions passed. Counts include overlapping modes and prefixes. Bounds tested with exact BigInt combinatorial arithmetic; finite runs do not establish the asymptotic exponents.

[Log-scale audit 45ecde8](https://github.com/tara-sooo/A166944-Lean/blob/45ecde8c329833dc2b33f16ab4af3694c99a51c6/research/min_direct_log_scale_recovery_audit.mjs), blob 230fbd5765fef36e98c0a5997c84b94ded9b878b. Run node research/min_direct_log_scale_recovery_audit.mjs. Actual ECMAScript execution; choose X=2^ceil(12p/5) exactly, balanced R by exact prime product, construct one allowed small-residue progression and scan first admissible representatives. Three distinct actual canonical roots in [X,2X) for each of the following words:
|p|s|q|R|waits|decimal digits of X|
|--:|--:|--:|--:|--|--:|
|2551|1741|1201|2161|3823,60,60|1844|
|3391|2341|1621|2861|5083,120,90|2451|
|8431|5821|4021|7103|12643,300,210|6092|
Nine roots total, 67167 literal BigInt GCD ticks with independent relative GCD comparison,45054 exact stage residue checks,163 progression candidates (154 rejected),265 small-prime class checks. All passed; exact recovery after two labels. These are actual canonical prefixes with controlled H scale; they test compatibility and clock geometry, not an empirical proof of the count (7).

Both audit source files exact remote readback verified. No Lean executable, no kernel proof, no Lean changes. No new Fourier exponent or proof of finite-twins contradiction; no external novelty claim. Main and siblings not changed by this work.
