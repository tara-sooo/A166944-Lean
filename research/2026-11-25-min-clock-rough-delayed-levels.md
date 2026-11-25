# Rough outgoing-slot support, delayed thick cohorts and true-tick deficit matching

2026-11-25 JST. Continues c8999c230ed4a80def419a7e4eaab3aea255eeec. New paper deductions: an extra reciprocal-prime logarithmic saving in rough eligible horizon support and weighted outgoing-slot support; negligible linear removal of thin aggregate cohorts independent of incoming q, including a delayed version forcing all retained same-slot pair-ticks to have a prior stationary common history; exact weighted allocation to true-tick upward deficit levels and separation into immediate cancellation, later matched and terminal unspent energy. This replaces the proposed purely incoming-gain transport for small q by a precise alternative ledger. It does not bound the terminal or matched ledger at the sufficient scale. No Lean compilation, twin infinitude OPEN.

## 1. Outgoing arithmetic support (NEW uniform weighted slot estimate)

Use original all-odd dyadic MIN roots M in [X,2X), N=X/2, B=ceil(sqrt(7X)), s=M+2,C0=2M-2,K=floor((7M-1)/4), H=4B,a=2B,u=log B,D=max(1,floor(B/u^2)). Assume original gate H+2B<=K-s eventually. Use full actual completed waits starting before relative H, including the crossing wait, stopping at twin terminals. At C, r(C) is the least eligible odd prime <=B dividing (C-1)(C+1), and actual next selected p>=r, p<=B. Wait [b,v) has length <=2r. The projected natural occupation may be late HIGH clipped to [a,H) or full positive-drift waits; arbitrary smaller nonnegative weights per tick in [0,1] are allowed. No new charged occupation outside the original prefix.

Call C rough when r>=D/4, r>0. All relevant horizons are O(X), and actual next event clocks satisfy C/2<=v<=C/2+3+H+2B, since C<=2v and C>=2M-2. If outgoing parity k=v mod2 and selected prime p, then p|C+2k-1 and v lies in a single progression of modulus 2p (0 for even, p+2 for odd). For fixed p,k there are O(B/p) possible phases v per C, uniformly including boundary rounding. Here p>=c B/u^2, and for all sufficiently large B this exceeds the earlier uniform rough-sieve cutoff B^(1/64).

The congruence C+2k-1=pj and roughness of C-1,C+1 imply O(X/(p u^2)) possible C by the same uniform two-form upper sieve used in the base true-birth and rough-anchor papers. Indeed one form is p times j, and modulo any odd sieve prime !=p the two forbidden residues in j are distinct. The interval length O(X/p)>=cB absorbs the earlier uniform error. Ignoring the additional MIN and exact slot reachability restrictions increases the envelope. The reciprocal prime sum over cB/u^2<=p<=B is O(log u/u) by Chebyshev and dyadic summation, with log p~u. Two consequences:

* Eligible rough horizons: choose p=r(C) and its side. The count is O(X/u^2 * sum_p 1/p)=O(X log u/u^3), strengthening the earlier plain rough support O(X/u^2). This extra factor uses r<=B; it is NOT an estimate for all integers avoiding small primes, including twin terminals with r=0.
* Weighted outgoing clock slots: each candidate (C,v,p) costs r(C)<=p; sum over its O(B/p) phases. The distinct actual slot (C,v) has unique selected label p by deterministic MIN. Hence
    S_slot=sum_actual rough slots r(C)
       <= O(XB/u^2 * sum_p 1/p)
       = O(XB log u/u^3).                             (1)
This sums weights over distinct physical slots, not original-tag incidences or ancestry masses. It holds for every actual completed original prefix, and does not require a lower bound on the last incoming q. The old reference tag incidence budget sum_(M,wait) r(C)=O(XB) follows separately from total gain O(B) per original tag and r<=1.5(p-1).

## 2. Delayed thick-cohort peeling with negligible linear loss

For each actual rough slot sigma=(C,v), partition its natural original tag incidences into a fixed bounded number J0 of classes, using their unmasked histories. A useful example: root-only with no prior nonLOW anchor, comparable incoming q>=r/f, and small q<r/f, where L is the tiny even primorial from the preceding checkpoint, y its largest prime, and f=u^(1/4). This comparison threshold is deliberately changed from the prior q>=r/u^(1/16); the new lemma works with either threshold and with arbitrary fixed classes. No reliance on the tiny primorial is needed for (1) or the peeling itself.

For class j in a slot define N_(sigma,j)(z)=#actual original tags of that class with wait arrival b_M<=z<v. This is the monotone cumulative arrival count of the original completed wait, NOT the number of tags whose clipped late occupation contains z. Every such tag exists in the actual prefix throughout its unmasked wait up to the same v. Take
    m=u^(11/4), eta=u^(-1/4), ell_sigma=max(1,floor(eta r(C))).
For arbitrary preceding holes, perform the following actual tick deletions:
(A) optional outgoing mismatch: discard the chosen wait occupation when p>f r. Then R_loss <= sum r <= (1/f)sum p = O(XB/f)=o(XB), because p>=3 and total selected gain O(XB).
(B) discard the first ell_sigma+1 ticks of each wait [b_M,v), so each remaining tick t has t-ell_sigma>=b_M+1. Its linear cost is <=(eta+O(1/r_min)) sum_(M,rough waits) r(C)=o(XB), with r_min=cB/u^2. This also eliminates short clipped occupations if they fall entirely in this initial part, with exactly the same bound.
(C) discard a remaining tick t if N_(sigma,j)(t-ell_sigma)<=m in its own class. Crucially, shift t back by ell_sigma. At each shifted z there are at most m eligible original tags if the gate fails, and all shifted ticks are actual within their own waits by (B). There are at most 2r possible z per slot. Each removed unit tick costs 1/2 in linear R. Thus
    R_thin,delayed <= J0 m S_slot
       = O(J0 XB log u/u^(1/4))=o(XB).                (2)
This direct shift avoids charging a full thick arrival burst during the delay. It is valid for arbitrary fractional prior tick masks bounded by 1. For J0 growing slowly it suffices that J0 log u=o(u^1/4); no claim for O(u) dyadic label classes. Apply before the final density gate, or reapply that gate with fixed reference.

Every surviving small-q tick now has MORE THAN m actual small-q companions already present at the shifted earlier tick (including itself), not merely a large total mass at departure. This is an unconditional aggregate thin mask that handles small q with no q/r factor. It does not show that the thick small-q class is rare. All removed pair products are absent from RETAINED energy; they are not absolutely paid quadratic energy.

## 3. All retained same-slot pairs have a stationary earlier common interval

For any unordered pair of original tags in the same slot, orient toward the later unmasked arrival b=max(b_M,b_M'), tie arbitrarily. Expand its ordered offdiagonal projected energy e=2r w_M w_M' over the focal tag's retained ticks t, each weighted by the other tag's full retained w<=1 (and the focal tick fraction if needed). Gate (B) ensures both actual original paths share state C on the whole interval [t-ell_sigma-1,t]. In particular t-ell_sigma is a true stationary upward tick, even when one retained occupation is clipped to a different source-relative age. This applies to ALL same-slot pairs, not just those previously classified OLD at a fixed D scale. The delay is relative to r, generally smaller than D for the lower rough band. It is not a claim of common history for D ticks. Distinct slots are unaffected except for the actual linear masks.

Define d(t)=2t-C(t) at actual true tick states. At a stationary tick d increases by 2, while at a selected event p it changes by 3-p. Thus both integer levels
    lambda_1=2(t-ell_sigma)-C-1,
    lambda_2=2(t-ell_sigma)-C
are actual upward crossings on the shared true path. Charge half of the focal tick contribution to each. These levels are positive because the previous state has nonnegative deficit. For a fixed pair, the shift is injective within a slot; across slots the charged ticks lie in disjoint actual waiting intervals. Thus no physical upward crossing of that pair receives total charge above 1/2 (weight<=1 per tick). This is a pairwise allocation to actual levels; it does not replace pair multiplicities by arithmetic key counts.

## 4. Exact immediate / later / terminal split, including small q

For a pair sharing the slot, let v be its next event, d_v=2v-(C+p-1) the post-deficit, and d_min^+(v) the minimum true deficit from v through the earlier actual recorded terminal/crossing stop of the two original tags, endpoints included. Both actual waits are completed, so both include v. Their histories after v agree up to the earlier stop; the minimum can be computed over actual post-event states because all intervening stationary ticks increase d.

Every charged level lambda belongs to exactly one class:
* Immediate if d_v<lambda: the outgoing event at v crosses it downward (its preceding tick deficit >=lambda).
* Later if d_min^+(v)<lambda<=d_v: the first subsequent downcross of lambda matches it.
* Terminal if lambda<=d_min^+(v): that upward crossing remains unmatched through the earlier actual stop.

Let I_rough, L_rough, T_rough be the weighted energies of these classes, summing the allocated half contributions. The exact identity is
    E_rough,same-slot,off=I_rough+L_rough+T_rough.      (3)
This holds separately on any pair class, including small-q/small-q and mixed q. The diagonal is <=R. The weights need not both have occupied the charged earlier tick in their clipped slabs; the charge uses ACTUAL full true histories as a reference and only the original retained weight in the energy.

For each unordered pair and level, upward and downward crossings alternate. Match a charged upward crossing to its first later downcross if one exists. Distinct charged crossings cannot use the same pair-level downward crossing. At a selected event p with n actual original tags sharing the completed slot, there are binom(n,2) unordered pairs and p-3 downward levels per pair on the true tick step. Consequently
    I_rough+L_rough <= (1/2) sum_all_actual_slots (p-3) binom(n,2). (4)
The sum uses ALL actual full slots through the crossing event, not just retained rough ones. A sharper statement is the exact subset allocation of (3); (4) is a deliberately loose envelope. Unlike net recorded-state descent 2w-(p-1), the true-tick decrement 3-p includes cancellations of ascent inside the SAME wait. In particular (4) cannot be substituted for a bound on the earlier recorded matched L_shared without paying these cancellations. The factor 1/2 uses unordered pairs, while the energy contribution e counts both orders. No comparison to the prior full positive-drift quadratic ledger is implied.

Terminal levels are actual unmatched upward crossings since true pair birth. Distinct such levels for a given pair cannot repeat without a downcross, so T_rough is bounded by one half of the sum of the terminal deficit minus the minimum deficit over each actual common true suffix (and can be much smaller). This upper budget also is not known to be small. The stationary allocation does not magically absorb terminal surplus into past selected gain; when a long rough wait raises d and the common prefix ends before a compensating descent, its energy genuinely belongs to T_rough. That is a new precise obstruction to using only downward-crossing control for the small-q amplification. A useful next target is to exploit actual earlier-stop geometry, or continue matching in an explicitly permitted longer reference and pay the remaining terminal levels there, without assuming that the extension decreases their energy at the necessary rate.

## 5. Result and scope

The previous rough-anchor comparable gain transport remains valid. The stronger support (1) and delayed peeling (2) can be used before it (possibly with the previous narrower comparable class). The small-q problem is reduced to thick stationary cohorts with >m actual same-class companions already present ell ticks earlier. Instead of bounding q n_A^2 with a huge factor r/q, the exact pair-level identity (3) eliminates that ratio entirely, at the expense of retaining immediate, later and terminal weighted crossing ledgers. A sufficient estimate for rough same-slot retained energy is I_rough+L_rough+T_rough=o(XB u^3); separate bounds on these terms or a joint contraction are still open. The preceding heavy-balanced distinct-slot CROSS, low-r thick shared anchors, natural MED destination transfer, and natural full-positive matched-ascent budget remain unresolved. This is a new reduction, not a twin-prime proof.

## 6. Finite verification and initial bug correction

Standalone research/min_clock_rough_delayed_level_audit.mjs, corrected source commit 5a017dfb2b5621c41b439a9820f732b385f0dcba, exact readback blob e045995ae30302db9ec37cf3bf816461bbc6d910. An initial diagnostic at fe02b218 used a largest-factor-overwriting sieve instead of a least-factor sieve, producing spurious mostly empty occupations. That commit's numerical output is INVALID; the code was immediately corrected by preserving the first assigned factor and ALL results below are from the corrected source rerun. Do not use the initial numbers as evidence. No prior checkpoint depends on this new invalid intermediate diagnostic.

Run:
    node research/min_clock_rough_delayed_level_audit.mjs 4096 16384 65536
Actual corrected function executed in available JS runtime (not separate Node invocation), 3 X times 2 modes times 2 occupations=12 combinations. Literal smallest-prime parity-gcd replay, checks original cutoff, waits, true deficit, exact arithmetic slot progression envelope, reference tag weights, three-class shifted thin gate, separate ratio/delay/thin linear loss, same-slot projection and exact pair-level partition, and aggregate downward injection bound. For up to 128 pairs per nonempty mode independently compares actual common recorded suffixes and scans every charged integer level for its first-slot/later/terminal fate. Floating-point fractional energies use tolerance. Analytic uses f=u^1/4, L=2 finite fallback, m=u^2.75 and eta=u^-1/4. Stress uses D=floor(B/4), L30,y5, f=4, m12, eta=1/8, not asymptotic parameters. The finite audit classifies small q with f as described; it does not use prior masks, does not measure the asymptotic sieve estimate, and only charges completed actual waits.

Largest X65536,B678, stress r>=43: 2595 eligible rough horizons, 3451 realized slots, sum_actual r=473263, relaxed arithmetic slot envelope69319 keys weighted6724523; ref R15464987, selected gain17722600. These finite envelopes are loose. Largest raw natural rough tick counts and reductions:
| occupation | raw ticks | ratio loss | delay loss | delayed thin loss | retained R |
|---|---:|---:|---:|---:|---:|
| late HIGH |607838|0|63534|12520|265892|
| full positive |7203839|0|708822|1189150|2652933.5|

Exact same-slot energy partition (does not include distinct-slot CROSS):
| occupation | diagonal | immediate | later | terminal | same-slot total |
|---|---:|---:|---:|---:|---:|
| late HIGH |144388.86|3608214.45|650536.39|8016425.52|12419565.21|
| full positive |1684430.40|43785565.22|14673439.97|86251078.28|146394513.87|

Largest late small-q/small-q offdiag5680633.59, matched2101857.45, terminal3578776.14; full-positive small-q offdiag95216758.75, matched40735492.35, terminal54481266.41. Distinct-slot cross44424.58 late and14797779.45 full positive. 205980 and1265882 actual pair-slot terms, 128 independent level-oracle pairs each. Untrimmed all-slot downward envelope before factor1/2 is528987854. Terminal is larger than matched for these examples, so the data explicitly shows why a downward-only charge is incomplete. Largest analytic mode has substantial linear loss (late 730886 raw ticks to 80481 kept; full positive 10170817 to313029 kept); analytic X4096 modes retain none. No numerical inference of negligible losses or full-energy contraction. Stress ratio deletion was zero in these six modes; analytic ratio deletion is nonzero, largest late14114/full68450 ticks. All final assertions pass.

Next: exploit earlier-stop geometry and true-level terminal budget, plus independent control of immediate cancellation (which is NOT recorded net descent) and later matched sectors. Consider longer actual reference matching within the original cutoff, with explicit separation between new reference and charged natural occupation. Preserve current branch and all other lanes; main untouched.
