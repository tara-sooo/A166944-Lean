# Negative MIN: multi-intermediate CRT relays and weighted live-retention criterion

2026-11-27 JST. Continuation of [769ef28](https://github.com/tara-sooo/A166944-Lean/commit/769ef2833eb0538f450bcc698c326917a0192e86). The requested objective is an unconditional proof of twin infinitude, not just finite tests. Here the previously uncontrolled relays containing intermediate labels are analyzed by reconstructing a whole bounded word of such labels, including repeats and fast interruptions of the low-only terminal map. A growing word-length bound is proved. Apply it to a new additive weighted cost, and then to the time integral of an online capped cohort, including discarded histories, not merely the endpoint. Finally derive a power-of-log decaying-retention criterion and an early-loss consequence under finite twins. The positive lower bound for live retention remains open.

## 1. Conventions and previous inputs

Canonical A in [R,2R], 6|A, birth n_A=3-A/2, N~R/6. Put L=log R, S=sqrt(2R+1), T=ceil S. We allow synchronized observation horizon T'=T or T'=floor(T exp(-L^delta0)), 0<delta0<1 fixed. Window width W=6 floor(T'/6), latest birth n0, retirement n0+T', observation [n0,n0+T') of T' postticks. Full age through retirement <=3T'/2 and gain <=3T'+6. At most B0=ceil((3T'+6)/W)+2=O(1) windows can visit the same x. Centers lie in the positive expanded slab I from lo-3T'-6 to hi.

Each actual completed label p is an odd prime factor of x-e, e=-1 or +1, and x becomes x-p+1. At firing n, for e=-1 (even) n=0 mod 2p; for e=+1 (odd) n=p+2 mod 2p. Postheight h=n+(x-p+1)/2 satisfies h>=0, h=0 or3 mod p, and h=O(T'). A root visits a center once; any stationary segment has length <=2q(x), q=min(lpf(x-1),lpf(x+1)), and <=2p if completed with label p. Sum completed p=O(T') per root.

Previous inputs from [66f63e3](https://github.com/tara-sooo/A166944-Lean/commit/66f63e372292963ae07b70ae73f63358387d176a) and 769ef28: non-twin dwell capacity
    sum_(x non-twin in I) min(1,2q(x)/T')
       << R(1+log^+(S/T'))/L^3.                              (1)
At fixed p and sign, sources with q(x)>=p^d/2, 0<d<1 fixed, have count O(R/(p log^2 p)) for p>=exp(c L^gamma), gamma>0 fixed. The source phase weight cap M implies source time at p>=Pmax=T' exp(-L^alpha), alpha<1,
    << Pmax^(d-1)+ M(1+L^alpha)/L^3.                        (2)
Here and below fractions are normalized by the FULL N and T', and M is a positive integer cap. The proof of (2) is the fixed-p two-form sieve and harmonic prime sum, with p<=O(T') and log p~L in this band. Fast source segments ell<p^d contribute O(Y^(d-1)) per root for p>=Y by sum p=O(T'). These inputs are valid with the new T' (R^.45<=T'<=T eventually), not only T.

## 2. Exact reconstruction for a bounded INTERMEDIATE WORD

Let 3<=z<Y, Q_z=2 product_(3<=q<=z) q. In a consecutive Y-high pair, source p>=P>=Y at x=pu+e, successor r>=Y, all intervening labels <Y. Suppose exactly j of them are >z. Denote their ordered labels q_1,...,q_j, signs e_i, and the number a_i of <=z events immediately before each q_i. Repeated q_i are allowed. The last <=z run ends just before r.

Fix p,e,source postheight h and source residue b=x mod 2Q_z. The initial poststate is x-p+1,n=h-(x-p+1)/2. At each <=z run the restricted MIN containing only labels <=z is periodic in position and clock mod Q_z, follows the actual <=z prefix, and terminates inside its initial common-multiple cell. Thus its gain <Q_z, event count <=Q_z/2 and elapsed time <=3Q_z. For fixed a_i its prefix (if it exists) has fixed gain and elapsed time on the current residue progression. This is true even when the next intermediate event interrupts the low-only run BEFORE its terminal.

Inductively suppose the current state before the next low prefix is x-g,n+t with fixed g,t on the progression. After taking its prescribed prefix, still write the updated state x-g,n+t. The spatial eligibility of q_i is
    x = g+e_i mod q_i.                                      (3)
If q_i has not appeared before, this pins a unique new residue class mod q_i by CRT; if repeated, either the previous pin agrees or there are no valid candidates. Since 2Q_z is divisible by 4, the now-fixed x mod 4q_i also fixes n+t mod 2q_i, so the actual first clock of that label is uniquely determined. Add that wait to t and q_i-1 to g. Ignore other competitors when counting candidates: every actual pair is included. Thus for each word, signs and prefix counts there is at most ONE progression
    x mod m, m=2Q_z product_(distinct q_i) q_i,              (4)
and all relay gains and elapsed times through the last intermediate event are constant on it. No factor q_i is charged for a repeat. Source p>=Y is coprime to m.

If the final successor has full wait w_r>2z, the last <=z run equals the entire restricted terminal map, so no final prefix count is needed. Otherwise one may prescribe a final prefix count, again <=Q_z/2. In both cases total relay gain E satisfies
    E <= j Y+(j+1)Q_z.                                      (5)
When all intermediate waits exceed 2z, each preceding <=z run is also terminal, so ALL intermediate prefix counts can be omitted. This is a second regime with larger z. If even one intermediate wait is small, the terminal-only reconstruction would not be valid; the arbitrary-prefix variant is the safe alternative.

## 3. Sieve all reconstructed pairs, slow and fast successors

Take fixed exponents 0<gamma0<=gamma1<1, Y=exp(L^gamma0) (constant positive multiplier in the exponent is harmless), P>=Y, log P comparable to L^gamma1. For the symmetric case below use P=(k+2)Y with gamma1=gamma0. Choose j<=k=k(R) with k=O(log L), Q_z<=Y^nu for fixed small nu<min(1/2,1-d), and kY+(k+1)Q_z+3<P. For P=(k+2)Y this holds eventually if Q_z=o(Y/k). Then E<p-3 for all source p>=P. Consequently r!=p: otherwise r=p would require E=e+1-f mod p (odd residue -1,1 or3), incompatible with even E in [0,p-3). Also r>=Y>q_i, so r is coprime to m.

For any j and set of repeated-index positions, the sum over q words of 1/product(distinct q_i) is <=(j+1)^j(1+sum_(z<q<Y)1/q)^j; encode which previous index is repeated or a fresh index, then sum each fresh prime harmonically (allowing duplicates only enlarges). Thus after the signs and prefixes, the total combinatorial factor is bounded by
    A_k = (k+1)[C(Q_z+1)(k+1)(1+log L)]^k                  (6)
for arbitrary middle waits, and by the same expression without Q_z+1 in the bracket when all middle waits >2z. The constant C is absolute. This estimate uses Mertens or its elementary harmonic upper bound. Repeated-index patterns are not treated as independent primes. Also m<=2Q_z Y^k=R^o(1).

Slow source and slow target: observed (possibly truncated) source ell>=p^d, target full wait w_r>=r^d>2z. Both neighbors of each center are rough at the corresponding p^d/2 and Y^d/2 thresholds. For fixed word, signs, prefix indices, p,e,h,b, (4) and p|x-e give a progression of step p*m of length scale R/(p*m)>>R^(1/2-o(1)), on which y=x-(p-1+E) with fixed E. Sieve x±1,y±1: at primes <=Y^d/2 use four linear forms, at larger primes <=p^d/2 use the two source forms. Omit primes dividing the modulus, 2,3,5, or the nonzero discriminant D(D^2-4) with D=p-1+E>=p-1. The last is nonzero and size R^O(1) for actual p,E. Its extra singular factor is bounded by (log L)^C, by splitting prime divisors at L and using Mertens below L. The omitted intermediate primes cost at most exp(O(k/z)) (for z>=7); the same bound with O(1+k) holds if z fixed. For our choices below this is bounded. The omitted <=z primes cost (log(z+2))^4. Use the same explicit Selberg diagonalization and truncated Euler-product Markov argument as 769ef28 section 8, with level p^c, sufficiently small fixed c depending on d. Error O(p^(6c)) is negligible against R/(p*m); main reciprocal product is at least a constant times (log p)^2(log Y)^2 divided by (log(z+2))^4(log L)^C. Thus the count on this progression is
    << R/(p*m) * (log L)^C/[(log p)^2(log Y)^2].             (7)
All count constants and exponents C may be taken fixed, independent of the word and k, for the chosen regimes. The discrimination factor and z omission are absorbed in C. No uniformity of full dynamic histories in large CRT moduli is used; the progression is specified explicitly and its length is of power size in R.

Source postheight has O(T'/p) options, since p<=O(T'); its phase time weight is O(M p/T'). These cancel. Sum b over O(Q_z) residues, canceling that part of the modulus. Sum words with (6) and source p by sum_(p>=P) 1/(p log^2 p)<<1/log^2 P. Therefore the fraction of such pairs, with arbitrary source and target scale, is
    << M A_k (log L)^C /[(log P)^2(log Y)^2].              (8)

Fast target: w_r<r^d. Prescribe its final low-prefix count (factor <=Q_z/2+1), unless it is already fixed. On the reconstructed progression the target prestate height b0 at its current clock is fixed, since the x terms cancel from n+t+(x-g)/2. For every candidate wait w in [1,(2V)^d] when V<=r<2V, the target prime r must divide
    H=2(b0+w)+1   or   2(b0+w)-5.
For an actual target H>=r-6>0, H=O(T'); discard candidates violating these necessary bounds. So for fixed w and sign only O(L/log V) prime factors r>=V are possible. Spatial pin at r adds one CRT congruence, coprime to p*m. The count is O(R/(p*m*V)+1). For V<=R^(.2), the plus-one term is absorbed because p<=O(sqrt R), m=R^o(1). Sum the reconstruction choices as in (8), now without roughness factors, and use sum_p 1/p=O(log L). Per target dyadic band this gives
    << M A_k (Q_z+1) (log L) * L V^(d-1)/log V.            (9)
Summing the O(L) bands V>=Y is o(L^-C0) for every fixed C0 if Q_z<=Y^nu, nu<1-d, and A_k polylog R. For V>R^(.2), ignore the intermediate congruences in the spatial count, keeping only p,r; p*r=O(R) and p!=r, giving O(R/(p*V)). The TOTAL number of reconstruction choices including residues, signs, words and prefix indices is at most (2Q_z)(Q_z+1)(k+1)[C(Q_z+1)Y]^k=R^o(1). Thus even this crude count yields a factor V^(d-1) R^o(1), power-saving. This separate treatment of the CRT remainder is essential at the square-root scale; it is not valid to absorb +1 uniformly into R/(p*m*V).

The fast SOURCE time is negligible as in section 1. Combining (8),(9), ALL sources p>=P of consecutive Y-high pairs with at most k intermediate events >z are negligible whenever the right side of (8) is o(1), including repeated intermediate primes and arbitrarily fast intermediate waits. The special all-slow-middle regime uses its smaller A_k. This extends the previous all-small-relay estimate (no intermediate events).

## 4. Choose a genuinely growing word budget

Let M=floor L^beta. Fix a small epsilon1>0 with beta+epsilon1<2(gamma0+gamma1).
For arbitrary middle waits use
    z=floor sqrt(log L) (at least 7),
    k=floor[epsilon1 log L/
             (log(2(Q_z+1))+2log(2log L))].
Then k=Theta(sqrt(log L)), using the prime number theorem for log Q_z~z, and A_k<=L^(epsilon1+o(1)). All assumptions of section 3 hold, and the slow pair bound is
    L^(beta+epsilon1-2(gamma0+gamma1)+o(1)).                (10)
Fast target/source errors are smaller than every fixed negative power of L.

For the all-middle-waits>2z variant instead take z=floor(c0 log Y), with Q_z<=Y^nu by sufficiently small c0>0, and k=floor(epsilon1 log L/[3 log(2log L)]). Then k grows like log L/loglog L, and the smaller A_k<=L^(epsilon1+o(1)). This retains the previous much larger lower band cutoff z~L^gamma0. Its exception includes a single fast intermediate; it is NOT a bound for all intermediate words at this larger cutoff. One can also interpolate z,k with k z+k loglog L small relative to log L.

For the symmetric arbitrary-wait version choose 2<beta<9/4, beta/3<alpha<3-beta, gamma0=gamma1=alpha and P=(k+2)Y. The omitted bottom source band [Y,P) has time O(M (1+log(k+2))/log^3 Y)+O(Y^(d-1))=o(1) by the ordinary two-form source sieve. (The extra requirement beta<3alpha is needed for this omission.) Consequently on a capped non-twin cohort the prior estimate of 769ef28 improves to
    |C_bad|/N <= o(1)+O(e^(-L^alpha) E_Cbad^* K/(k+1)),    (11)
where K counts labels z<p<Y, E^*=sum/N. Indeed discard terminal, p>=Pmax, last high, and all pairs with <=k middle events. Every remaining disjoint relay has >=k+1 such events, so charge the source time <=2Pmax/T' to them. Low time <=O(Q_z/Y)+O((Y+Q_z)K/T'), negligible relative to the displayed coefficient of K. This allows K=o((k+1)exp(L^alpha)) instead of o(exp(L^alpha)), but the lower band cutoff is smaller than the one in 769ef28; it is not a uniform improvement of that earlier condition. In the all-slow-middle variant, charge either one fast middle event or k+1 slow middle events. Both estimates still require an actual trajectory budget bound.

## 5. Asymmetric weighted additive cost (use the new pair estimate again)

Now separate three scales:
    Y0=exp(L^gamma0), Y1=exp(L^gamma1), Pmax=T' exp(-L^alpha),
    0<gamma0<gamma1<1, 0<alpha<1,
    beta+epsilon1<2(gamma0+gamma1), beta+alpha<3.
Use the arbitrary-wait reconstruction at Y=Y0, P=Y1, z,k of section 4. Since gamma1>gamma0, the source threshold exceeds kY0+(k+1)Q_z+3 eventually, without omitting a bottom band. Define for each root's actual full history through retirement the nonnegative additive cost
    C_R(A) =
      [e^(-L^alpha)/(k+1)] K_(z,Y0)(A)
       + (1/T') sum_(Y0<=p<Y1, q(x)>=p^d/2) 2 q(x),         (12)
where K counts all completed labels z<p<Y0 including pre-window events. Each term depends only on the actual source x and winning p at a completed firing. In particular using q(x), rather than the root's full wait since entry, ensures the cost increment is COMMON after a merger even for ancestors that reached the stationary block at different times.

For high sources p>=Y1: discard near-max p>=Pmax by (2), last Y0-high event by time <=2Pmax/T', and all short reconstructed relays by (10). Each remaining source is followed by its next Y0-high event with >=k+1 narrow-band events in between. These relay intervals are disjoint since consecutive Y0-high pairs are used, even though the source threshold is Y1. Their total time is bounded by 2 e^(-L^alpha) K/(k+1).

For low sources p<Y1: <=z runs each have gain <Q_z, number <=1+K+N_(>=Y0), and N_(>=Y0)=O(T'/Y0); narrow band gain <=Y0 K. The medium events Y0<=p<Y1 with q(x)<p^d/2 have waits <=2q(x)<p^d, so total time fraction O(Y0^(d-1)) by sum p=O(T'). All OTHER medium events have normalized dwell <=2q(x)/T', already paid in (12). Thus low time is bounded by
    O(Q_z/Y0+Q_z/T'+Y0^(d-1))
      + O((Y0+Q_z)K/T') + second term of (12).
The narrow coefficient (Y0+Q_z)/T' is o(e^(-L^alpha)/(k+1)) for any fixed exponents <1. No assumption on the number of fast medium labels, even if repeated, is made. This is better than charging every such event at the largest possible label.

Combining terminal and completed time yields
    |C_bad|/N <= B0-independent-constant * E_Cbad^* C_R + Err_R,    (13)
for every cohort capped at M per window endpoint. Here and below constants are fixed for the exponent choices. The term Err_R is bounded by
    O(M(1+log^+(S/T'))/L^3 + M(1+L^alpha)/L^3)
       + L^(beta+epsilon1-2(gamma0+gamma1)+o(1))
       + o(L^-C0)                                         (14)
for every fixed C0. The last term includes subexponential fast, last, low-run, and omitted-end-segment errors. Formula (13) for a non-twin endpoint cohort does not assume finite twins: a visited twin cannot jump before retirement under the gain cap, so such a cohort never visits a twin center. The weighted cost can be used in the previous exact greedy M-smallest list and budget threshold ledger, since it is additive and common at a firing. If gamma0<alpha, the contribution of first uses of narrow labels is <=e^(-L^alpha)Y0/(k+1)=o(L^-C0), uniformly per root. This allows interpreting the narrow cost as a repeated-event burden; the exact online algorithm uses total counts, not a root-specific repeat count.

## 6. Apply the same estimate to online LIFE, including all discarded roots

This is a stronger use of (13) than a final cheap cohort. Run ANY online policy: births introduce one token; tokens follow their actual MIN path; discard tokens irreversibly at any time, and keep at most M live tokens per occupied actual state (x,n,J). Policy may depend on actual past, and need not be greedy or know endpoints. Let d_A be the absolute discard time (retirement if not discarded). Define
    l_A = max(0,min(d_A,n0+T')-n0)/T',
    eta_live = (1/N) sum_A l_A.
All births occur by n0. This is the integral of the normalized live mass over the observation. If a root is discarded before n0 it contributes zero. Let C_R^pre(A) use completed events up through discard or retirement, including any event on which the token is discarded.

The phase capacity proof does NOT require a bound on the total number of different tokens entering a phase: at each physical tick at most M are live at x,J. For a given outgoing firing clock, every stationary interval ending there is contained in the preceding 2q(x) ticks (and preceding 2p), so their integrated live time is at most M min(T',2q(x),2p). A terminal block is contained in the last 2q(x) ticks before retirement; its integrated live time is at most M min(T',2q(x)). Thus (1),(2),(8),(9) and their normalized time estimates apply directly to live time, even though different tokens may be discarded/arrive in a phase. Do not bound the number of distinct visiting tokens by M; that claim would be false for an arbitrary online policy.

For each live prefix, when a high source is observed but its next Y0-high event is after deletion or absent, there is at most one such last source; discard its time <=2Pmax/T'. If an actual outgoing event has not completed before deletion, the final partial nonterminal segment is handled by the same last-high charge if high, or <=2Y1/T' if low. All other charged disjoint relay events are within the prefix and paid by C_R^pre. Low-run bounds remain valid on every prefix. The terminal twin time across all windows is at most B0 M times the number of twin centers in I, normalized by N. Hence, without assuming finite twins,
    eta_live <= (B0 M/N) #twins(I) + C E^* C_R^pre + Err_R,         (15)
where E^*=sum/N, with the same fixed constants and (14). This includes online cap or threshold deaths. Under finite twins the first term vanishes for all sufficiently large R.

Choose the greedy policy retaining at most M lowest costs, discarding any that exceed budget b_R. Its one-event cost increment is at most e^(-L^alpha)/(k+1)+2Y1/T'=o(L^-C0). Thus E^* C_R^pre<=b_R+o(L^-C0), counting the threshold-crossing event if it kills the token. The exact final cheap-retention identity of 769ef28 is still valid. The new sufficient criterion is **positive live time**, not positive final retention:
    eta_live >= delta>0, b_R=o(1) on unbounded slabs
implies >> R/L^beta twin centers there. A policy with zero terminal survival but many late deaths could still prove twins through (15). More generally eta_live is at least final retention, so this criterion weakens the former lower-bound task. The exact lifetime identity is
    eta_live = final retained fraction
             + (1/N) sum_(discarded A) l_A.                (16)
Equivalently it is one minus the normalized remaining observation time lost at each death. This distinguishes early losses from late ones; bounding their unweighted count alone discards this information.

## 7. Quantitative weak retention and early-loss consequences; try to close

A positive constant is not necessary. Fix sigma>=0 and choose
    beta+sigma+alpha<3,
    beta+sigma+delta0<3 (omit delta0 if T'=T),
    beta+sigma+epsilon1<2(gamma0+gamma1).
Then Err_R=o(L^-sigma). If budget b_R=o(L^-sigma) and the live-time fraction >=c L^-sigma along unbounded slabs, (15) forces >> R/L^(beta+sigma) distinct twin centers. The same conclusion follows from final cheap retention >=c L^-sigma. This statement does not demand a constant fraction of cheap trajectories. The twin upper sieve is consistent when beta+sigma>2. It would preclude the stated sufficient hypotheses at beta+sigma<2.

For instance beta=2.1, sigma=.25, alpha=.60, gamma0=.45, gamma1=.85, epsilon1=.10, delta0=.50 work: beta+sigma+alpha=2.95, beta+sigma+delta0=2.85, beta+sigma+epsilon1=2.45<2.60. The proof would yield >> R/L^2.35 distinct twins from live fraction of order L^(-.25) with budget o(L^(-.25)). Narrow band lower cutoff z~sqrt(loglog R), upper exp(L^.45), count weight e^(-L^.60)/(k+1); all medium p from exp(L^.45) to exp(L^.85) are paid only through the rough dwell charge (12), with the short-q population free. This example deliberately uses gamma0<alpha so narrow first uses are negligible. More generally any 2<beta+sigma<8/3 admits such fixed exponents with gamma0<alpha<3-beta-sigma and gamma1<1 sufficiently close to1; choose epsilon1 small. This follows from beta+sigma<2(1+3-beta-sigma). The range is sufficient, not asserted optimal. M need not itself exceed L^2 if the retention is allowed to decay.

Under finite twins (15) forces eta_live=o(L^-sigma) for these budget/exponent choices. Since every token surviving to observation offset lambda T' contributes at least lambda to its lifetime, its surviving fraction <=eta_live/lambda. In particular for each fixed lambda>0 all but o(1) roots must have been discarded before that offset; even for lambda=L^-sigma when sigma>0 the same follows. Taking T'=T exp(-L^delta0) implies that for the corresponding narrower windows almost all roots die by age <=3T'/2, from either cap merging or budget exhaustion. This is an actual early-loss consequence of the previous weighted sieve, not merely a statement about endpoints.

Try to prove a contrary deterministic lifetime lower bound. The policy that prioritizes youngest roots (smallest A) at a merge guarantees survival of each root until age u=floor(3(M-2)), provided budget is not crossed: if a root of age <=u is removed, there must be M younger roots at that state. All their A' lie in [x,A], where A-x<=2u+6; the count of other canonical roots is <=floor((2u+6)/6)<M, contradiction. This uses actual trajectories, regardless of previous deletions. A budget cannot be crossed at age u for the displayed parameters and e.g. b_R=L^(-sigma-1), because completed gain<=2u+6, narrow event count <=O(u/z), medium dwell-cost sum <=O(u/T') and both are smaller than b_R. However this only guarantees age of order M. With window births spread across width comparable to T', the unconditional normalized lifetime lower from the latest O(M) births in each full window is of order (M/T')^2 (and one could use a different observation convention to get M/T', still too small). It is exponentially smaller in L than the required negative-power-log bound. The deterministic height/gain cap likewise gives only total narrow count O(T'/z), much larger than the allowed narrow budget. The simple capped phase supply count O(M T'/(z log z)) is also too large. Thus these actual closure attempts do not establish the live-time lower bound. The key remaining target is a lower bound for the cumulative lifetime of cheap capped histories (or the old endpoint retention), using arithmetic of genuine merger contacts and repeat traffic, not just height or finite CRT walls. No new unconditional twin proof.

## 8. Audits and limitations

Three scripts executed as actual ECMAScript functions before commit and on exact remote source after fetch. No standalone Node or Lean kernel, no independent analytic referee. These finite controls verify the arithmetic reconstruction and exact lifetime/cost ledgers, not the asymptotic estimates or parameter-scale retention lower bounds.

A. [Multi-relay CRT audit 500eef1](https://github.com/tara-sooo/A166944-Lean/blob/500eef15c7ceaba0891535b922d2b0320928655b/research/min_local_negative_multi_relay_crt_audit.mjs), blob 6c7b1d3e562ce06fd665a434cb3f0d2dff28755f. Four slabs R12000,48000,192000,480000; 122004 roots,2641688 root events,915521 counted controls,471172 overlapping source/target pairs,431507 reconstructed short words (k=3),23864 with repeated intermediate label,164873 with fast intermediate,332803 rough-form checks. Exact BigInt CRT class modulus, every middle wait and offset, final restricted terminal/truncated prefix, positive target height factor, disjoint long-relay charge verified. Fixed finite thresholds (z,Y0,P1)=(3,11,47),(5,23,97),(7,47,193),(5,47,193); not the growing parameters. Example A480000, source257,target31, middle [(7,1 preceding small event,wait14),(7,2 preceding small events,wait5)], E26, exact modulus420, target factor155. The second 7 is a repeat and a fast interruption; terminal-only relay reconstruction would be invalid.

B. [Live cheap-flow audit d8c81e3](https://github.com/tara-sooo/A166944-Lean/blob/d8c81e3f94869bcdaa5220ea91fe5c39dbf62ecd/research/min_local_negative_live_cheap_flow_audit.mjs), blob 6bb30066f07a32ea9ec881cbc8d84053e645f2b1. Same four slabs,122004 roots,2641688 independent root replay events,2325216 counted controls and520926 phase-cap checks. Fixed z5,Y47,k2, Pmax=T/2, four caps/budgets. Exact endpoint identity with full-root replay, every death, budget, interval integral, phase time cap, disjoint surviving relay charge and low prefix gain checked. At R480000 cap64,budget16, final retention .84546443 vs live .91645247; merger loss .02141223, threshold loss .13312334. Cap4,budget4 retention .17551031 vs live .21438985. All include existing twins. Different R and parameters from prior finite controls.

C. [Weighted live-flow audit 3f505db](https://github.com/tara-sooo/A166944-Lean/blob/3f505db8f7e23f2700af677f18d267db0cec5784/research/min_local_negative_weighted_live_flow_audit.mjs), blob 33881a10ab2d8e7e14a03bfcce5559bbaabf97b3. Same four slabs,122004 roots,2641688 root replay events,2091598 counted controls and357407 phase-cap checks. Finite z5,Y0=23,Y1=97,k2, exact integer event cost 8 per narrow event, 2q(x) per medium event with 4q(x)^2>=p, zero otherwise; these are finite proxy weights (d=1/2), not the asymptotic coefficients of (12). Exact weighted greedy selection and free short-q medium time bounds checked with all lifetime/relay caps. At R480000:
    M    integer budget   final retention  live fraction  merge loss  budget loss
    4    32               .14819815        .17962036       .31087111   .54093074
    16   128              .37199535        .44144527       .12222347   .50578118
    64   128              .41983225        .49390281       0           .58016775
    64   256              .63339208        .72325611       .00207497   .36453294
Last control actual observed medium time paid by rough cost .02547935, short-q medium .00004337, summed rough charge .13180621 (loose). All include existing twin centers; no asymptotic inference. T'=T in the finite audits; shortened observation horizon is derived analytically using the earlier uniform dwell sieve, not separately numerically tested.

Main and sibling branches unchanged. Full proof and Lean formalization remain open.