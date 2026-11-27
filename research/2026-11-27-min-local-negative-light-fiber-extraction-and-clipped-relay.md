# Negative MIN: light-fiber extraction, clipped age frontier, and mass-capped relay sieve

2026-11-27 JST. Continuation of [66f63e3](https://github.com/tara-sooo/A166944-Lean/commit/66f63e372292963ae07b70ae73f63358387d176a). User asked how to prove from the current point. This develops an alternative to proving dominant departure phases, then replaces a global endpoint entropy target by a clipped merger potential, and actually transfers the positive MIN three-condition source sieve to a mass-capped negative ensemble. The remaining estimates are identified below; no complete twin proof.

## 1. Unconditional light-fiber long-dwell extraction

Use the synchronized all-root ensemble of 66f63e3, A uniform over N canonical roots in [R,2R], T=ceil sqrt(2R+1), observation U uniform on the T postticks of its window, endpoint Y=Y(A), global fiber size m(Y). Let X=X_U(A). Each root visits any center at most once. The observed stationary segments have integer lengths ell_i, pi_i=ell_i/T, summing to one. Define
    H_path=E_A[-sum_i pi_i log pi_i]=H(X|A),
    L_end=E log m(Y).
For large R all visited x lie in the positive halo I from the prior notes, and gain <=3T+6.

Fix a mass cutoff M>=1. A light root means m(Y)<=M. At a fixed center x, absolute clock and window J, all roots there have the same future and endpoint. Thus at most M light roots occupy this state. Since at most B0=O(1) windows can visit x, averaging over ticks gives the exact bound
    sum_{A light} Pr(X=x|A) <= B0 M.                       (1)
No departure-phase sparsity is needed.

Put L=log R, 0<alpha<1, P=T exp(-L^alpha)/2. A segment of probability pi_i>=exp(-L^alpha) satisfies q(x)>=P by ell_i<=2q(x). The non-twin centers in I with q(x)>=P are
    << R(1+log^+(S/P))/log^3 R <<_alpha R/L^(3-alpha).     (2)
This follows from the proof of the previous dwell sieve (66f63e3, section 2): for large R, P>=R^.4. If x is non-twin, q(x)=p<=S and one composite neighbor is p*r with r>=p prime. At fixed p and sign, the two-root upper sieve gives O(R/(p log^2 R)) possible centers (the residue-modulus version is stronger than needed here). Sum over p in [P,S] by dyadic prime upper counts. There are O(1+log(S/P)) bands and the harmonic prime sum per band is O(1/log R). This is a COUNT, not the weighted soft capacity.

An observed twin center cannot have a completed outgoing event before retirement: both eligible labels are the neighboring primes, of order R, so even one such jump would violate the gain cap. Every root visiting a twin center ends there. Hence the event “light root, non-twin endpoint” contains only visits to non-twin centers. Its long-segment root-time mass is at most B0 M times (2) divided by N by (1). Its short-segment mass is at most H_path/L^alpha. In fact the entropy numerator can be restricted to that cohort. Therefore, unconditionally,
    Pr(m(Y)<=M, Y non-twin)
      <= H_path/L^alpha + O_alpha(M/L^(3-alpha)).          (3)
This directly turns a joint entropy control into twin endpoints, without controlling H(V|X,J) or requiring terminal occupation separately.

For fixed beta>0 with beta+alpha<3, take M=floor L^beta. If a positive fraction delta of roots is light and H_path=o(L^alpha), then at least (delta-o(1))N roots end at twins, among light fibers. There are consequently >> R/L^beta DISTINCT twin centers in I along these slabs. One can restrict the H_path hypothesis to the light roots, using the nonnegative unnormalized cohort entropy in (3).

In particular:
    L_end <= (2+o(1))loglog R,
    H_path=O((log R)^gamma) for some 0<=gamma<1
on the SAME unbounded slabs suffice for twin infinitude. Indeed choose gamma<alpha<1 and 2<beta<3-alpha; Markov gives Pr(light)>=1-2/beta-o(1). For each fixed 0<epsilon<1-gamma one may choose beta=2+epsilon and an appropriate alpha, giving the quantitative lower bound >>_epsilon R/log^(2+epsilon) R in those slabs. The case of gamma<0 is already covered by gamma=0. Both actual asymptotic hypotheses remain open. This is a wider time-entropy allowance than requiring bounded or o(loglog R) phase entropy; it does not assert logical equivalence of the old and new sufficient conditions.

## 2. Use the age frontier to avoid the global endpoint entropy hypothesis

Let c_M(t)=min(t,M) for M>=1. In each actual synchronized window, follow the merger forest of 735c8e6. A node with incoming masses m_i and outgoing m=sum m_i loses
    C_M(v)=sum_i c_M(m_i)-c_M(m) >=0.
Births have mass one and components never split. Telescoping the clipped mass, rather than f(t)=t log t, gives the exact identity
    sum_v C_M(v)=N-sum_{J,y} min(m_J(y),M).                  (4)
Here m_J is the terminal mass within window J. The clipped loss is zero whenever the combined mass does not exceed M. The inequality
    C_M(v)<=sum_{i != i_max} min(m_i,M)                      (5)
follows by c_M(m)>=max_i c_M(m_i).

Choose age cutoff u and M=M_u=1+floor((2u+6)/6). Use the young/old split of 735c8e6: a group is young when every root had age <u just before the tick, births are young, old status is permanent. At a node total young mass Y_v<=M_u, total old O_v. Thus the internal young clipped loss is zero. The mixed clipped loss c_M(Y_v)+c_M(O_v)-c_M(Y_v+O_v) is <=Y_v, and nonzero only at genuine mixed nodes. Define lambda_u=N^-1 sum_{mixed v}Y_v, and
    A_cap(u)=N^-1 sum_{v with >=2 old groups}
                  sum_{old i != largest old} min(m_i,M_u).
Then (4),(5) imply
    N^-1 sum_{J,y} min(m_J(y),M_u) >= 1-lambda_u-A_cap(u).  (6)
It also suffices to use the actual two clipped losses, which are smaller than this bound. The usual age-frontier minority mass is an upper bound for A_cap, but uncapped majority mass and rank entropy are NOT needed.

At most B0 windows contribute to a global endpoint y. Hence
    sum_y min(m(y),B0 M_u) >= sum_{J,y} min(m_J(y),M_u).
If lambda_u+A_cap(u)<=1-delta for some fixed delta>0, the right side is >=delta N. Fibers larger than 2B0 M_u/delta contribute at most delta N/2 to the left side. Thus at least delta/2 of roots have m(Y)<=ceil(2B0 M_u/delta). This last implication only uses positivity of clipped mass.

Combine with (3): for fixed beta>0, 0<alpha<1, beta+alpha<3, set u=floor L^beta (u<=T eventually). It suffices to prove, on common unbounded slabs,
    lambda_u+A_cap(u)<=1-delta,
    H_path=o(L^alpha).                                    (7)
No bound for the entropy of very heavy endpoint fibers is required. This does not claim that the first line of (7) is established asymptotically; it localizes the needed collision control to the actual clipped minority traffic and young-to-old contacts. One may instead prove directly a positive lower bound for the clipped retention in (4).

## 3. Relate time entropy to actual outgoing labels

Give every observed stationary segment its actual outgoing completed prime p_i or the proxy S for terminal. Then
    H_path = E sum_i pi_i log(T/p_i) + E sum_i pi_i log(p_i/ell_i).
Each ell_i<=2p_i (for terminal use ell_i<=T and p_i=S). Also sum_i p_i<= (3/2)(3T+6)+S by the total gain bound, so Jensen applied to the second sum gives an upper bound log(sum p_i/T)=O(1), and the lower bound is -log 2. Hence
    H_path = E sum_i pi_i log(T/p_i)+O(1).                 (8)
The terminal contributes only O(1). To prove the second line of (7) it suffices to control the time-weighted log deficit of actual nonterminal labels, not the total number of ticks or uniform counts of short events. Also H_path<=E log(1+N_event), so sublinear powers of log R for that latter average would suffice for the special beta=2+epsilon route.

## 4. Actually transfer the direct-arithmetic three-condition sieve with the inherited mass cap

Fix epsilon>0, c>0 and K>=2, P>=R^epsilon/2, P<=C sqrt R. Consider a negative source jump p in [P,2P) followed by the FIRST completed jump r>=P, with r<=KP. All intervening labels are <P and their total gain is E. Require E<=B<P-3 and the observed source segment length ell>=c p. In a given source tuple write x=p*u+e and next high source y=r*v+f, e,f in {-1,1}. Then
    y=x-(p-1)-E,
    rv=p(u-1)+a, a=e+1-E-f.                               (9)
The integer a is odd (E is even), nonzero and |a|<=B+3<P<=p; consequently p!=r and rv=a mod p is a nonzero modular hyperbola. The source wait implies q(x)>=cp/2. For all sieve primes l>3 with l<min(P,cp/2),
    r !=0 mod l, rv != a-p mod l, rv != a-p-2e mod l.       (10)
The two product residues differ by 2e, even if one is zero. Thus the local forbidden count on F_l^2 is precisely 3l-2, identical to the positive MIN source-sieve proof in [14c6176](https://github.com/tara-sooo/A166944-Lean/blob/14c6176473bd6b30599d06a02e49cc2679c227ae/research/2026-11-26-min-direct-modular-hyperbola-three-root-source-sieve.md).

For fixed p,e,f,E, reuse sections 2–4 of that proof, with r in [P,KP], v in [1,O(R/P)], congruence rv=a mod p. Its elementary Kloosterman estimate, progression Fourier bounds, and Selberg weights apply verbatim because a is nonzero mod p and the local forbidden count is identical. The long side R/P is >=a fixed positive multiple of p since P<=C sqrt R. The old error bound is uniform with this constant; choose sieve cutoff P^(1/64), eventually below cp/2. It gives O_{c,K,C}(R/(P log^3 P)) surviving integer pairs. Each fixes x by (9). Sum over p by the prime upper count O(P/log P), e,f and even E<=B, to obtain
    # candidate source tuples <<_{c,K,C} R(B+1)/log^4 P.   (11)
There is no inherited-mass assertion in the source sieve itself.

Here is the actual mass transfer. Restrict to roots with global endpoint mass <=M. At any firing phase (x,n,J), all such roots which observe the segment ending at that firing share the same endpoint, so their number is <=M. Even if their entry times differ, all of their observed durations are <=min(T,2p). For fixed source x,p, eligible firing times are spaced by 2p, so O(1+T/p) occur per window, and at most B0 windows are possible. Their TOTAL normalized time weight on the light cohort is O(M) because (1+T/p) min(1,2p/T)=O(1). This is the needed inherited-mass cap that was absent from the previous attempt to transfer the positive source estimate. Thus (11) gives
    root-time fraction of the specified light-root pairs
       <<_{c,K,C} M(B+1)/log^4 P.                          (12)
Sum over dyadic P between R^epsilon/2 and O(T), giving
    <<_{epsilon,c,K,C} M(B+1)/log^3 R.                    (13)
With M=O(L^beta) and B=floor L^b for fixed b>0, beta+b<3, this is o(1). The proof is unconditional, counting actual synchronized observed source weights, and allows arbitrary early history and actual inherited light mass.

## 5. Use (13) to reduce the remaining time-control obstruction

Take M=O(L^beta), beta<3, choose alpha in (0,1) with beta+alpha<3, and Pmax=T exp(-L^alpha/2). On the light NON-TWIN endpoint cohort, (1),(2) already bound the long-segment mass by o(1). Short terminal segments contribute <=exp(-L^alpha). Short nonterminal segments with p>Pmax contribute at most
    O(T/Pmax)*exp(-L^alpha)=O(exp(-L^alpha/2))
per root, because sum p=O(T). Thus time on this cohort is, up to o(1), on completed p<=Pmax. No finite-twins assumption is needed for this assertion.

Fix 0<epsilon<1/4. All first-use p<R^epsilon consume at most O(R^(2epsilon)/T)=o(1) time per root (sum distinct p and ell<=2p). Denote the remaining repeated-small time fraction on the light cohort by sigma_rep. For a medium source label R^epsilon<=p<=Pmax take P=2^floor(log_2 p), its dyadic lower edge. Its next completed r>=P may be absent. There is at most one such last source per band; sum its p over bands is <=4Pmax. Their root-time is o(1).

If the next r exists but r>KP, charge source p to that successor. A successor can receive at most one charge from each band. Sum of charged source p over bands with P<r/K is <=4r/K by a geometric series. Sum over successors and use sum r=O(T): all these scale-up source waits contribute O(1/K). Sources with ell<c p contribute O(c). The remaining sources have a comparable successor r<=KP and ell>=c p. For their short relays E<=B, (13) proves total light time o(1). Hence the only remaining medium source time is on pairs with relay E>B.

Define Lambda_{M,epsilon,B} as total root-time fraction on light roots with R^epsilon<=p<=Pmax, a next completed r>=P, and E>B, without further restrictions on comparable size or minimum wait. All these fractions are normalized by the FULL N and T, not conditional on the cohort. Then
    Pr(light and Y non-twin) <= sigma_rep + Lambda_{M,epsilon,B}
                               + O(c+1/K)+o_{epsilon,c,K}(1).       (14)
Choose fixed c arbitrarily small and K arbitrarily large before taking R to infinity; it follows that limsup of the left side minus sigma_rep minus Lambda is <=0. This is an actual application of the new mass-capped sieve, not a claim that comparable relays dominate unconditionally.

There is one further deterministic restriction on Lambda. Choose z=a0 loglog R with fixed 0<a0<b. The uniform primorial boundary width 2 prod_{3<=p<=z}p is log^(a0+o(1)) R, by the prime number theorem. If every intervening relay label were <=z, the monotone negative path could not leave that primorial cell, by e173792, and E would be at most its width, eventually <B. Thus every source counted in Lambda has an intervening label in (z,P). This separates the two remaining difficulties: repeated labels below R^epsilon and medium-label excursions with a genuinely intermediate relay. Neither the height budget nor static barrier theorem bounds their TOTAL weighted occupation by a small constant: E>B may be much smaller than p, so the gain needed per long relay can be negligible. Simply charging B to each pair cannot establish the necessary contradiction. Proving a bound on this weighted occupation, or using (8) to prove (7), remains open.

In particular if the clipped retention in (6) stays >=delta and M is chosen as ceil(2B0 M_u/delta), it suffices to show sigma_rep+Lambda <=delta/2-eta for some fixed eta>0 on the same unbounded slabs. Equation (14) would then force at least eta-o(1) roots ending in light twin fibers and >>R/log^beta R distinct twins. This is an alternative to the time-entropy bound (7), uses the actual mass-capped arithmetic estimate, and does not require an endpoint entropy upper bound or a dominant-phase hypothesis. No such uniform bound is proved here.

## 6. Verification

A. [Light dwell, source-pair and scale-charge audit 3fe80b6](https://github.com/tara-sooo/A166944-Lean/blob/3fe80b61eb9094e11011580dd4dbfaf450d27001/research/min_local_negative_light_fiber_long_wait_audit.mjs), blob 8e6f8278a7ac2c7f7f16d06af32250c24ac6e40b. Executed as ECMAScript before commit and exact remote reexecution. Four slabs R12000/48000/192000/480000, 122004 roots, 2641688 root events, 119874 counted arithmetic/light-mass checks and 390675 geometric scale-charge checks; additional per-root height/entropy assertions. Checks (1), long-dwell counts and twin termination, (8), (9),(10) for specified small sieve primes, mass per phase/source tuple, and last-band/scale-up charge bounds. Does not independently verify the analytic asymptotic Selberg sieve. First attempted script construction hit JS exponentiation syntax error before execution or write; fixed before the first commit. At R480000 cutoff M326 all roots light, fraction ending at twins .8179773, H_path=.8152851, label-deficit mean .6251263. For alpha=.25 actual long non-twin mass .213745, long twin .641021, short .145234. The crude finite bound B0 M count/N is >1 (164.1), so no numerical deduction from (3) at these slabs. Scale partition K=4/8/16 on the tested low-to-medium cutoff p>=5 (NOT asymptotic R^epsilon): total .223417, last .104620, scale-up .039003/.017129/.007343, long relay .062435/.079316/.086508. These are finite diagnostics.

B. [Clipped age frontier audit adfbc2e](https://github.com/tara-sooo/A166944-Lean/blob/adfbc2ef07ce8f242c52fabd7bd8f79e299a0171/research/min_local_negative_clipped_age_frontier_audit.mjs), blob ec04106df609aaf482eed148b39daa66022867ed. Executed as ECMAScript before commit and exact remote readback. Six slabs R12000..2e6, 622004 roots, 2110844 occupied-component jumps, 555743 actual merger nodes, 4336567 counted checks plus clipped-potential integer assertions. Uses same clock and independently replays per-root endpoint multiplicities with that clock. First script-generation attempt had a parenthesis syntax error, fixed before writing. At R=2e6:
    u       M_u   clipped retention  actual clip loss  lambda+A_cap
    1       2     .10296910          .89703090          1.13688414
    14      6     .24974125          .75025875          1.14865015
    55      20    .55468255          .44531745           .97825898
    210     72    .92185892          .07814108           .63877564
For u210 the actual light threshold calculated by the retention proof is 938, and every root at this finite slab is light under that threshold. No uniform retention bound from these values.

All exact remote content verified; scripts not run in standalone Node or Lean, no independent mathematical referee. No main or sibling modifications. The proposed proof route now has two quantitative paths: (3)+(6)+(8), or (6)+(12)–(14). To complete one must actually establish positive clipped retention and a time entropy or remaining weighted relay/repeat occupation upper bound. This is not yet an unconditional proof.