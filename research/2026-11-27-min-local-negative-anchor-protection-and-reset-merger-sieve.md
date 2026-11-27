# Negative MIN: protection across rough near-square anchors and short relays

2026-11-27 JST. Continuation of [5a22180](https://github.com/tara-sooo/A166944-Lean/commit/5a221805964d0d023f1577e066e67ec984d0aa66). The previous live-time inequality reduces twin infinitude to a cheap capped survival lower bound. This note attacks actual cap losses, rather than only strengthening that upper inequality. The new result is a protected class with o(N) (or power-log smaller) total merger deaths over the whole synchronized observation: young histories, and histories just after a rough near-square-scale event, including subsequent relays of small total gain. The proof uses actual postheight pins, a short-height-gap count, two different reset-pair sieves and a long-resident sieve. It then combines the result with budget threshold averaging and proves an unweighted successor restriction on protected anchors. It does not yet bound survival through the intervening unprotected portions.

## 1. Setup and the protected priority policy

As in 5a22180, put L=log R, T=ceil sqrt(2R+1), T'=T or floor(T exp(-L^delta0)), fixed 0<delta0<1. The synchronized window width is W=6 floor(T'/6), latest birth n0, retirement n0+T'. N canonical roots A in [R,2R], 6|A, born at n_A=3-A/2. Full age <=3T'/2, gain <=3T'+6, all centers in I of length O(R) and positive of order R. At most B0=O(1) windows can visit a given center. Completed p has wait <=2q(x)<=2p<=3(p-1), q(x)=min(lpf(x-1),lpf(x+1)), and total completed p=O(T').

At firing n, incoming source x becomes a=x-p+1. Let c=0 for even firing (minus source sign) and c=2 for odd firing (plus sign), and s(c)=0 or3 respectively. Actual arrival satisfies
    a=c mod p,     h=n+a/2=s(c) mod p,     0<=h<=O(T').      (1)
The source neighbors are p(u+1) and p(u+1)+2e when a=pu+c, e=c-1 in {-1,+1}.

Fix a>0, b>0, 0<d<1 (a is now the exponent in P, not a spatial coordinate), M=floor L^beta, P=T'/L^a, B=floor L^b, u=floor(3(M-2))-1. All inequalities below are for sufficiently large R. Call a completed event a ROUGH ANCHOR if
    p>=P,  q(source)>=p^d/2.
It is not assumed that every ancestor's wait is long: the property depends only on actual event source and winner. Every live token after such an event remembers its anchor (p,c,position v,time n_a,height h_a). It is high-protected as long as its cumulative gain from that post-anchor position is <=B, unless a new label >=P occurs, which supplies a new anchor if rough and otherwise clears the protection. This last convention does not matter before gain B is exceeded, since P>>B. Young-protected means not high-protected and age <=u. These classes are disjoint eventually since a high anchor costs gain >=P-1>2u+6. Use any cap selection giving high-protected tokens priority over young-protected, and both over unprotected; ties arbitrary. Budget deaths, if any, happen before cap selection. All tokens follow their actual trajectory until irreversible deletion.

At every merger group, each incoming live list has size <=M. If k groups contain high-protected tokens, the loss among them is <=M(k-1) and zero if k<=1. A single resident group is possible, and a birth cannot be high-protected. Choose one anchor representative per such group; representatives from different groups are necessarily distinct physical events because deterministic trajectories once coalesced never split. Charge the loss by at most M times the number of unordered pairs of representatives. A given pair of physical anchor events in the same window can be charged at most once, because their trajectories coalesce at the first contact and cannot subsequently separate. This counts losses, not arbitrary root pairs or full uncapped traffic.

## 2. Exact reset structure, and close-height anchor pairs

At a merger into position y at tick n, postheight h=n+y/2. If n is even and h=0, there is no resident: at n-1 its height would be -1. Birth has height3, so all incoming groups are moving. If n is odd and h=3, an existing resident must have last arrived at n-3 by an even firing into the same y at height0. Indeed its last arrival or birth must be in [n-3,n-1] by height nonnegativity. Birth cannot be earlier than n at this position. For an even last arrival, (1) requires its prime to divide 3-j for j=n-n_arrival odd, so j=3; for an odd last arrival j=2 and its prime would divide -2, impossible. In this case y is divisible by4. This is an exact reset-resident identity; no statistical hypothesis.

For two high-protected representatives meeting at (y,n), write their post-anchor positions v1=y+E, v2=y+F, 0<=E,F<=B. Let their anchor heights h1=k1 p+s(c1), h2=k2 r+s(c2), k1,k2>=0. At least one group is moving at the merger. Its representative has elapsed time <=3B since its anchor, because all post-anchor events up to arrival are completed and each wait <=3 times gain. Define D=ceil(P^d)+3B+4. If the other anchor is also of age <=D, then
    |h1-h2| <= D+B/2.                                     (2)
Both primes are >=P, so this is o(P). The spatial pins are
    y+E=c1 mod p,     y+F=c2 mod r.                        (3)

Same prime p=r is impossible for two distinct anchors in this close case. The pins give E-F=c1-c2 since their difference has absolute value <p. If signs equal, E=F and k1=k2 from (2), giving the identical poststate and clock. If signs differ, k1=k2, their postpositions differ by2 and their heights by3 in the same orientation; their absolute clocks then differ by2, contradicting opposite firing parity. Thus p!=r. Moreover either both k1,k2 are zero (singular pair), or both positive, since a single zero cannot give a height difference o(P).

For both positive, count candidate tuples directly. p has O(T') choices, k1,k2 have O(L^a) each. By (2) r lies in an interval of length O(P^d+B+1) for fixed p,k1,k2,c1,c2. For each E,F and signs, (3) gives O(R/(pr)+1)=O(R/P^2) possibilities for y. Each tuple fixes both firing times and sources. There are O((B+1)^2) offset choices. Thus the number of nonsingular close pairs is at most
    O(T' L^(2a) (P^d+B+1) R/P^2 (B+1)^2)
      = R^((1+d)/2+o(1)).                                 (4)
This is power-saving even for shortened T'. No roughness sieve is needed for the nonsingular case. The multiplicity from windows is bounded by B0.

## 3. Singular pairs: equal shifted pins versus modular hyperbola

Now h1=s(c1), h2=s(c2), and p!=r. Both source neighbors are rough to at least P^d/2, a polynomial power of R. Fix E,F,c1,c2. The shifted product relation is
    p U=y+E-c1,   r V=y+F-c2,
    p U-r V=Delta=E-F-c1+c2.
The source centers are p(U+1)+e1 and r(V+1)+e2, with e_i=c_i-1. Here |Delta|<=B+2<<P; both cofactors are positive of order at most O(R/P). Split p,r into dyadic bands X<=p<2X, Z<=r<2Z, X,Z>=P/2, both <=O(T'). There are O(log L) bands because T'/P=L^a. We show a uniform upper count
    O(R L^-6 (log L)^C)                                   (5)
per band pair and fixed offsets/signs. Use the fixed-dimensional Selberg diagonalization from 66f63e3 and 769ef28: for one-variable progressions with g(l)=k/l outside exceptional primes, error O(D_sieve^6); for modular hyperbola boxes with local density k/l+O(l^-2), error as below. All discriminants here are nonzero integers of size R^O(1); the omitted primes contribute at most (log L)^C, by splitting at L and Mertens. A fixed small sieve level power of R and the truncated Euler product/Markov proof gives k logarithmic powers in the reciprocal main term. No lower sieve is used.

Case Delta=0. Since p!=r, U=r w, V=p w, with integer w>=1, w<=O(R/(XZ)). Fix w. Necessarily p and p w+1 avoid all sieve primes, by primality and roughness of the second source. These two linear forms have distinct roots at primes not dividing w; sieve p in its full band to obtain O(X L^-2 (log L)^C). For each such p, sieve r by the four linear forms
    r, w r+1, p(w r+1)+2e1, r(p w+1)+2e2.
All are rough: the latter three follow from source roughness and factoring the known large labels. Their roots are distinct over Q: the constants are nonzero; the two forms in wr+1 have determinant 2e1 w!=0; the determinant against r(pw+1)+2e2 is 2e2 w-(pw+1)!=0 for p>3; the remaining determinant is 2e2 p w-(p+2e1)(pw+1)!=0 for p>=7. Omit primes dividing leading coefficients and pairwise determinants. Thus O(Z L^-4 (log L)^C) r choices. All bands have length scale R^(1/2-o(1)); fixed small sieve level R^c gives negligible error uniformly in w,p. Multiplying and summing w<=O(R/(XZ)) proves (5).

Case Delta!=0. Fix p, and use the nonzero modular hyperbola
    r V=-Delta mod p
on the rectangle r in its band, V in [1,O(R/Z)]. Apply the elementary Kloosterman estimate of [14c6176](https://github.com/tara-sooo/A166944-Lean/blob/14c6176473bd6b30599d06a02e49cc2679c227ae/research/2026-11-26-min-direct-modular-hyperbola-three-root-source-sieve.md), section 2, O(p^3/4). Its arithmetic progression Fourier proof gives each residue pair modulo a sieve modulus coprime to p the area main term plus O(R^(3/8+o(1))), since both rectangle side ratios to p are R^o(1). The necessary exclusions on (r,V) at each sufficiently small sieve prime l>5 are
    r=0, V=-1, r(V+1)=-2e2,
    r V=-Delta-p, r V=-Delta-p-2e1.                        (6)
Here the displayed equalities specify forbidden sets, not constraints that an admissible pair satisfies. Outside primes dividing the nonzero constants Delta+p, Delta+p+2e1, p, or 2, each of the five sets has l+O(1) points and every intersection of two distinct sets has O(1) points (the last two product curves are disjoint; intersection of r(V+1) with a product curve fixes r). Hence local forbidden size is 5l+O(1). Apply the same Selberg quadratic argument on residue pairs as 14c6176, level R^c with c<=1/256: the total error is O(R^(3/8+8c+o(1)))=o(R/p times L^-C0) for any fixed C0. The reciprocal main form is >> L^5/(log L)^C. For each fixed p there are O(R/(p L^5)(log L)^C) candidates. The prime upper count O(X/L) supplies the sixth power, proving (5). This treatment includes nonzero offset shifts and opposite signs without assuming prime cofactors.

Sum (5) over offsets and bands. Each singular anchor pair key fixes both physical times and can contribute to at most one merger in its window. Thus the number of singular close keys is
    O(R L^(2b-6+o(1))).                                    (7)
This count is of candidate events, not merely normalized stationary time.

## 4. Long resident contact and the protected merger-loss theorem

If the other high-protected representative has elapsed time >D, it must be in the unique resident group. Its completed events since anchor consumed <=3B ticks, so it has been stationary at y for >P^d ticks. Therefore q(y)>=P^d/2. The incoming representative has a rough source x=y+E+p-1 and p|y+E-c. For fixed p,E,c, sieve the one residue progression of y mod p by the four forms from x±1,y±1, factoring the source's known label p. These are distinct over Q since x-y>=p-1>2; omit the fixed discriminant divisors as before. All four roughness thresholds are polynomial in R, so the count is O(R/(p L^4)(log L)^C). At most O(T'/p)=O(L^a) source heights; fixed p,E,y,h fixes its physical anchor. A moving anchor can arrive at y only once. There is at most one resident group, so each such key is charged at most once in its window even if that resident has many different historical anchors. Summing p over the near-square band using sum_p 1/p=O(log L/L), then E, gives
    #long keys << R L^(a+b-5+o(1)).                        (8)

Combining (4),(7),(8) and the cap-pair charge of section1:
    high-protected cap deaths / N
       << L^(beta+2b-6+o(1)) + L^(beta+a+b-5+o(1))
          + R^(-(1-d)/2+o(1)).                            (9)
This holds for the entire observation including pre-window history, even with additional arbitrary budget deletions. There is no assumption of a cap on the full endpoint fiber.

Young-protected alone cannot overflow: their roots lie in [y,y+2u+6], spaced by6, so their total count is <=1+floor((2u+6)/6)<=M. A young loss therefore occurs only if a high-protected group is present. At such a merger h<=u+3 from any young root. The representative high anchor has height h_a=h-(elapsed since anchor)+E/2<=u+3+B/2, so p>=P>>u+B implies h_a=s(c); it is singular. Count such anchors by fixed p and sign: source x=pu+e with source roughness gives the two linear forms u and pu+2e, so O(R/(p L^2)) choices (uniform with no growing discriminant issue). There is only one singular height per sign. Sum p>=P through O(T') gives O(R L^-3 log L) anchor keys. For each anchor and each possible E<=B, at most 1+floor((2u+6)/6) distinct young roots can die at y=v-E, even across several successive contacts there, because deletion is irreversible. Assign each young death to one of the present high anchors. This yields
    young-protected cap deaths / N << L^(beta+b-3+o(1)).   (10)

Consequently for fixed sigma>=0 and parameters satisfying
    beta+sigma+2b<6,
    beta+sigma+a+b<5,
    beta+sigma+b<3,
the whole protected cap loss is o(L^-sigma). This is an unconditional actual collision-loss upper bound: it excludes a family of merges, rather than assuming their rarity from dwell statistics. It does not bound collisions between unprotected groups. At height0 there is no resident, and at height3 the resident reduction of section2 is a special case of the singular pair count; the proof also covers nonzero heights and short post-anchor relays.

## 5. Combine with the earlier weighted live-time cost and protect against budget deaths

Use the additive cost C_R of section5 of 5a22180 (not the local-diversity version, although its nonnegative common increment bound would also suffice). Its scales Y0=exp(L^gamma0), Y1=exp(L^gamma1), 0<gamma0<gamma1<1, narrow charge e^(-L^alpha)/(k+1), medium charge 2q(x)/T' if q(x)>=p^d/2, no cost at p>=Y1. The uniform maximum increment
    epsilon_R <= e^(-L^alpha)/(k+1)+2Y1/T'
is smaller than every fixed negative power of L. Anchors p>=P>>Y1 pay zero. Each full root path has at most O(T'/P)=O(L^a) anchors; within each high-protected interval at most O(B+1) completed events leave it still protected. At young age <=u at most O(u+1) completed events occur. Thus the sum of cost increments at all events whose POSTstate is protected on any full root history is at most
    O((u+1+(B+1)L^a) epsilon_R).                          (11)
This counts potential budget-death events in the correct poststate, including events during which a previous protection ends only if the new state is also protected.

Choose one common budget threshold t in [b_R,2b_R], b_R=L^(-sigma-1). For a full actual path, the set of thresholds for which its first cost crossing lies on a protected event has measure at most the sum (11), because each event crosses precisely an interval of thresholds of length its cost increment. Cost monotonicity and actual-path determinism are essential; an early cap death can only remove a later possible budget death. Averaging over t, there exists a deterministic common threshold for which protected budget deaths over all roots and windows are
    o(N L^-C0) for every fixed C0.
This existence is compatible with any cap policy prioritizing protected groups. The priority policy need not minimize final cost; the previous live inequality was proved for arbitrary irreversible caps.

Now choose exponents satisfying the previous live criterion's conditions as well:
    beta+sigma+alpha<3, beta+sigma+delta0<3,
    beta+sigma+epsilon1<2(gamma0+gamma1).
For example beta=2.1,sigma=.25,alpha=.60,gamma0=.45,gamma1=.85,epsilon1=.10,delta0=.50, a=1.1,b=.25,d=.6. All inequalities of sections4–5 hold. With the chosen budget, mean prefix cost <=2b_R+epsilon_R=o(L^-sigma). The previous live-time inequality gives, under finite twins, eta_live=o(L^-sigma). Hence for every fixed lambda>0 the fraction still live at offset lambda T' is o(L^-sigma). Almost all original roots must be discarded early, yet the combined protected merger/budget deaths are o(L^-sigma). In particular almost all deaths must be at age >u AND outside the B-gain neighborhood after the latest rough near-square anchor. This is a new restriction on the actual necessary losses under the finite-twin hypothesis, not a proof of their impossibility.

## 6. Use the protected-loss theorem for unweighted successors

We can go further on the actual anchor population, using the fast-height factor and slow two-sided sieve of 769ef28. For every live token at a rough anchor firing p>=P, inspect the full actual continuation to its next completed r>=Y0 with intervening total gain E<=B (if such a pair exists). We count ANCHOR TOKENS, not root-time on the source segment. Cap at the source tick gives at most M such tokens per actual firing. Count all candidate phases across B0 windows, whether or not the tokens survive to the successor.

If r has full wait w_r>=r^d, its source y=x-p+1-E has q(y)>=Y0^d/2, while q(x)>=p^d/2 by anchor definition, without assuming the source's own observed wait long. For fixed p,sign,E the four forms x±1,y±1 on x congruent to the source sign mod p are distinct. Use level p^c (fixed small c), with two exclusions through the source roughness threshold and four through the smaller Y0 threshold, as in section8 of 769ef28. The reciprocal main term supplies (log p)^2(log Y0)^2, up to (log L)^C. Thus candidate x count
    << R/(p (log p)^2 (log Y0)^2) (log L)^C.
Now there is NO normalized time weight to cancel the heights: pay O(T'/p)=O(L^a) possible source postheights. Sum p over the near-square band and E<=B; multiply by cap M. The normalized anchor TOKEN count is at most
    L^(beta+a+b-3-2gamma0+o(1)).                           (12)

For fast target w_r<r^d, retain the previous nonzero height factor H=2h+2D-E+1 or -5 with r|H, H>=r-6>0, H=O(T'), D<=3E+w_r. Here D is firing difference, not the threshold in section2. Since E+3<p, p!=r as in 769ef28. At fixed bands p~X,r~Z, count source p and h, E,D, the O(L/log Z) possible prime factors r of H, and O(R/(XZ)) possible spatial sources by CRT. Multiplication by M (rather than M X/T') gives normalized count
    << M (T'/X) (B+1)(B+Z^d+1)/(Z log X) * L/log Z.
The extra factor T'/X=O(L^a) is harmless since Z>=Y0 grows faster than any power of L. The sum over bands is smaller than every fixed negative power of L. Thus (12) plus negligible error bounds all the specified anchor tokens. With beta+sigma+a+b<3+2gamma0 (true of the example in section5), they are o(N L^-sigma).

Take z0=floor(c0 log L) with small fixed c0>0 so the primorial cell width Q0=2 prod_(3<=p<=z0) p <=B by Chebyshev. Then z0>the previous narrow cutoff z~sqrt(log L) eventually. After a rough anchor, if subsequent labels remain <=z0 they cannot leave this cell (e173792), so their total gain <Q0<=B, and completed time <=3B. Throughout such a relay the token is high-protected. Consider EARLY anchor tokens with at least tau T' time remaining at firing, fixed 0<tau<1; it may be a pre-window firing. Each token is counted once per such event, not once per root. Under finite twins, the following alternatives exhaust these tokens:
- If discarded before or during the low-only relay while still protected, charge its protected death. There is at most one such unresolved anchor per death (any later anchor has label >z0).
- If its first completed label >z0 in the full continuation is >=Y0, the intervening gain <=B; (12) and the fast count apply. This is negligible independently of actual deletion.
- If no label >z0 completes before retirement and it survives, all later completed time <=3B. Its terminal observation is >=tau T'-3B, hence for large R at least tau/2 of the horizon. Only one such final anchor per token is possible. Under finite twins the actual capped terminal dwell bound of 5a22180, (1), gives at most O(N M (1+log^+(S/T'))/(tau L^3)) such tokens, which is o(N L^-sigma) for fixed tau.
- Otherwise the first subsequent completed label >z0 is in (z0,Y0), and the token survives to its firing (it may die on that event after paying its cost). This is one narrow-band event. Distinct consecutive anchor intervals on one actual root are disjoint, so each narrow event can be charged at most once.

Consequently for the budgeted protected priority policy of section5 under finite twins,
    #early rough-anchor tokens
       <= #live completed narrow-band token events + o(N L^-sigma).    (13)
If tau=L^-zeta, the same follows with the added condition beta+sigma+delta0+zeta<3. The actual count on the right includes the event that causes budget or cap deletion, if any. This is a genuinely unweighted supply statement using the new protection theorem. In particular cheap anchors cannot avoid all intermediate labels by being absorbed during the low-only continuation. It does NOT establish a contradiction, since the narrow-band budget permits exp(L^alpha) times a negative log power of events per token, whereas the number of near-square anchors per root is only O(L^a). The compulsory one narrow event per anchor consumes a negligible portion of that budget. Trying to infer survival from the deterministic time to leave a singular B-gain neighborhood gives only B/2-3 ticks, also much too small versus T' L^-sigma. Nor does the theorem bound the population of roots that die in the gap after young age and before the first rough anchor. The missing lower bound is therefore on actual cheap survival in these unprotected intervals, or on budget traffic there. The proof is not complete.

## 7. Executed audits and limitations

Three scripts on the same branch, executed as ECMAScript in tool runtime before commit and on exact remote readback. Fixed finite cutoffs used to check arithmetic and loss identities, not growing asymptotic scales. No independent analytic referee, standalone Node process or Lean kernel run.

A. [Anchor priority audit f39ce48](https://github.com/tara-sooo/A166944-Lean/blob/f39ce483f2b5b0b2cf5ea76deef27bb700df574c/research/min_local_negative_anchor_priority_audit.mjs), blob375256a0ac13e69a8fd91949cb3ffc7d7c8ea3ba. Six slabs R12000..2e6,622004 roots,17010526 full-root replay events,7258199 counted structural/replay controls,1215 protected anchor pairs including754 singular close,231132 reset3 resident checks,3506 roughness-form checks (in addition to per-event congruences and mass identities). Original version a2e7c50 had an inert uniqueness assertion for long keys; fixed in f39ce48 and the full six-slab run passed the actual uniqueness assertion. Exact same-prime exclusion under the sufficient gap hypotheses, unique anchor pair and long contact keys, young height pin and cap losses checked. At R2e6 finite P251,B8,M32,d=.6,u89, final .70386070, live .73553698, protected cap deaths .01091701 (high .00276000, young .00815701), unprotected deaths .28522229. 192 close pairs of which187 singular,126 long. At P1001,B4,M4, protected deaths .00183000, unprotected .81535882, final .18281118. These counts include existing twin endpoints, do not estimate growing-parameter retention.

B. [Budgeted priority audit ea9be8e](https://github.com/tara-sooo/A166944-Lean/blob/ea9be8e0e497d63a63ed8186efd496b0d8df4b3b/research/min_local_negative_budgeted_anchor_priority_audit.mjs), blob1466210274d1f2b58fdba6527d48165f2f16e2c7. Four slabs R12000..480000,122004 roots,2641688 full-root replay events,1166429 counted controls plus per-root threshold interval assertions. Finite proxy additive cost8 per narrow event (5<p<47), 2q per rough medium event below P, zero above P; exact protected threshold measure over [budget,2budget) checked against total protected cost increments. Actual fixed-budget policy also replayed. At R480000,P123,B8,M32,budget256 final .62159223, live .70548729; protected cap loss .00658742, protected budget .00646242, other cap .07699904, other budget .28835890. Mean full-history protected threshold crossing fraction .00152215 over [256,512), upper by protected increment sum .17989414; this is a finite measure bound, not the asymptotic random-threshold result.

C. [Early anchor successor audit 961245c](https://github.com/tara-sooo/A166944-Lean/blob/961245c8339588e2c95d995d6b5e96cc5c5af3f1/research/min_local_negative_anchor_successor_audit.mjs), blob533bf6c95935302261007324d5c1b8f2baced38c. Four slabs122004 roots,2641688 full-root replay events,1215324 counted controls including48302 successor, factor and roughness checks. Finite z0=3 or5,Q0=6 or30, B=Q0, Y0=23 or47, early remaining T/4. At R480000,P123,M32,budget256, early live anchor tokens59548; first >z0 high11424 (fast1320,slow10104), narrow43720, no completed >z0 before retirement4404 (full continuation, including those later deleted). Verified low-only cell wall, total gain and time, distinct labels and nonzero target-height factor, both source/target roughness and exact partition. No asymptotic inference; the no-high case is not asserted to be a live survivor without checking deaths. The analytic use of (13) explicitly charges deaths first.

Main/siblings untouched. Complete twin proof and formal verification remain open.