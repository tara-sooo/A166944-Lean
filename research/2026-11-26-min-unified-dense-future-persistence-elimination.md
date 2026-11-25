# Eliminate persistence from the moderate-clock certificate by multiscale dilution and dense future high labels

2026-11-26 JST. Continues [aa04b0b2b305](https://github.com/tara-sooo/A166944-Lean/blob/aa04b0b2b305c80ecac7de0e3c137813126ddf0e/research/2026-11-26-min-unified-first-defect-transport.md), integrating the multigrid geometry of 8689a99, phase-conditioned ranks of cd83a9d, and the prime-root future-distinct-label strategy of 1a4005f2f336. Independent source heads checked unchanged: prime-root 1a4005f2f336ede61cca1a9656c158a559338b72; stable-heavy e1ad9e2b434c652699e1bc9a0797887631e0ea6d. New theorem: the moderate residual clock can be bounded by ONLY the averaged first-defect energy, with the same physical cohort cutoff and asymptotic coefficient 24 ell. There is no need to establish a separate persistence-envelope upper bound. This does not prove that the entire relaxed persistence energy is small. The remaining massive-clock and defect-energy upper estimates are open. No Lean verification.

## 1. Frozen ensemble and source measure

Retain X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B. All original completed gain-stopped MIN prime-root paths are unchanged. Event at prehorizon C has odd label p<=B, gain g=p-1, wait w<=2r(C)<=2p and w<=3g. Actual gain <H on each tag; initial deficit 6 and final deficit nonnegative. Under finitely many twins all tags reach T eventually and W_all>=N(T-6)/2.

Use all frozen local masks and the longer focal entropy mask from aa04b0b, with grids P_j (M=Theta(u/ell)), P_min>=B^(1/8)/O(u), P_max<=B^.25, consecutive ratios >=u³/O(1). Put a=u^.25, epsilon=ell^(-1/2), theta=1/ell. Each retained event e has at least (1-epsilon)M good grids, with actual right witness either itself (p_e>=aP) or a nonself crossing q<=P/a whose prehorizon is within 2P of C_e. Its source posthorizon is J=C+q-1. In fact noncrossing gap to the next crossing is <=P. Each original tag contributes <=9P of assigned wait per boundary atom of the right witness.

Use L0 largest even primorial <=ell, A=L0/2, y0 largest prime factor. At each source projected event (C,q), n_c is the full original tag count in the residue class c=v mod L0, b_v is the full original physical exit population, a_v is its stable subset from aa04b0. On a good witness, n_c>H/(Aq u ell²), b_v<=2n_e where n_e is the original focal true arrival group mass, and if
    n_e <= n_phase_cut(e)=H/[256 max(P_max,L0 p_e)u ell³],
the rank-unpaid, near-mass-eligible stable far partner set in that class has population >3 n_c/(8ell). The focal original tag itself is stable at that witness. The far distance is R_P(q)=16 max(P,q) or the larger R_e; the displayed lower bound holds for the local R_P(q).

Use the exact restricted normalized source energy E_P^o of aa04b0, with original class-thin, rank, near-mass and stable focal/partner restrictions. Each ordered original source tag/partner-tag pair contributes P/n_c per crossed atom, and its row and column coefficient sums at a given atom are <=1. The common forward distance is now fixed at
    Lambda=floor(D_s/4), D_s=floor(T/(u ell^6)).
Then Lambda=Theta(H/(u ell^6)), Lambda>>B+P_max, and all stable source tags have enough actual completed future gain after J to cross Lambda. Compare both actual continuations until first translated-prefix failure or until focal prefix gain reaches Lambda. As in aa04b0, the persistent pair mass I_P satisfies the radical envelope with
    L_v=lcm(L0,2q,2p_1,...,2p_k)>Lambda,
    persistent partner fraction <=min(1,2 floor(4H/L_v)b_v/n_c).
All other pairs are routed to their first actual defect (split or same-edge exit lag change) at a side with a nonperiodic selected label p>y0. Denote the exact transported mass at projected destination (C,p) by D_P(C,p), and its grid average by Dbar(C,p). We will bound only the moderate retained clock by the defect sector, NOT assert an upper bound on I_P for all sources in E_P^o.

## 2. Low focal labels: grid-size dilution

Take Y=B^(1/10). For all large X, Y<P_min/a, so a retained focal event with p_e<Y is nonself on every good grid. Also L0 p_e<P_max, hence n_phase_cut=H/(256P_max u ell³). Every good right witness has q<=P_j/a. Exclude the single largest grid from this argument (no clock payment; one fewer usable witness per event). For all other grids P_j/P_max=O(u^-3). For a moderate focal event n_e<=n_phase_cut, the persistence partner fraction at its good right witness satisfies
    f_persist/n_c
       <= (8H/Lambda) b_v/n_c
       <= (8H/Lambda) A q/(128 P_max ell)
       = O(A q u ell^5/P_max)
       = O(ell^6/u^(2+1/4)) = o(ell^-2).                (1)
Here A<=ell/2, q<=P_j/a. This is uniform across all such focal events and good grids. It uses the conservative radical bound L_v>Lambda, not an unproved distribution of L_v. It is a bound on the stable smaller-or-equal partner mass relative to the ORIGINAL class denominator, exactly the source measure being transported. The surviving defect-bearing partner mass is therefore > (3/(8ell)-o(ell^-2))n_c. No special roughness condition on the low focal label or its witness is required.

## 3. High focal labels: all-mass forward richness trim

Call an original event expensive-high if p>=Y and w>=g/ell. Pay all waits of p>=Y events not meeting this condition at O(NH/ell), since their waits are <g/ell. Use the SAME original event list, not a new trajectory.

Partition prehorizons into ordinary blocks [k L_b,(k+1)L_b), L_b=floor(Lambda/2), independent of the primorial grids. Let eta=1/ell. Within each tag and each such block, pay the waits of expensive-high events for which the sum of waits of strictly later expensive-high events in that same block is <eta Lambda. These form a terminal portion of the expensive-high list; their total wait is <=eta Lambda+3B in a block. Every original tag meets O(H/Lambda+1) blocks. Thus the total cost, including the cheap-high trim, is
    O(NH/ell+N(H/Lambda+1)(eta Lambda+B))
       = O(NT/ell).                                     (2)
Indeed B/Lambda=o(1/ell) and Lambda<=H. This argument does not assert that the *number* of expensive-high events is small or that their wait is uniformly distributed. It is a trailing wait-mass trim, not a trailing gain trim, and is applied only to the focal actual events. The original source energy continues to use the previous frozen populations. Both high masks are optional in the massive sector too, at no extra cost.

Every remaining focal event e with p_e>=Y therefore has >=eta Lambda actual expensive-high wait STRICTLY after it in its own block. At any good grid's actual right witness, the horizon J after that crossing is <=C_e+2P_max+B (and J>=C_e+g_e). The expensive-high events of this future list lost before or at that crossing have total waits <=3(2P_max+B), because actual gain intervals on one tag are disjoint and w<=3g. This is o(eta Lambda). The others have prehorizons below C_e+L_b <=J+Lambda. Consequently all those remaining expensive-high events occur in the actual source prefix that ends at its first completed gain crossing Lambda. Its expensive-high wait is at least
    eta Lambda -3(2P_max+B) >= Lambda/(2ell)             (3)
eventually. This is true on ALL good grids, including self and nonself, and for any representative of the stable focal departure slot by deterministic continuation from (v,J). We have not imposed the new focal richness mask on partner tags. It is enough to force a defect from the focal word.

## 4. Local two-form sieve rules out persistence in a rich word

Uniformly in every odd prime p>=Y, in an arbitrary interval I of prehorizons of length Lambda+B+O(1), the number of even C in I with p eligible and r(C)>=(p-1)/(2ell) is
    O(Lambda/[p u²]).                                  (4)
Proof: for each of the two eligibility signs write C=p h-sigma. The two forms h, p h-2sigma avoid odd primes <=z=floor(p^(1/40)); z<(p-1)/(2ell) for large X, and every such sieve prime is less than p. At each odd sieve prime the two forms have distinct roots. The parameter interval has length O(Lambda/p+1), at least of scale Lambda/B for the full containing interval. Apply the dimension-two upper Selberg sieve with squarefree cutoff z and the same denominator/remainder proof as 8008fbc and 12292f36. Main upper density O(log^-2 z)=O(u^-2), uniformly since log p>=u/10. Remainder O(z^8)<=O(B^.2) is absorbed by Lambda/(p u²)>> B^.2, as Lambda=Theta(B²/(u^(5/4)ell^6)). The argument works in translated intervals; it is not an inference from a global O(X/p) support bound. No new prime-tuple lower estimate. The definition of r uses eligible odd prime factors; all sieve primes here are <=B. Bounded scales are irrelevant to the asymptotic claim.

In any actual source prefix starting at J and ending upon crossing Lambda, prehorizons are in [J,J+Lambda), and each is visited at most once. Every expensive-high event has r>=g/(2ell), since w<=2r. Its wait is <=2p. Thus for any one fixed high label p, its expensive-high wait in the prefix is O(Lambda/u²), by (4). If the prefix radical L_v<=4H, then there are at most
    log(4H)/log Y = 20+o(1)
distinct labels >=Y in it, since all divide L_v. The same bound holds for any completely translated prefix with nonzero |Delta|<=4H. The total expensive-high wait would be O(Lambda/u²), contradicting (3). Therefore the stronger one-strand conclusion holds:
    L_v(Lambda)>4H at every good witness of every remaining high focal event.  (5)
There are ZERO persistent partners at those witnesses, independently of their physical group sizes. In the moderate sector the original rank lower mass >3 n_c/(8ell) is entirely defect-bearing. This proof uses local sieve scarcity of each expensive high label rather than any claim that large labels are automatically distinct or abundant in every actual word.

## 5. Defect-only moderate-clock certificate

Combine (1) and (5). After the o(NT) focal masks in (2) and all prior masks, for every retained moderate focal event, on at least (1-epsilon)M-1 good grids its actual right witness has defect-bearing stable smaller-or-equal far partner fraction at least (3/(8ell)-o(ell^-2)). All these ordered pair-incidences are among the original eligible source energy E_P^o, and by definition they are routed to actual first defects. The same right cell capacity <=9P per tag-atom implies
    sum_(retained moderate e using this grid) w_e
       <= [9/(3/(8ell)-o(ell^-2))] sum_(C,p) D_P(C,p).
Averaging the grids, counting each focal event on at least (1-epsilon-1/M)M grids, gives
    W_mod,rem <= [ (24+o(1)) ell/(1-epsilon-1/M)] sum_(C,p) Dbar(C,p).
All constants are uniform; the o(1) term tends to zero. This uses the entire relaxed transported energy as an upper bound; we have not proved that other source slots have negligible persistence. In particular we have not asserted that mean I_P=o(NT/ell). We simply no longer need I_P to dominate this focal clock.

The normalized transport and row/column capacity of aa04b0 transfer unchanged:
    Dbar(C,p) <=2 Lcap n(C,p), Lcap=Lambda+B+P_max,
and p>y0 for every destination. Its graded thin mass m_eff=Dbar/(2Lcap) can be paid for m_eff<= H h(r)/(Lcap u ell³), h(r)=log²(2+r)/(1+log log(2+r))², and stronger mid/rough caps from aa04b0. Their total energy cost O(NT/ell²), after multiplying by ell still o(NT). Write D_rem for the total residual averaged first-defect energy after these payments. Let W_massive,rem be actual retained clock with n_e>n_phase_cut(e) after previous masks and (2). We have under finitely many twins
    NT/2-o(NT) <= W_massive,rem + (24+o(1))ell D_rem.     (6)
The factors 1/(1-epsilon-1/M)=1+o(1) have been absorbed. Thus a new sufficient condition is
    liminf_(dyadic X->infty) [W_massive,rem+24 ell D_rem]/(NT) < 1/2.    (7)
To justify removing the asymptotic coefficient, on a subsequence with the displayed normalized nonnegative sum bounded below 1/2 by a constant margin, ell D_rem/(NT) is bounded, so its multiplication by o(1) is harmless. Same physical cutoff as cd83a9d and same leading coefficient as aa04b0. The new criterion is implied by aa04b0's previous sufficient condition with Pi_rem+D_rem at the same chosen Lambda, since Pi_rem>=0 and focal masks only decrease W_massive. Even the previous condition with exact persistent energy replaced by I_rem implies (7). No assertion of strict separation on actual asymptotic ensembles; the eliminated independent estimate is a substantive reduction of that route. Neither D_rem nor massive clock has the required strict upper bound yet.

## 6. Finite diagnostics

[Final standalone audit](https://github.com/tara-sooo/A166944-Lean/blob/cfa892ab0ebd913e591f3fcb6dcc5d49f0b8bdd7/research/min_unified_dense_future_persistence_audit.mjs), exact remote readback verified. Eight final-parameter runs passed in ECMAScript runtime (four ordinary, three reach-focused, one short). Reproduce: node research/min_unified_dense_future_persistence_audit.mjs 1024 4096 16384 65536. Ordinary T=min(16B,floor(X/2)), Lambda=2B (min32); focus T=floor(B/2), Lambda=max(8,floor(B/8)); short Lambda=8. Y=max(5,ceil(B^.25)), expensive w>=g/4, eta=.08, fixed grids [6,30,210], wheel6, rank theta=.5, radius q, stable substitute is actual future room >=Lambda. These deliberately differ from analytic parameters. Initial focus runs with Lambda=2B had zero ready slots; changed only focus Lambda in final source and reran those three tests, yielding nonvacuous checks. Short test exercises positive translated pairs. Reconstructs original trajectories, trailing high mass trim per block and exact budget, original right witness geometry, lost high wait and transfer of remaining high wait to actual completed source prefix, relaxed local finite eligible rough support census and per-label wait domination, product of distinct actual expensive-high labels, sampled? NO: all qualifying ordered distinct exit-slot pairs under the finite rank/room/phase/radius filters, translation to first defect, persistent high-label divisibility and count, normalized partition. Does not test analytic sieve constants, low-sector asymptotic inequality (1), new final clock certificate (6)-(7), or cumulative earlier masks. Finite high density alone need not eliminate persistence; in short test 67 of 111 persistent pairs have finite high prefix wait >=eta Lambda. No literal gcd oracle or Lean compilation.

| X/mode | ready slots | high-label product >4H | rich right-witness transfer checks | finite qualifying slot pairs | persistent |
|---:|---:|---:|---:|---:|---:|
|1024|52|31|23|0|0|
|4096|429|429|830|46|0|
|16384|1565|1565|4088|156|0|
|65536|4442|4442|9147|435|0|
|4096 focus|1695|112|324|170|0|
|16384 focus|6784|1481|4175|740|0|
|65536 focus|28165|9925|13554|3792|0|
|65536 short|40541|0|0|7645|111|

Largest ordinary: 5709 roots,140255 events, no diagnostic T reaches, actual W2395330; 10013 block-tail checks, 46854 relaxed local support checks, 21597 retained rich focal incidences. All 4442 ready slots have high-label product >4H, and all 435 qualifying ordered slot pairs defect. Largest focus: 2886 reaches,75256 events,21773 block-tail checks,62812 local support checks,7317 rich focal incidences, 3792 qualifying pairs all defect. Short: 111 positive persistent-pair divisibility checks and 7534 defect pairs, zero rich focal incidences under its short block cutoff. The finite paid fractions are large with the substitute parameters, and the finite evidence does not establish (4) or the required asymptotic upper contraction. The mathematically new removal of the persistence term follows from sections 2–5. Main and independent source branches unchanged by this work.
