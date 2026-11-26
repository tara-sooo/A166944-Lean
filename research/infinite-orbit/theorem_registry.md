# Initial constraint registry — hypothesis and semantic scope

Pinned baseline main bd180e3de0fe6e12cc3c3ea25d65a985445344eb; direct 3e19d7e945788d39b12a17744c2139970e90da8d; unified 6ec6ce3cc11afb8efa86611cc8c6eabf0aa872fa. This is a first-pass registry, not an exhaustive declaration inventory. "Paper" is not Lean verification; computational evidence is not promoted to universal constraints.

| ID | Result / constraint | Domain and required hypothesis | Status in source | Virtual model I |
|---|---|---|---|---|
| L01 | parity gcd, first hit and horizon update | canonical odd root; uncut or adaptive with eligibility | main recurrence gcd Lean; MIN transfer paper | finite exact lift |
| L02 | C<=2t; ordinary deficit d>=0; d'=d+2w-g | canonical MIN; g=p-1 | direct paper | relative proof |
| L03 | w<=2p; -g<=delta d<=5g | actual MIN event on unchanged plateau | direct paper | relative proof |
| L04 | adaptive pool p^2<=C+1; stops iff C±1 prime | standard integer C>=4 | direct paper | finite lift only; no absolute order |
| L05 | under finite twins above last center every adaptive trajectory infinite | standard integer; finite twins | direct paper conditional | virtual infinite events proved independently, not standard arithmetic |
| L06 | bounded label set cannot cross common even multiple; labels unbounded | unbounded gain, selected divisibility | direct paper | translated barrier proof |
| L07 | finite transcript CRT with composite neighbors | uncut, adaptive transfer requires eligibility | direct 425a4b9 paper + audit | generalized compatible ensemble construction |
| D01 | single-band deficit-chain sieve and product lower bound | actual standard window, selected nonresets in factor-two sqrt band, deficit cap, appropriate polylog closeness and witness-free hypothesis | direct 3793617 paper; actual higher-window finite coverage absent in source | not imposed |
| D02 | limsup (U+V)/(sqrt X log^gamma X)=infinity, 0<gamma<5/6 | hypothetical actual fixed canonical infinite ray, finite twins, arbitrary chosen factor-two near-sqrt band populations; geometric blocks | direct 3793617 paper conditional | not imposed |
| D03 | low-label gain / outside positive variation supply on disjoint pinned corridors | actual block, designated completed corridors, no offset witness; K>2V, S^2<=H+1, L>4S; see exact inequalities (3)-(6) | direct 3e19d7e paper + finite audit | not imposed; standard offset witnesses retained |
| U01 | A_mu=int alpha dmu=o(NT); int(1-phi)dmu=o(NT) | original dense source ensemble, actual forward assignment, finite twins | unified 6ec6ce3 cites prior paper | not imposed |
| U02 | F_late^mu(S)<=sqrt(2 k_S c_a N(H+Pmax) A_mu) | actual assigned missing focal mass, stable classes, k_S=1+floor(4H/S) | unified 6ec6ce3 paper | not imposed |
| U03 | bounded quotient mutual sample S_quot<=2d sqrt(M A_mu) | exact original two missing draws; high discovery graph, d=2 floor(Q) K | unified 6ec6ce3 paper | not imposed |
| U04 | homogeneous fan/comb necessary bounds | stable actual same-code trie, exact radical/lag hypotheses | unified 6ec6ce3 paper | not imposed |
| U05 | local lifetime deficit sieve forces macro missing in specified medium-band bounded-budget regime | actual source block with all specified gain, size and variation hypotheses | unified 6ec6ce3 paper conditional | not imposed |
| X01 | universal macro missing lower bound; remaining early large-quotient/small-label supply; final contraction | unified target | OPEN, not constraints | not imposed |
| R01 | actual A166944 record-index/twin classification and travel target | full original GCD recurrence, canonical record ancestry and specific target hypotheses | main partial Lean, final open | separate semantic domain; no blanket transfer |

Primary sources: [direct basic](https://github.com/tara-sooo/A166944-Lean/blob/425a4b9a32e8a4a808582eb75d06cfecb7c56f0a/research/2026-11-25-min-direct-arithmetic.md), [direct chains](https://github.com/tara-sooo/A166944-Lean/blob/3793617fd82ac3fa0b68679a57529fce233b3660/research/2026-11-26-min-direct-deficit-chain-sieve-and-global-log-obstruction.md), [direct corridors](https://github.com/tara-sooo/A166944-Lean/blob/3e19d7e945788d39b12a17744c2139970e90da8d/research/2026-11-26-min-direct-thickened-cut-recovery-and-local-supply.md), [unified XIX](https://github.com/tara-sooo/A166944-Lean/blob/6ec6ce3cc11afb8efa86611cc8c6eabf0aa872fa/research/2026-11-26-min-unified-radical-fan-lifetime-sieve.md), [main README](https://github.com/tara-sooo/A166944-Lean/blob/bd180e3de0fe6e12cc3c3ea25d65a985445344eb/README.md).

Next registry expansion: extract exact statements and dependency graph from all applicable MIN research notes and formal modules; identify fixed cutoff vs adaptive transfer conditions; separate actual source density from arbitrary finite ensemble. No constraint may be promoted just because a finite audit passed.

## Checkpoint II — scope separation

[Scale and tomography note](https://github.com/tara-sooo/A166944-Lean/blob/3343213ef21d2d4fc5836283e0b9664cd92f6fce/research/infinite-orbit/scale_and_tomography.md). Latest direct cut source [2a47be1](https://github.com/tara-sooo/A166944-Lean/blob/2a47be177db12d7fdcdc99daf9dfe7be0403da34/research/2026-11-26-min-direct-grouped-cut-sieve-and-all-label-corridors.md).

| ID | Constraint | Residue ensemble I | Scalar clock model II-B |
|---|---|---|---|
| L08 | common-root positive event congruence / finite CRT bound; all-prime tomography | exact; proves bare indexed ensemble has no standard common base | not imposed on multiple roots |
| L09 | absolute adaptive magnitude p²<=H+1 | finite lift only | exact |
| L10 | selected side time congruence | exact | exact |
| L11 | selected side neighbor divisibility; earliest competition | exact relative rule | not imposed; finite audit reports failures |
| D02 | global U+TV logarithmic lower bound (aggregate numerical condition) | not transferable | satisfied numerically with TV=Theta(X), not an application of actual-ray theorem |
| D04 | all-label endpoint corridor demand, exact anchor negligible mass, eroded deep-bypass bound (source (5),(7),(8)) | not transferable | all endpoints safe, zero anchor/endpoint demand, bypass mass G+o(X) by arithmetic cut distribution |
| D01 | high-band sublinear deficit-cap chain theorem | not imposed | hypotheses not met |
| U01–U05 | dense actual source allocation / collision and missing supply | not imposed | not imposed |

These columns refer to DIFFERENT structures; their intersection remains open. The finite common-root obstruction uses only positive event congruences, not artificial factors. The scalar construction does not license an inference from selected time clocks to actual first-hit recurrence. No full theorem inventory or Lean verification yet.

## Checkpoint III — exact standard horizon/clock constraints

[Phase graph paper](https://github.com/tara-sooo/A166944-Lean/blob/252201a0a16a1bf1b3dd69c508e8309872683940/research/infinite-orbit/phase_graph.md).

| ID | Constraint / conclusion | Status and scope |
|---|---|---|
| L12 | Exact maximum wait W(H,p): min(2p, smaller same-side 2q-2, larger same-side 2q, opposite 2q-1) | PAPER proof by previous-clock gaps and CRT attainment, all standard even H, arbitrary time, not canonical ancestry |
| L13 | For fixed standard horizon word, full earliest-hit/least-tie time cylinder: parity plus allowed residue sets for each factor q | PAPER exact equivalence, fixed waits, bounded interval must also meet resulting classes |
| L14 | H/2<=t<=3H+3 for canonical adaptive states | PAPER necessary envelope, not sufficient ancestry |
| D05 | High long edges p>=eta sqrt X,w>=p-2 require rough neighbors; eventually at most one eligible factor per side, semiprime or prime; possible H density o(1) | PAPER; initial source density, not later source-weighted transport |
| D06 | Max good-run gain L bounds interruptions: G_good<=L(1+b_lo+U_hi/(T-1)) | PAPER, actual block with longSafe good events; uniform L=O(sqrt X) OPEN |
| D07 | Bounded integer-slope tube t=mH+O(1) at large consecutive labels forces even side and exact line m=1 or2 | PAPER; residual one-sided prime chain, not all variable-slope rays |
| A01 | Finite factor/clock DAG and exact bounded-phase max-run computation | COMPUTATION X=4096,16384,65536,262144, fixed K210,V12. Actual standard segments with envelope, not verified canonical ancestry; no asymptotic extrapolation |

II-B's uninterrupted all-high long safe scalar model fails in all four tested windows even after relaxing phase consistency; exact MIN segments of two and three events nevertheless exist. The intersection of all constraints across arbitrary scales remains open. No new Lean verification.

## Checkpoint IV — exact low relay and first-high entry

[Mixed relay paper](https://github.com/tara-sooo/A166944-Lean/blob/c0f7f50e3fe9ad93693d1ffed951a211959a7c4a/research/infinite-orbit/low_relay.md), source direct [47a1442](https://github.com/tara-sooo/A166944-Lean/blob/47a14426499afbaacaadb11114dac7caccdb4fdf/research/2026-11-26-min-direct-variable-order-sieve-and-uniform-pinned-gaps.md).

| ID | Constraint / conclusion | Status and scope |
|---|---|---|
| L15 | Low-only transducer modulo K=2P_R terminates, gain E<=M_R<K, time B<=3E; actual low prefix agrees | PAPER; actual standard H+1>=R², no outside label allowed in prefix |
| L16 | Good highs p>=T>2R+2, w>=p-2 are R-rough; any intervening all-low relay must reach exact restricted terminal; same p cannot recur consecutively if M_R<p-3 | PAPER; full competition still required for sufficiency |
| D08 | G_low<=M_R(n_out+1); if R=o(log X), all outside labels >=Theta(sqrt X), then G_low=o(X); all outside long => d_b-d_a>=G-o(X) | PAPER; macroscopic positive variation allowed, not contradiction |
| D09 | Mixed-run bound G_good<=L_R(1+b_mid+U_bad/(T-1)) | PAPER; uniform L_R=O(sqrt X) OPEN |
| D10 | First outside long high after canonical low prefix has o(X) possible sources at fixed R, O((M_R+1)X/(loglog X)^2) count | PAPER; dense distinct odd canonical roots, not prime-root relative density or later source mass |
| L17 | First outside long high if p>max(9,d+1): post d'=2p+6s, w=(3p-1+6s-d)/2 | PAPER; fixed R automatically at sufficiently large square-root scale, not arbitrary later high |
| A02 | Compressed mixed DAG and exact bounded-phase audit with low relays; canonical first exit | COMPUTATION; R3,5,7 mixed and R3,5,7,11 first exit. Actual intermediate-state four-high word, canonical ancestry not checked; 5,222,400 first-exit source incidences, 84,643 applicable unit-multiplier checks pass. |

No all-constraint infinite survivor or final contradiction. Medium relays, bad high events, eventual rather than initial entry, and dense transport remain open. No new Lean verification.

## Checkpoint V — semiprime entry sieve and frozen unit-state continuation

[Entry cost paper](https://github.com/tara-sooo/A166944-Lean/blob/d66016a0d154c17acab78cddcb5e97e2c9bae077/research/infinite-orbit/entry_cost.md). Analytic sieve imported from direct 3793617; latest sibling references direct bc3b10b and unified f1f6e1c.

| ID | Constraint / conclusion | Status and scope |
|---|---|---|
| D11 | Good high p>=eta sqrt X,w>=p-2 at displacement E<=D<=X from canonical H0 in [X,lambda X] forces H=pq+e with q prime, opposite neighbor rough; count odd roots O((D+1)X/log^3 X) | PAPER; standard fixed-dimensional upper sieve, sufficiently large X, arbitrary prior labels |
| D12 | Prime-root refinement O((D+1)X/log^4 X), averaged exceptional factors via bounded second moment of J_3 | PAPER; three nonproportional forms in q for fixed p,E,e; no relative-density claim for sparse prime subsets |
| D13 | Dense odd or prime-root families: early-good fraction o(1) at D=o(log^3 X); under finite twins positive fraction need Omega(log^3 X) actual pre-entry bad gain and waits for fixed R | PAPER; tagged resource Omega(N log^3 X), not automatically omitted Mhat, not macroscopic |
| L18 | Any shallow good event with p>max(9,d+1) has frozen post state (H+p-1,(H+p-1+2p+6s)/2), injective in H,p,s; shallow entry multiplicity <=floor(D/4)+1 | PAPER; no restriction to prior low labels, not later merging |
| A03 | Exact unit-stratum mixed continuation with frozen arrival, and canonical first-good prefix scan | COMPUTATION; 261120 distinct roots incl43081 prime; 29026 unit cases pass; 6514 feasible arbitrary-state unit triples; max high count <=3 in four finite windows; ancestry of maxima not checked |

Uniform later mixed-run bound L_R remains OPEN. No Lean verification, full all-constraint model, or finite-twin contradiction.

## Checkpoint VI — signed recovery ledger and bounded-multiplier mixed-run capacity

[Recovery budget paper](https://github.com/tara-sooo/A166944-Lean/blob/956c288e4152e8f35e1f7fbcc5c34bca02dd2c76/research/infinite-orbit/recovery_budget.md).

| ID | Constraint / conclusion | Status and scope |
|---|---|---|
| D14 | Good p>=T, drift >=delta g, low relays <=M_R, alpha=delta-M_R/(T-1)>0: cumulative good gain F_j implies d'_j-d_start>=alpha F_j and strictly increasing good post-deficits inside a mixed run | PAPER; long condition w>=p-2 uses delta=1-2/(T-1) |
| D15 | Per mixed run all good gain with post d'<=D is <=D/alpha, even with deep vertices interspersed; full span if h<=k is <=(2kB+6)(1+M_R/(T-1))/alpha | PAPER; uniform O(sqrt X) at fixed R,k and square-root T, uncapped run bound remains open |
| D16 | Adjacent deep-to-shallow good highs in a mixed run require (2k-1)p2>=2h1 p1-M_R-9 under long condition; unit return needs ratio >=4-o(1) | PAPER; relative multiplier may fall despite strictly growing absolute deficit |
| D17 | Stop actual block once at last capped good; signed recovery P^-_bad >=alpha F - d_b+d_a - M_R(1+U_m/(r_R-1)+U_h/(T-1)); alpha F_cap<=D+M_R+c_m U_m+c_h U_h | PAPER; all earlier good gain in exact endpoint bound, actual physical budgets, no repeated boundary cost |
| D18 | Fixed R, D=o(X), square-root long good macro capped gain forces macro medium/bad-high gain; if interruptions submacro, later good d'=Omega(X), h=Omega(sqrt X) after macro cumulative good gain | PAPER; no finite-twin assumption needed conditional on actual block; deep/positive-drift survivor remains |
| U06 | Sum D17 once per full original tag: N(D+M_R) boundary; exact weighted cores use (D+M_R)sum b_Q instead | PAPER; no automatic missing-measure/core conclusion or implication from 4w>=g to positive ordinary drift |
| A04 | Actual recovery audit incl prescribed strata, weighted costs, upward returns | COMPUTATION; 1,402,869 event incidences, 161077 exact endpoint checks, 1098 positive exact demand; zero coarse macro-cap positive-demand examples; not Lean |

No full all-constraint infinite survivor, arbitrary uncapped run bound, or finite-twin contradiction.

## Checkpoint VII — deep inverse resonance and reverse branching

[Deep inverse paper](https://github.com/tara-sooo/A166944-Lean/blob/b6a2dd4a675afb63715c663a8ac0b9a922e783fb/research/infinite-orbit/deep_inverse.md).

| ID | Constraint / conclusion | Status and scope |
|---|---|---|
| L19 | At post (J,n), side s=n mod2, possible incoming label p divides gcd(J+2s,n-2s); exact wait interval from competitor previous gaps and canonical envelope | PAPER; at most two distinct labels p>=eta sqrt X, not two pre-times; arbitrary feasible intermediate states need not have ancestry |
| D19 | Distinct incoming high p,r force J=a pr-2s,n=c pr+2s, bounded integer a even,c, rational corrected slope c/a; positive nonreset d'-6s>=2pr, h_p>=r,h_r>=p | PAPER; reset exception, same-label merges unrestricted by this test |
| D20 | Both labels long => ar-1,ap-1 prime; two-form upper sieve gives O(X/log^4 X) collision states, uniformly O(D/log^4 X) in translated interval D>=X^(1/2+epsilon) | PAPER; physical distinct states, not tagged multiplicity |
| L20 | Exact reversed compressed high/low graph: in-degree <=8 times the offset-set size (1+floor(B/T)), with each candidate checked by inverse and actual forward competition | PAPER; fixed R and square-root band, no ancestry claim |
| U07 | From first designated shallow high entry after gain <=D0=o(sqrt X), at most k highs with only low relays: source multiplicity <=(floor(D0/4)+1) sum_{j<k} (D_R^rev)^j; polylog D0 and k=o(log X) imply X^o(1) | PAPER; restricted history, not total unified mass |
| A05 | 45,334,999 local arrival candidates, 1,849,266 feasible incidences, 40 distinct-label collision state incidences (all deep), 482 actual forward mixed pairs reverse-checked; 64,512 canonical roots show substantial equal-label merges | COMPUTATION; no Lean verification or asymptotic proof from finite data |

Uncapped arbitrary mixed-run bound, full all-constraint infinite survivor and finite-twin contradiction remain open. 

## Checkpoint VIII — gain-charged reverse graph and narrow-band unit cohorts

[Charged reverse paper](https://github.com/tara-sooo/A166944-Lean/blob/0e18d3da82d16963a18e2c562a3f0f99aa680171/research/infinite-orbit/charged_reverse.md).

| ID | Constraint / conclusion | Status and scope |
|---|---|---|
| L21 | Exact reverse compressed good graph with arbitrary non-good relays: for fixed even relay gain E, prior time lies in [n-u-3E,n-l], enumerate prior clocks and verify full deterministic MIN | PAPER; all good p in [T,B], w>=p-2, square-root band; exact local feasible states, not ancestry |
| D21 | Fixed-E reverse degree <=C(1+E/T), C=8(1+B/T); relay E<=M_R+c_m U_m+c_h U_h | PAPER; c_m=1+M_R/(r_R-1), c_h=1+M_R/(T-1); includes short and out-of-band highs |
| U08 | Depth j reverse path capacity A_j(S)=C^j binom(floor(S/2)+j,j)(1+S/(jT))^j, S=M_R j+c_m U_m+c_h U_h | PAPER; actual total relay budget, no independence; overcount allowed |
| U09 | First unit entry at displacement <=D0, <=k good visits, total post-entry interruption gain U: source count <=(floor(D0/4)+1)(1+sum_{j=1}^{k-1} A_j(M_R j+cU)); logarithmic cost-depth bound | PAPER; explicit history class, not general unified multiplicity |
| D22 | From first good post to later good post, c_m U_m+c_h U_h>=d'_1-d'_k+sum_{i=2}^k(p_i-3-M_R); unit return in B<2T-M_R-9 and T>M_R+3 pays tau=2T-B-M_R-9 | PAPER; arbitrary intermediate multipliers/interruptions, disjoint consecutive unit visits sum without repeated endpoint charge |
| U10 | Unit target cohort m with first designated good displacement <=D0: tagged bad cost >=tau(m-floor(D0/4)-1)_+ | PAPER; no bound on depth or first multiplier; per-target, not additive across overlapping targets, not omitted measure |
| A06 | 64512 canonical roots,4608 targeted starts,1503465 actual events; 283 reverse checks,20 independent full integer-time enumerations,46948 cost-depth capacity checks; canonical narrow-band 15-source unit cohort, 9 first arrivals and 6 paid returns | COMPUTATION; all pass; no exhaustive asymptotic verification |

Uncapped high-deficit regime and weak/short high population remain; no all-constraint infinite model, Lean verification or finite-twin contradiction.

## Checkpoint IX — rational clock locking and transverse crossing costs

[Rational clock paper](https://github.com/tara-sooo/A166944-Lean/blob/41dfbb76ed6d5ee4d5a6be42b8fe8218acc31469/research/infinite-orbit/rational_clock.md).

| ID | Constraint / conclusion | Status and scope |
|---|---|---|
| L22 | Corrected slope mu=(n-2s)/(J+2s); for reduced a/b, p divides Z=b(n-2s)-a(J+2s), so abs(Z)<T at p>=T forces exact resonance | PAPER; b odd forces even arrival side on resonance; includes resets |
| D23 | Same-slope consecutive selected high post-states: w_j-mu g_j=mu E-W+2(1+mu)(s_j-s_i); absolute mismatch <=4E+10 | PAPER; arbitrary actual relays and waits, no deficit cap |
| D24 | Reduced denominators <=Q: slope switch requires E+g>=X/(9Q²). Under 18 B Q²<=X, switch relay pays its own ending mismatch; sum mismatch <=4U+10(k-1)+4B | PAPER; uniform Q=o(X^(1/4)) at square-root B |
| D25 | Locked-scale fast gain 4w<=g <=16U+40(k-1)+16B; deep nonpositive drift and long events below slope 1 have analogous mismatch bounds | PAPER; selected small-denominator population, not all deep high states |
| U11 | Canonical root sentinel slope 1/2 removes initial 4B credit (Qstar=max(2,Q)); nonreset denominator b>=X/(6+5G0); reset-to-nonreset selected relay E>=(X/Q-6)/5-B | PAPER; actual full tagged lifetimes, no automatic missing-mass implication |
| D26 | Diagonal L=n-J-4s divisible by p; strict opposite signs cost E>=(2T-B-5)/2, zero requires n=J even; long downward and fast upward sign/zero transitions have stronger costs | PAPER; any selected high list, no denominator cap |
| A07 | 532803 start incidences incl27648 canonical,13484128 events; 3053230 alignment checks,763 strict diagonal crossings,1347 literal GCD controls | COMPUTATION; all assertions pass, no locked-scale switches or low-Q canonical nonreset entries observed |

Large-denominator high states, strong complementary gain, positive-drift resonant trajectories and diagonal zeros remain. No full all-constraint infinite model, uncapped mixed-run bound, Lean verification or finite-twin contradiction.

## Checkpoint X — cofactor transition capacity and large-denominator diversity

[Cofactor support paper](https://github.com/tara-sooo/A166944-Lean/blob/0dd23c6dc881fe1a1201f132a11714a6761ad2b1/research/infinite-orbit/cofactor_support.md).

| ID | Constraint / conclusion | Status and scope |
|---|---|---|
| L23 | Even corrected cofactor a=(J+2s)/p=(H-e)/p+1>=p+1; a=b m with reduced denominator b and m=gcd(J+2s,n-2s)/p | PAPER; square-root band a=Theta(sqrt X), no wait/deficit cap |
| D27 | Consecutive selected pair (a,b0), p,r, sides s,t: (b0-1)r-a p=E-1+2(t-s) odd nonzero; fixed cofactor pair with E<=K occurs <=C_lambda(K+1), C_lambda=12(1+2lambda) | PAPER; gcd divides nonzero shift, affine lattice count, arbitrary relays/waits on one ray |
| D28 | n consecutive selected pairs, P actual ordered cofactor pair support, S distinct cofactors, U complementary gain: n²<=2C_lambda P(U+n)<=2C_lambda S²(U+n) | PAPER; integrated ordered-cost count, macro high gain and bounded S force macro U |
| D29 | S<=sum_(actual reduced b) floor(Lmax/b); for b>=beta T bounded denominator support forces macro complement if selected gain macro, U=O(sqrt X polylog) forces polynomial diversity | PAPER; not small-denom locking or a bound on all support |
| D30 | Repeated same cofactor has strictly increasing labels; adjacent same-cofactor selected pair pays E>=2a-r-1>=2T-B+1 | PAPER; narrow band implies Omega(T), disjoint adjacent relays only |
| D31 | Positive ordinary drift at square-root-scale p forces prime cofactor q=a-1 asymptotically; fixed q and varying p two-form sieve gives total F_up=O(X S_up/log² X) | PAPER; actual cofactor support, no small complement hypothesis |
| U12 | Weighted original-tag extension sum w_i n_i <=sqrt(2C_lambda (sum w_i P_i)(sum w_i(U_i+n_i))) | PAPER; full actual lists, no automatic omitted-mass conclusion |
| A08 | 64512 canonical roots,16702 targeted starts,1761174 events,122013 pair identities,67888 moment checks,120 integer-lattice censuses,152 upward cofactor repeats | COMPUTATION; all final tests pass, no repeated ordered pair within a tested list, no asymptotic constant inference |

Large cofactor and denominator supports remain compatible. No full all-constraint infinite model, general uncapped bound, Lean verification, or finite-twin contradiction.
