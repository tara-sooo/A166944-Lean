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
