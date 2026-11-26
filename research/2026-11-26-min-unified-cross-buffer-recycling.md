# Integration XXIX: source-preserving cross-label extraction and local diversity at the recycling scale

2026-11-26 JST. Parent 973784527ec9195ff4b74e891032ea5bbaab0eb2. Direct preflight 9c1bd5a3cbe5bd1da18af164bc6d652c2e3d2c0f, [causal stratum theorem d422023](https://github.com/tara-sooo/A166944-Lean/blob/d422023036a9cb61ebe6e87890fa28dcecf21ae9/research/2026-11-26-min-direct-causal-recycling-scale-and-stratum-transport.md), [mandatory buffer audit](https://github.com/tara-sooo/A166944-Lean/blob/9c1bd5a3cbe5bd1da18af164bc6d652c2e3d2c0f/research/min_direct_mandatory_cross_label_transport_audit.mjs). New: replace the one-stratum part by earlier distinct-label causal consumption WITHOUT changing the source population or increasing its weights, preserving both residence bounds and the direct near-minimal support gap constraints. On comparable narrow guards this gives a macro population of cross-label strongly separated endpoints, with Omega(log² Y) distinct sources in many recycling-scale short bins if the long-bin weighted support is near minimal. No general upper bound on source support.

## 1. Source-preserving mandatory-buffer extraction

Retain XXVII–XXVIII's original tag, long prehorizon bin L, actual excursion fragments with guard width <=M_*, chosen fast high consumers d'>6, and local matches m_st. Restrict any subset of those matches (including residence E_st,U_st<=A M_*), to source labels Y<=p<=R0. Assume Y>=11. All labels are odd and actual ordinary postdeficits have form 2ph+6I. A source with positive matched height >6 has h>=1. Same label p at source and target implies h-k=0,1,2: positive overlap requires 0<a-b<u_up+u_down<=4p-2 (a=d'_s,b=d'_t); a-b=2p(h-k)+6(I-J). Direct d422023 shows zero and two strata cost <=10 PER SOURCE by nonreuse. One-stratum requires w_s>=p-1 and exact return l=m-1 (m=(q_t-q_s)/2, l=((n_t-2J)-(n_s-2I))/p positive). Thus m>=2 and E_st=(2m-1)p+1-2(J-I)>=3p-1. In particular same-label one-stratum transfer never occurs with E<3p-1. These conditions are independent of the source/consumer choice.

For each actual source s let c_s be its retained cross-label mass, b_s its one-stratum mass, x_s its exceptional mass <=10, a_s=c_s+b_s+x_s its original retained matched weight. If b_s>0, choose its earliest retained one-stratum consumer t. Source postheight a=2ph+6I, target postheight b=2p(h-1)+6J. All such target down intervals lie in the union [2p(h-1),2p(h-1)+p+3], so b_s<=p+3. Set hi=2ph, lo=hi-p+3. Positive overlap implies source preheight < target preheight <=lo and source postheight>=hi. Each height in [lo,hi) is therefore first crossed DOWN after s and strictly before t (t's preheight <=lo). Its most recent upward event is exactly s. No such first down can have label p: a p-down interval of length <=p-3 starting at a possible postheight 2pj+6K is disjoint from [lo,hi), up to endpoints, for p>=11. Hence this compulsory buffer gives p-3 units of actual distinct-label consumption, before the earliest retained same-label consumer. In particular its E,U are bounded by those of that consumer, including if we first restricted all original retained pairs to bounded residence. The buffer may include original cross-label units; do not add both credits blindly.

For EACH source retain either its original c_s cross-label matches or a submeasure of its buffer of size min(b_s,p-3), whichever is larger. All chosen units are actual chronological last-up matches on the SAME tag, in the same fragment. A source's extracted mass a_s^cross satisfies
    a_s^cross <= a_s,
    a_s^cross >= [(p-3)/(2(p+3))] (a_s-x_s).
So, summing, at least (1/2-o(1)) of retained original middle mass is converted to cross-label mass, since sum x_s<=10NH/(Y-1). This improves the use of the direct mandatory-buffer argument for transport with *source weights*: it preserves any prior restriction on actual source occurrences (including same-label return gaps), never adds a new source or increases its weight. Across sources no duplicate height consumption, by last-up uniqueness. It also preserves the two residence cutoffs E,U<=A M_* pointwise. It is not an additive credit to XXVIII's original matched mass.

Guard enlargement: within each retained fragment take the union of original guard components [a,b] extended to [a,b+2R0]. Each original component has length >=Y-1 since made from selected intervals of length g>=Y-1. Thus enlarged width <=M_*(1+2R0/(Y-1)). The compulsory buffer belongs to this enlargement since its hi <= d'_t+2p and lo>=d'_t for p>=11. Original cross units also inside. Each actual event is in one fragment, so this width caps ALL extracted units ending at a given consumer, even if many sources serve it. We retain no credit for upward matches across unrelated fragments. When M_*,R0=O(Y) enlarged width M^+=O(Y).

## 2. Macro distinct-label transport on comparable narrow guards

Suppose along an unbounded X sequence the hypotheses of XXVIII's macro matched middle population hold: small strengthened missing, core low NONRESET gain p<Y=o(NH), macro selected fast core gain F>=rho NH, Y->infinity, L>=B Y^epsilon, M_*<=K0 Y for fixed K0, and every retained chosen consumer label >=Y. Nonempty guard forces p_consumer<=M_*+1; original middle sources use R0=max(Y,1+ceil(M_*/delta))=O_rho,K0(Y). XXVIII gives macro local matched middle source mass, actually consumed by selected fast core events. Retain E,U<=A M_* using both moment tails with A sufficiently large fixed. Extract cross matches by section1. Total remains >=c NH for some fixed c>0. Original source occurrences lie in exact common cores, but new buffer consumers need not: discard noncore consumers, costing at most G_omit=o(NH) since every actual down <=g and no reuse. This follows from XXI–XXII, not an assumption that every intervening event is a core event.

A buffer target may have d'<=6, but a label r<Y<=p cannot descend from a buffer height >=p+3 to <=6, since its down length <=r-3. Hence ALL low-label extracted consumers are nonresets (original selected consumers already high). Their total cost <=core low nonreset gain=o(NH). Large consumers r>R1 cost <=M^+ NH/(R1-1); choose R1=K1 Y, fixed K1 sufficiently large to leave macro mass (or cap by B). This bounds both endpoint labels in [Y,O(Y)] without assuming any particular label at a buffer first descent. No need to treat the buffer consumers as fast or rough.

Further strengthen endpoints by deleting weak sources or weak consumers, i.e. up length <eta p or down length <eta r. Cost <=eta sum p or eta sum r <=(1+o(1))eta NH each, by source/target nonreuse. Also delete pairs with positive net postheight difference a-b<=eta p or <=eta r. For fixed source, all such matched heights are in [a-eta p,a], giving <=eta p total, NOT once per consumer. For fixed target all such matched heights lie in [b,b+eta r], <=eta r total, NOT once per source. Thus these two deletions cost <=(2+o(1))eta NH. For sufficiently small fixed eta>0, macro cross transport remains and every retained pair satisfies
    p != r, Y<=p,r<=K2 Y,
    d'_s-d_s>=eta p, d_t-d'_t>=eta r,
    eta max(p,r)<d'_s-d'_t<=3p+r-2,
    0<=E_st,U_st<=A M_*.
This is a genuine directed net-height loss of order Y, not just two unrelated endpoint congruences. It also implies actual pre-to-pre horizon span <=O(Y). If the consumer is reset, then its preheight <=r+3; source preheight >=2ph+6I-3p-1, so overlap requires 2ph<=r+3p+4. Therefore sources with multiplier h>(K2+4)/2 cannot use reset consumers in this bounded-scale extraction. For any such deep-source subpopulation the macro extraction persists if its original mass is macro (choose the constants in terms of that mass). This is a source-depth/consumer-reset exclusion, not a claim that deep sources are forced.

Exact endpoint phase used in direct audit: C_s ≡ e_s+p(2I-2h-1) mod4p and C_t ≡ e_t+r(2J-2k-1) mod4r. For distinct labels and fixed pre-to-pre shift D=C_t-C_s, compatibility modulo4 is necessary and then a unique CRT progression mod4pr. This follows from n_s≡ I(p+2) mod2p and ordinary postdeficit 2ph+6I. The height multipliers are the actual ones, not independently selectable. We do not sum a speculative joint sieve over arbitrary h,k,D or count the downward endpoint as rough. The previous XXVIII short-relay count still applies to its own population, and may be applied to this extraction using M^+ and actual consumer supports.

## 3. Local diversity at recycling scale, preserving the long-bin support restriction

For the macro extracted population with E,U<=A M_* and endpoint labels comparable Y, set L_s=ceil(Y log²Y). Repartition each ORIGINAL tag's prehorizon line into half-open short bins of width L_s, and intersect with its old long bins (L_s=o(L)). Choose a common offset in {0,...,L_s-1} by averaging: a retained pair of prehorizons separated by Delta=O(Y) is cut by a short-bin boundary for at most Delta offsets. Thus some offset loses O(1/log²Y) fraction of extracted mass. No old-long-bin boundary loss since all matches already local. This uses integer actual horizons and weights, and retains complete events assigned by PRE-horizon. No new entry cost or assumption on total physical gain of a short bin (B can be much greater than L_s). At most O(N(1+H/L_s))=O(NH/L_s) short pieces. Retained comparable target gain per piece <=L_s+K2Y (actual first-to-last prehorizon span plus last selected gain), regardless of large omitted events. Thus extracted mass per piece <=2L_s eventually. Macro retained mass implies Omega(NH/L_s) busy pieces with >=c' L_s each.

Without extra hypotheses the direct short-interval two-form upper sieve on a fixed upward source p~Y gives total weighted capacity O(L_s/(loglog Y)^2) per label on these pieces; parameter length padded ceil(L_s/p)+2=O(log²Y), use the upper bound on a FULL interval of length L_s even for truncated pieces. Actual source matched weight <=3p+1. Hence each busy piece needs Omega((loglog Y)^2) distinct source labels. This imports d422023 without a repeated guard-entry charge or per-piece initial deficit.

Now additionally assume original long-bin ACTUAL matched weighted source support sum D_s<=D0 (NH/L) log²Y (XXVIII) and polynomial upper p<=const Y^b, automatic in comparable band. Before extraction discard the small original matched weight of sources not satisfying BOTH preceding/following gaps m>=a0 log²Y in their original selected middle source lists, by XXVIII. Choose tolerance sufficiently small relative to original macro mass. Even after residence truncation and cross extraction, every surviving source is one of those actual good sources; extraction never increases its mass and does not introduce new sources. Gap between any two consecutive surviving good sources of a fixed p in a long bin >=2a0 p log²Y-2, including intervening discarded visits. So any short piece of length L_s contains O_(a0)(1) such source occurrences PER LABEL. Each supplies <=3p+1<=O(Y). A busy piece consequently needs
    #distinct actual extracted source labels >= c'' log²Y.     (1)
This strengthens the direct loglog²Y short-bin diversity in the near-minimal long-bin support regime. Both the short-bin cross-label mass and diversity are tagged counts; many tags can be on the same physical trajectory. This is compatible with long-bin D_s=Theta(log²Y) (the same labels could be used in many short pieces); no contradiction from multiplying short-bin support by number of bins. It identifies a high-utilization requirement on the SAME source population. No upper on those labels' simultaneous supply has been proved. If long-bin support is not near minimal, only the first diversity bound follows. No forced narrow guards, low nonreset scarcity or small missing.

## 4. Diagnostics

Run node research/min_unified_cross_buffer_recycling_audit.mjs 4096 16384 65536. Extended actual six prime-root runs and 48 controls from XXVIII; finite residence cutoffs 4*cap, source-preserving choice, exceptional per-source cap, extracted cross geometry, endpoint phase, small net-height caps (eta=.1), finite short-bin fixed offset (not asymptotic averaging), target gain and actual occurrence spacing. Finite one-stratum matches may be absent; independent interval-geometry controls test the mandatory buffer, not actual one-stratum MIN paths. No claim finite data satisfy near-minimal asymptotic support; no full cumulative kernel, independent sieve constant certification or Lean verification. 
```json
{
  "totals": {
    "controls": 48,
    "crossMass": 306470,
    "oneMass": 120,
    "exceptionMass": 2618,
    "extractMass": 306478,
    "extractPairs": 13572,
    "phaseChecks": 13572,
    "bufferUnits": 260,
    "oneSources": 28,
    "depthReset": 0,
    "nearHeight": 7086,
    "strongMass": 298202,
    "shortBinMass": 181680,
    "shortBins": 6779,
    "shortLabels": 7040,
    "spacingChecks": 119
  },
  "geometry": 42912,
  "valid": 21456,
  "units": 1057560
}
```
Main/direct unchanged. Next: in busy short pieces bound cross-label supply using actual endpoint height support and joint phases, or show near-minimal repeated-label utilization impossible; high-support and macro-missing alternatives remain. Final NT-scale strict gap open.
