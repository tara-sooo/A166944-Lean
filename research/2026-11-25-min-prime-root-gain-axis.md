# Directed gain-axis occupation, including time-disjoint never-meeting pairs, and direct projected high ranks

2026-11-25 JST. Continuation of 72aa600b9fe6cc87697c961425718104b788a5e7. Two new unconditional absolute deletions for the original prime-root gain-stopped hybrid. The first compares paths on the common absolute HORIZON coordinate, not at a common physical clock time. It handles even time-disjoint far quota segments and does not assume comparable actual waits of the two roots. The second directly pays ordered high-energy pairs at a common projected horizon, without any first-meeting hypothesis. Neither proves the full residual. Paper deductions and actual finite diagnostics; no Lean compilation or external novelty claim.

## 1. Inherited actual ledger and a gain-axis measure

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, T=floor(X/u^.25), H=T+B, N=Theta(X/u), Q=ceil(B/u), m_g=u^(19/4)/ell^4. All paths are ORIGINAL canonical MIN gain-stopped paths (including the first crossing event or original cutoff/terminal), with the same fixed source cells, full sparse medium quota lists, gap-dependent phase cells and partner normalization. The per-root completed gain is <H and completed time W_M<=3H. No rerunning of MIN, no new allocation.

For every original completed event e with prestate (t,C), label p and next state (s,D) with D=C+p-1, put the half-open gain interval I_e=[C,D). For root M its completed intervals partition [2M-2,C_end(M)). Define a measure on the ABSOLUTE horizon axis by
    d mu_M(x) = (s-t)/(p-1) dx    on I_e,
and zero outside that range. Its mass is W_M, and for any two original visited horizons C<=F, mu_M([C,F))=t_M(F)-t_M(C). No terminal wait or extension beyond an original path is included. The gain coordinate x is the same absolute integer-horizon axis for all roots, not their separate gains since injection. At each x a root occupies at most one original event. It need not be at that event at the same physical time as another root occupying x.

For a directed far quota charge from M to M' at common earlier/later horizons C<E, let F be the end of the focal actual E-plus-LOW block. Set I=[C,F) and J=[C,E). BOTH roots have gain occupation throughout J regardless of the overlap or disjointness of their actual elapsed-time intervals. The extension [E,F) is used only for focal accounting. The charge uses the existing actual block length b_M(E)=t_M(F)-t_M(E)=mu_M([E,F)). For fixed M,M',E the total of all charges at E, including arbitrary subsets of earlier quota choices, is
    <= (C0/m_g)(P/Q)^(1/8) b_M(E),             (1)
where P is the dyadic band of the later least factor r(E), not necessarily any label at the current x. This is the inherited actual-relative endpoint inequality of 6aa99f5. The asymptotic constant is uniform.

## 2. Rank-limited directed gain occupation

At every x and fixed original source cell, take ALL currently gain-occupying original tags and their actual event descriptors
    (M,C,D,p,t,s,q),
where q is the previous incoming selected prime, or 0 at an original root. For a candidate partner cohort (any of the partitions below), define the source-order distance from a focal M to a member M' as the number of cohort roots in (M,M'] if M'>M, or [M',M) if M'<M. The focal need NOT be a member of the candidate cohort. A cap m admits at most 2m distinct partner tags, regardless of cohort mass or interleaving. This is a moving rank relative to the focal source, not an absolute numerical source distance and not the cohort's rank from its two ends.

Choose Y=max(5,ceil(B/u)), d=max(1,floor(u^.25)). For each later factor band P put a_P=(Q/P)^(1/16) and
    m0(P)=max(1,floor(a_P m_g/u^.25)),
    m1(P)=max(1,floor(a_P m_g/u^.5)),
    m2(P)=max(1,floor(a_P m_g/u^1.5)).
These parameters define a relation for a fixed band and coordinate, not a change in MIN or quota pools. A directed link from focal a to partner b!=a in the same cell is good if any test holds:
    0: partner rank<=m0 in the entire gain-active cell;
    1: C'=C, partner rank<=m0 in pre-horizon cohort C';
    2: D'=D, partner rank<=m0 in post-horizon cohort D';
    3: p'=p, partner rank<=m0 in (C',p') cohort;
    4: |C'-C|<=d with rank<=m1 in pre-horizon cohort, OR
       |D'-D|<=d with rank<=m1 in post-horizon cohort;
    5: p'>=Y, |s'-s|<=d, rank<=m1 in (C',p',s') cohort;
    6: q'=q>=Y, rank<=m2 in (C',q') cohort;
    7: q'>=Y, |t'-t|<=d, rank<=m2 in (C',q',t') cohort.
All ranks use the full original gain-active cohort, without paid masks. The relation is deliberately DIRECTED: mu_M and mu_M' can be quite different even on the same gain span. Symmetrizing and then using the focal's measure with the other endpoint's degree is not justified. The tests require no equality of physical ticks or common successor.

## 3. Uniform arithmetic degree bound

At fixed x, the pre-horizons of tags with chosen label p' satisfy C'<=x<C'+p'-1. The even C' thus lie in an interval of length p'-1, and p' divides C'+sigma(s'), where sigma=+1 for odd s' and -1 for even s'. For each sign they form a single residue modulo 2p'. Hence for a specified p' there are at most TWO possible pre-horizons, and for a specified p' and exit parity at most ONE. This is why test 3 costs at most 4m0 even if their physical exit clocks are widely separated.

For test 5, a fixed s' has at most O(1) odd prime divisors p'>=Y of the positive integer s'-2(s' mod 2)=O(X): their product divides that integer and log Y~u. Each such p' and the fixed parity yield at most one pre-horizon at x. Thus there are O(d+1) possible (C',p',s') cohorts. For test 7, a prescribed t' similarly has O(1) incoming q'>=Y. The incoming congruence q'|C'+2(t' mod 2) and even C' determine a residue modulo 2q'. Since ALL gain-active pre-horizons lie in [x-B,x], there are O(1+B/Y)=O(u) possible pre-horizons per label/parity. Thus O((d+1)u) fine incoming cohorts. For test 6 the given q'=q permits two parity residues, with O(u) possible pre-horizons, and the aggregate cohort includes ALL entry ticks, no extra tick multiplicity. Test 4 has O(d+1) candidate boundary cohorts. The remaining three tests each target only one cohort.

The total directed tag degree at each (M,x,cell,P) is therefore
    O(m0+(d+1)m1+(d+1)u m2)
       = O(a_P m_g/u^.25).                          (2)
This uses only original tag ranks and actual clock congruences. No assertion of sparse arithmetic state mass. In particular the relation admits partners deep inside an arbitrarily large cohort when close to the focal's source-order position. Equation (2) also includes all lower factor bands; floors/max1 are harmless asymptotically.

Write G_P(M,M') for the set of x where the directed link is good. By integrating (2) with respect to the FOCAL measure for each M,
    sum_(ordered M,M') mu_M(G_P(M,M'))
       <= O(a_P m_g/u^.25) sum_M W_M
       = O(a_P m_g NT/u^.25).                      (3)
The partner need not be physically active when the focal is. The disjoint fixed source cells ensure no cross-cell multiplicity factor. The relation may depend on P but not on C,E, the gap band, or a particular quota edge.

## 4. Weighted interval-cover transfer, including lower-band disjoint far pairs

Let eta=u^-1/16. Pay any remaining far charge (including time-disjoint) if
    mu_M(G_P(M,M') intersect J) >= eta mu_M(I).     (4)
For a fixed ordered pair AND fixed P collect the extended gain intervals I of all accepted charges (over all earlier-hit choices and gap bands), and let U be their union. Each distinct accepted later E has its actual E-plus-LOW gain block [E,F) contained in U. These blocks are disjoint on the focal original path. By (1) their total accepted charge is at most
    (C0/m_g)(P/Q)^(1/8) mu_M(U).
Choose a subfamily of extended intervals with EXACT union U and ordinary geometric multiplicity at most two (the established minimal-subcover lemma). The same multiplicity bound holds for the absolutely continuous measure mu_M. By (4),
    mu_M(U) <= sum_chosen mu_M(I)
       <= eta^-1 sum_chosen mu_M(G_P intersect I)
       <= 2 eta^-1 mu_M(G_P).
This argument uses no comparability of two actual waits, no conversion of the partner's gain weight into the focal's time, and no need for the two actual elapsed-time intervals to intersect. Sum over ordered pairs and use (3), then sum over dyadic P:
    W_gain << NT/(eta u^.25) sum_P (P/Q)^(1/8) a_P
           = O(NT/u^(3/16))=o(NT),                 (5)
since a_P=(Q/P)^(1/16) gives geometric summability. This is a new absolute actual-clock deletion after any earlier far masks, including two-clock concurrent occupation. It can pay lower-band time-disjoint pairs, not paid merely by the earlier upper-band fast-disjoint result. It can also pay never-meeting overlapping pairs. No hypothesis of a first waiting or physical meeting is used.

For each remaining far edge the directed good fraction in its common gain segment is <eta relative to its actual extended time, in addition to all prior residual conditions. For an upper-band slow edge the extension contributes o(1) fraction of the focal time (from c9054d2), so nearly all focal-time mass on the common gain segment fails all eight tests. For lower bands do not assert this last fraction without controlling the extension. Failure of the tests is not a quantitative bound on all other pairs.

## 5. Separate direct projected-rank high energy exclusion

Let F0=T²Bu (write F0 to distinguish from an extended event horizon F above). Freeze the full natural high incidence list I_high (p>=Q and r(C)>p/sqrt(log p)) before accounting holes. At each pre-horizon C its original tags have shared r(C), but may have different entry times, incoming labels and outgoing labels. For arbitrary retained subset J, R_J<=O(NT). We can bound ordered pair energy directly at C, rather than at a first physical meeting. In the full original list at C, form
- the global list in source order and separately the global list sorted by (physical entry tick, source);
- cohorts by previous incoming label q (including q=0 for an initial root), sorted by source;
- for each fixed aligned source-cell width d0, the per-cell cohort sorted by source.

In the global lists pay directed pairs with rank distance <=m0h=floor(B u^1.5), using either ordering. In any incoming-label cohort, pay a partner at relative source-order distance <=m1h=floor(B sqrt(u)) from the focal, even if the focal is not in that cohort. There are O(u/ell) possible positive q, since each divides C(C+2), with at most one extra root cohort. The total directed degree of the first two classes is
    <=4m0h+O(m1h u/ell)=O(Bu^1.5).
This treats asynchronous pairs directly, including far physical times but nearby chronological rank. It does not require either endpoint to be near an end of its own branch, small physical merger mass, or any previous matching state.

For a fixed source-cell scale d0=B2^k<=B u^2.25, also allow relative source-order rank <=m_d=floor((d0/B)u^1.75) within ANY partner cell, including different cells. At a common pre-C the roots lie in a source interval of length <T/2, so only O(1+H/d0) cells occur. Directed degree per scale is
    O(m_d(1+H/d0))=O(Bu^1.5).
The term m_d alone is negligible since d0<=B u^2.25. The same bound permits chronology order inside each partner cell, if desired, by taking distance in the sorted list relative to the focal's (t,M); not needed in the finite audit.

For each scale, and separately for the global/label tests, the ordered high energy covered is bounded by
    O(Bu^1.5) sum_C r(C) W_J(C)
       = O(Bu^1.5 NT)=O(F0/u^.25).
Here one counts only pairs with both endpoints in J, using full frozen lists for the ranks. Union over O(1+ell) scales and with previous energy exclusions gives o(F0). If one wishes to symmetrize, the ordered union bound gains at most a factor two, because r(C) is identical for both directions (unlike section 4). This is an absolute energy-slice bound, NOT a linear deletion of incidences or a bound on full ancestry mass. It applies to synchronous AND asynchronous pairs. In particular the previous first-physical-meeting and asynchronous exit-phase residual can also be restricted by these direct projected rank tests. When using a previous relative absorption inequality, subtract only the newly covered actual retained ordered energy in its remaining terms; do not count previously paid pair products twice. The direct bound is valid without invoking that inequality and can be unioned at the actual retained energy level.

## 6. Reproducible audit and results

Derived standalone ECMAScript research/min_prime_root_gain_axis_audit.mjs. Latest source commit c52d2a2426d29a3b9d405c581426f3cdcfa12361, blob 6e648ff2a78d8bf5e608be98d4be41d82667f715, exact remote readback. Commands:
    node research/min_prime_root_gain_axis_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_prime_root_gain_axis_audit.mjs --crt-stress --gain-stress 256 1024 4096 16384 65536 262144

Actual audit function executed in the available ECMAScript runtime. Initial version: 28 runs, all seven modes at four X256..16384; ten additional runs at X65536/262144 (normal concurrent, combined CRT/gain stress, stress, analytic, wide). Final version adds 32 independent gain-coordinate control samples and individual arithmetic capacity checks before rank tests; all 18 final runs (analytic, concurrent, combined stress at six X) pass. Other final-version modes not rerun. Original canonical paths, previous exact ledger, waiting forest, entropy and prior CRT checks retained. New sweep of full original gain intervals at queried coordinates, all candidate degrees for queried focal/band, same-label horizon capacity and incoming/exit arithmetic independently verified, directed weighted deduplication and exact cover union; focal measure tested by independent binary-search oracle and actual endpoint time (floating rational weights with tolerances). Previous occupancy/CRT masks applied first, then gain-axis masks, then waiting/entropy masks recomputed on remaining charge blocks, so no double subtraction. High diagnostics are direct ordered counts on full natural high set, not cumulative high residual, with one source-cell scale only and source order (no chronology inside partner cells). Analytic finite quota residual empty; controls exercise arithmetic but not limiting prevalence. Gain-stress uses rank bases 8 instead of 2, CRT-stress as in previous checkpoint, not asymptotic parameters.

| X | normal previous never cost | new gain-paid never cost | new remaining never cost | new total residual |
|---:|---:|---:|---:|---:|
|4096|22.333333|18.5|3.833333|3.833333|
|16384|65.121212|11.265152|53.856061|53.856061|
|65536|16|2.333333|13.666667|66.6|
|262144|185.259259|67.203704|118.055556|169.852868|

At X16384 normal gain total15.265152 includes11.265152 never and9.113636 time-disjoint. At X65536 total2.75 includes2.333333 never/time-disjoint. At X262144 normal total67.20370370 (all never-meeting), 42.53703704 time-disjoint, 121 directed edges, 11694 queried pair-gain units, 1290 focal degree tests, max degree11, 63 accepted ordered pair/band covers, 3067.571429 deduplicated good measure within accepted interval unions. Previous entropy gap pays13.45410138 unchanged; total residual237.05657130 ->169.85286759. Combined stress largest: gain total154.05555556 (all never), time-disjoint119.72222222, 481 directed edges, 242 covers; previous CRT-stress never184.92592593 ->30.87037037, total residual236.72323796 ->82.66768241. At X65536 combined stress all remaining never cost15.5 paid. Final X262144 normal concurrent includes 32 independent controls,1671 arithmetic checks, max candidate cohorts [same label2, near exit2, same incoming1, near entry1]. Later arithmetic tests add no extra priority-paid finite charge at the largest normal scale; actual reduction mostly from relative source ranks and shared gain boundaries. Their bounds hold independently of numerical prevalence.

High largest concurrent natural set: total E=211641172 (including diagonal), direct ordered covered offdiag=118054019 (async49421359, sync68632660); incoming cohort adds5255908, source-cell adds45827265 beyond previous direct list tests (priority within this new classifier only), max directed degree42. Wide largest E311130640, direct covered173652019 incl async71206260. Analytic largest E218152748, covered208418956 (all natural offdiag). These are noncumulative finite control values, not additional savings over the complete high residual or asymptotic evidence.

## 7. Remaining mathematical task

The actual gain-axis relation now covers a substantial finite part of the specific previously untreated time-disjoint never-meeting class without changing the proof target. The remaining directed far segments must evade both the time-axis and gain-axis relations (with their respective density criteria), including long overlaps of gain-active groups with deep relative ranks. A possible next route is to prove an arithmetic restriction on sustained large relative gain-axis rank by tracking actual entry/exit words of the intervening source groups, or an independent prime-source reverse-fibre bound for those groups. The direct high-rank lemma isolates large relative source/chronology rank at each actual common horizon, not only at a first merger. Neither the general medium residual o(NT) nor the high residual o(T²Bu) is established. No full reverse-origin fibre theorem, Lean proof or twin-prime proof. Main unchanged.
