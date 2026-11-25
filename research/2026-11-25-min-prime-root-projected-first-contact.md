# Projected first-contact pair budget for the gain-stopped prime-root hybrid

2026-11-25 JST. Continues a5e11196ff5d675f6d281a797780f609207fe8a1 on research/min-prime-root-repeat-energy-2026-11-25. Imports the deterministic reverse-horizon coding idea of 396976cb39d5 (parallel short-clock branch), but uses the longer gain-stopped prime-root ensemble and first common HORIZON, not first common physical state. New unconditional deletions of whole source-pair energy classes, including asynchronous contacts and later recontacts. The residual high energy and medium moment remain OPEN. Paper proof and finite audit, no Lean compilation or novelty assertion.

## 1. Full projected paths and exact energy decomposition

Use the original canonical MIN prefix of a5e1119 with T=floor(X/(log B)^(1/4)), B=ceil(sqrt(7X)), N prime roots M in [X,2X), initial (s,C0)=(M+2,2M-2), and original cutoff K(M). Include the final vertex, whether twin, original cutoff, or first postgain >=T. The full vertex list of one source has strictly increasing horizons, so a source visits each C at most once. Its total gain G_M<T+B. Write C_end(M) for its final horizon.

For any retained high-event incidence set I (in particular the one after all preceding hybrid accounting deletions), let I_M(C) be its 0/1 indicator and W(C)=sum_M I_M(C). All I_M(C)=1 imply an actual pre-event at C. Write
    E=sum_C r(C) W(C)^2,
    R_I=sum_C r(C) W(C).
For two distinct roots M,M', let J(M,M') be their FIRST common horizon in the FULL vertex lists, if it exists, irrespective of time, cutoff flag, or accounting deletion. Define
    e(M,M')=2 sum_C r(C) I_M(C) I_M'(C).
Then exactly
    E=R_I+sum_{unordered M!=M' with common horizon} e(M,M').
The diagonal R_I=O(NT)=o(T^2 B). The common horizons in e are all >=J. Since r<=p<=1.5(p-1), the disjoint gain intervals after J in either original source show
    e(M,M') <= 3 min(C_end(M)-J,C_end(M')-J) <= 3(T+B).    (1)
This bound covers every later common horizon, whether the physical trajectories merge, split in projection, or recontact. If J is a terminal vertex for one source, the contribution is zero. Unlike physical common-suffix identities, it does not require a deterministic successor on the projected horizon graph.

At a non-root first contact the two incoming labels MUST be distinct. Indeed an incoming p ending at J comes from the pre-horizon J-p+1; if both labels were p the two sources would have an earlier common horizon. If one root starts at J, the other has an incoming label, and there is at most one root at any J. The same observation applies if both paths last selected the same large label p at the same post-horizon D<=J before only LOW jumps: they share D-p+1<J already. All classifications below use the full prefix, even when the first contact itself is not retained.

## 2. Nearby source pairs

Write u=log B, l=loglog B. Take d=floor(B u^(3/2)). For sufficiently large X, d<T/2. By the uniform prime interval upper bound, each prime root has O(d/log d) other prime roots at distance <=d. Thus the number of unordered near pairs is O(N d/log d). By (1) their entire ordered contribution is
    E_near << NT d/log d
           = O(T^2 B/u^(1/4)) = o(T^2 B),
using N=Theta(X/log X), T=Theta(X/u^(1/4)). This is a deletion by ROOT SEPARATION, not by pre-gain near the root. It is valid without any restriction on how late or how often near roots contact.

## 3. Reverse-complexity cap and an unconditional whole-pair bound

Choose y maximal such that L=2 product_{3<=p<=y} p <= l^(1/4), for sufficiently large X (finite diagnostics use fixed L=6,y=3). Then LOW-only blocks of selected primes <=y have total gain <L, so they have fewer than L/2 jumps. For even D let d_y(D) be the number of distinct odd primes y<p<=B dividing D or D+2. Every actual non-LOW label p has one such post-horizon D (p|D or p|D+2).

For every actual source and visited vertex C define the integer reverse complexity
    kappa_M(C)=L product_{non-LOW hits before C} (L d_y(D_i)).
It is monotone in its original prefix, unchanged by LOW steps. This is the uniform-candidate version of the adaptive Kraft construction in 396976cb39d5. It suffices here and permits exact capped integer audit. For each fixed C,
    sum_{M visiting C} 1/kappa_M(C) <= 1.              (2)
Proof: reverse from C, choose an even LOW offset e in [0,L) with weight 2/L, stop with factor 1/2 or choose continuation with factor 1/2 and a uniform candidate prime from d_y(C-e), then move to C-e-p+1. Empty candidate sets lose continuation mass. The total weight of outgoing choices is <=1, and reverse horizons strictly decrease. Restrict to valid initial horizons when stopping. Compress each actual prefix into its reverse LOW offsets and non-LOW labels; its leaf mass is exactly 1/kappa. Distinct original roots identify distinct leaves. This proves (2) by induction on the reverse tree, without assuming independence or unique time reconstruction. In particular at most floor(tau) visiting roots can have kappa<=tau.

In addition to the pointwise cap, one actual root has only
    O(L(1+log tau/log L))
visited vertices with kappa<=tau: there are at most log(tau/L)/log L completed non-LOW hits while good, and each intervening LOW block has at most L/2+1 vertices. If tau<L there are none. This prefix LENGTH bound follows from the same product, not from a physical first-meeting expiry argument.

Let tau_g=floor(B/sqrt u). Count pairs whose first projected contact occurs with BOTH histories having kappa<=tau_g. Each good vertex incidence can see at most tau_g-1 other good roots there. Therefore the number of these unordered pairs is at most
    O(N tau_g L(1+log tau_g/log L)).
Using (1), the whole later energy of this class is at most
    E_gg << NT tau_g L(1+log tau_g/log L)
         << T^2 B L/(u^(1/4) log L) + T^2 B L/u^(5/4)
          = o(T^2 B).
There is no need for the two histories to remain good, or even for them to follow the same future projected path. This is why the ordinary good-vertex count suffices on this longer gain scale. It is NOT the previous short-clock expiry theorem (which required a common physical suffix and had a different threshold). Current good-tag contributions would also be negligible by E<=2 tau_g R_full for pair incidences involving a good current tag, but that alone would miss pairs that later become bad; (1) handles the whole pair.

## 4. Recent-high groups and one-sided thin mass bounds

Choose a second large cutoff P=ceil(B/u^(1/4)), distinct from the retained high cutoff Q=ceil(B/log B), with P>=Q eventually, and tau_s=tau_thin=max(1,floor(u^(1/4))). Say a vertex incidence is recent-high if the last non-LOW label before it was q>=P. Let D be that label's actual post-horizon. Only LOW jumps occur from D to C, so
    0<=C-D<L.
For this recent-high incidence use group key (D,q). For each fixed C the number of distinct possible recent-high keys is O(L): there are L/2 possible D, and each D(D+2) has O(log X/log P)=O(1) distinct prime divisors >=P. This counts label/horizon keys, not roots, and holds with arbitrary ancestry.

Each source has <=G_M/(P-1) selections >=P; each such selection can supply at most L/2+1 subsequent recent-high vertex incidences (including its immediate post-vertex and possible terminal). Hence the total V_recent of these incidences is
    V_recent <= (L/2+1) sum_M G_M/(P-1) = O(NT L/P).   (3)

A. First contact with one recent-high history and the OTHER history having kappa<=tau_s: for each recent-high incidence there are at most tau_s possible other roots of that complexity by (2). All such first contact pairs number <=tau_s V_recent (orientation overcount harmless). Their whole later energy is
    E_rs << NT^2 L tau_s/P
          << T^2 B L/u^(1/2) = o(T^2 B).
The recent-high root can have arbitrarily large ancestry. This includes contacts at an initial root of the other source eventually, since kappa_root=L<=tau_s. It does not require the other source to be recent-high.

B. First contact with BOTH histories recent-high and at least one of their two groups having total mass <=tau_thin at the contact horizon: mass here means all actual original source tags with the given key, not just retained high tags. Their two keys must differ by section 1. The total mass of all thin recent-high groups at any C is O(L tau_thin). Charge the pair to its other recent-high incidence (or both orientations in a tie). By (3) the number of such pairs is O(L tau_thin V_recent), and their whole energy is
    E_rt << NT^2 L^2 tau_thin/P
          << T^2 B L^2/u^(1/2) = o(T^2 B).
This is a genuine pair bound even when the other group has arbitrarily many roots. It does NOT bound pairs with both recent-high groups thick. If the other side is not recent-high, a thin group alone is insufficient; only A or another criterion can be used.

C. A first contact at a root vertex with the other history recent-high contributes at most V_recent pairs, because at any C there is at most one original root. This separate bound is useful even for finite tau_s<L and is asymptotically contained in A. Energy O(NT^2 L/P)=o(T^2 B).

All four exclusions (near pairs, both-good first contacts, recent/small, recent/thin, plus redundant recent/root) may overlap; the sum is an upper bound for their union. These are pair-energy exclusions, not deletion of the participating source tags from the linear clock budget. They apply to ANY retained high incidence set, including the full high set, since (1) uses the original gain budget.

## 5. Physical clock congruence at a common horizon

The preceding projected first-contact classification does not assume equality of times. For comparison, at a physical common vertex (t,C) define delta=2t-C. The horizon invariant and elapsed time bound give
    0<=delta<=6+5(T+B), delta even,
since delta=6+2(t-s)-G_so_far and t-s<=3G_so_far.

An incoming p satisfies p|C and t=0 mod 2p if the event time is even, or p|(C+2) and t=p+2 mod 2p if odd. Hence
    2p | delta-epsilon, epsilon=0 (even t), 6 (odd t).
Two distinct incoming p,q at the same physical vertex therefore satisfy
    2pq | delta-epsilon.
In particular if 2pq>6+5(T+B), then delta=epsilon exactly (the reset line); e.g. both p,q greater than sqrt((6+5(T+B))/2) suffice. This restricts the very-large mixed physical meetings on the gain prefix, not the asynchronous projected contacts. It does not bound ancestor products on the reset line. The equality can occur at a later physical synchronization after an earlier asynchronous contact. If the incoming labels are the SAME, first physical synchronization can still occur, because the predecessor horizons agree but times can differ. It is not a first projected contact.

There is no physical root injection for a prime root M with B<M: at its time M+2 (odd), an incoming p would have p|(t-2)=M, impossible. But a projected contact at its initial horizon is entirely possible with different times. This distinction is important in using prime roots.

## 6. Residual energy criterion

Partition unordered first-contact pairs by priority: near, both-good, recent/small, recent/thin, recent/root, remaining. Let E_bad be the sum of e(M,M') of the remaining class on the fully retained high incidences of a5e1119. The diagonal is negligible and all the preceding excluded pair classes have combined energy o(T^2 B). Thus
    E_h = E_bad + o(T^2 B).
This is an equality up to a nonnegative controlled remainder, not merely a new sufficient condition with an unbounded discarded energy term.

Remaining pairs have separation >d (and <(T+B)/2 if they meet), at least one kappa>tau_g at first contact, if one side is recent-high then the other has kappa>tau_s, and if both are recent-high both groups are thick. Recent-high/root contact is excluded. Low/medium incoming and more complicated histories remain important. The remaining E_bad=o(T^2 B), together with the preceding medium Z_m=O(N B log^3 B), on the SAME unbounded dyadic sequence, would imply R=o(NT) by a5e1119 and hence twin-prime infinitude. Both estimates remain OPEN. The first-contact budget (1) can also be used with the actual minimum remaining gain instead of the crude uniform cap when studying this residual; no bound on its sum over the bad pairs is claimed.

## 7. Reproducible audit and finite observations

Standalone ECMAScript research/min_prime_root_projected_first_contact_audit.mjs, exact remote readback at d7b5cf1417baad718dc042a16c3c68f7d70c5d02, blob d4e4fc69319d955a813d5385e1f4159f07ef69e1. Run:
    node research/min_prime_root_projected_first_contact_audit.mjs 256 1024 4096 16384 65536 262144
Executed the audit function in the ECMAScript tool runtime, not a separate Node invocation. All 18 window/mode combinations passed. Literal parity-GCD comparisons on X256 and X1024: gain1719, short1183, four1707, identical to preceding prefix audit. All actual vertices, including terminal and root. For every unordered root pair, sweep increasing C and identify first projected contact independently of first physical synchronization. Verify distinct incoming labels or root, distinct recent-high keys at first contact, integer capped Kraft bounds and good prefix lengths, actual recent-high counts, all independent pair-count inequalities, exact energy partitions for both full p>=Q and the trim/relative-cheap/rank residual, and exact per-pair remaining-gain bounds. All finite energies are safe integers, independently recomputed via W(C)^2. Check physical non-injection, mixed deficit product congruence and large-product reset gate at actual first physical synchronizations. The retained incidence test is the previous fixed diagnostic trim/ratio/rank alone, not the entire cumulative hybrid; classification bounds hold for arbitrary retained subsets.

Mode short uses T=B, mode four T=4B; both use fixed y=3,L=6, P=ceil(B/4) with min5, tau_g=128, tau_s=tau_thin=12, near d=floor(B/64). Mode gain uses asymptotic T, P, tau,d formulas but same fixed L6, and retains fixed trim/ratio/rank diagnostic. Gain mode finite d is larger than all observed actual separations, and most roots terminate long before T; it cannot test the asymptotic bad class. Diagnostics intentionally use much smaller d to exercise all first-contact classes. No extrapolation of finite fractions to the limiting bounds.

| X | T=B all first projected pairs | simultaneous first contacts | root contacts | later first physical synchronization |
|--:|--:|--:|--:|--:|
|256|84|2|30|29|
|1024|275|20|82|not tabulated|
|4096|1756|112|426|not tabulated|
|16384|9463|432|1899|not tabulated|
|65536|48967|2164|6974|17355|
|262144|234035|9405|29248|82352|

At X262144, T=B=1355, N20390, 464179 events, 484569 vertices, 4992 crossings, 15398 twin terminal roots. 224630 asynchronous first projected contacts and 9405 simultaneous; 204787 non-root first contacts with necessarily distinct incoming labels, 29248 root contacts. 91757 pairs eventually have a physical common vertex within prefix; of 82352 later first physical synchronizations, 81563 have the SAME incoming label. There are 10194 first physical synchronizations with distinct labels, 10104 reset, 1479 satisfying the large-product gate (all reset). Maximum good current mass4, recent groups2, total horizon mass42. Independent first-contact class counts (overlaps allowed) gg2752, recent/small1345, recent/thin207, recent/root672.

Largest X, disjoint priority ledger:

| T | class | first pairs | ordered full high pair energy | ordered diagnostic retained high pair energy |
|--:|:--|--:|--:|--:|
|B|near|19344|10567530|208862|
|B|bothGood|135|68072|780|
|B|recentSmall|1325|335672|0|
|B|recentThin|200|44062|0|
|B|rootRecent|0|0|0|
|B|remaining|213031|71095508|611650|
|4B|near|19473|14574976|1087300|
|4B|bothGood|135|100354|2594|
|4B|recentSmall|1978|1208440|59932|
|4B|recentThin|459|190532|0|
|4B|rootRecent|0|0|0|
|4B|remaining|344929|190426728|10938164|

For T=B, full high diagonal7273605, full E89384449; retained diagonal179475, retained E1000767, matching a5e1119. For T=4B, full diagonal9807301, full E216308331, retained diagonal767205, retained E12855195. The new removed classes thus have nonzero actual full high contributions, including recent/thin (which happened to vanish in the fixed retained diagnostic). At T=4B, retained remaining energy10938164 is still the largest part, not a numerical certificate of the unresolved asymptotic bound. All 18 exact audits pass; no Lean compilation.

## 8. Next target

Study first contacts at low/medium incoming horizons where at least one history has kappa>tau_g and the other may be high-complexity too, and both-thick recent-high group products. For the physical subset exploit the reset congruence and later same-label synchronizations, but projected first contacts with different times need their own arithmetic control. The exact remaining-gain pair budget permits gain-weighted first-contact bounds rather than uniform suffix costs. No bound for the main bad class or the medium moment has been established here. Main and other branches unchanged.
