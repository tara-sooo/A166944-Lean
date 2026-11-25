# Growing-depth rare-set reverse expansion and bounded-ancestry first meetings

2026-11-25 JST. Continues d30e5353b9e90202315c143a3132d6f1cd5a8edc (shallow high-factor exposure), 396976cb39d54785b6c502bb24d7786c5e247973 (Kraft/expiry), and the short-clock slab at 25473614cf384cff0d8af534e34404cd774ae053. New unconditional rare-set pullback theorem for GROWING non-LOW depth, and an actual source-pair cap for all first meetings with both histories below that depth after rare-root removal. This removes the fixed two-medium restriction and the small/large interleaving gap for the rare-set deletion. No full energy bound or twin-prime proof. Paper proof, not Lean-compiled.

## 1. Setup

All original odd roots M in [X,2X), N=X/2, X dyadic, B=ceil(sqrt(7X)), s=M+2, C0=2M-2, K(M)=floor((7M-1)/4). H=4B, a=2B; assume H+2B<=min(K-s), eventually. Keep all actual prefix states up to and including the first post-event vertex after the relative H cutoff, if any. Stop at a twin. As in the previous clock notes, r(C)>0 is the least active odd prime, waits <=2r(C), and C<=2t. All horizons lie in V={even C:2X<=C<7X}. The per-root linear slab cost R_M=sum r(C)w_M(C)<=B, where w is the relative [a,H) fractional clock weight. Thus deletion of o(X) entire original source tags removes o(XB) linear cost; under the no-twin hypothesis the remaining R=(N-o(X))B. It does NOT imply negligible energy of the removed pairs.

Put ell=log log B, S=max(1,log ell), L=largest even primorial <=6 S^(1/4), with LOW cutoff y (including L=2,y=2). Contiguous LOW-only gain is <L by the even-multiple barrier. A non-LOW event is a selected p>y. In this note DEPTH means the number of completed non-LOW events from the original source (not the number of distinct labels). Do not confuse this with the count of medium labels when large selections have already occurred.

## 2. NEW: uniform tail bound for reverse arithmetic degree

For even J in V define

    P_y(J)={odd prime p:y<p<=B, p|J or p|(J+2)},
    d_y(J)=|P_y(J)|.

The post-event divisibility ensures that any actual non-LOW incoming event has its p in P_y(J). For odd p the two divisibility sides are disjoint. Certainly

    d_y(J)<=omega(J)+omega(J+2)<=O(log B),

where omega counts distinct prime factors. This bound by itself is too expensive to iterate.

Let T=ceil(20 ell), and let D={J in V:d_y(J)>T}. We will use the total candidate EDGE mass of D, not merely its cardinality. Elementary divisor counting gives

    sum_{n<=7X+2} 2^omega(n) <= sum_{n<=7X+2} tau(n)
                             = O(X log X),

since 2^omega(n) counts squarefree divisors, while tau(n) counts all divisors. If J in D then at least one of omega(J),omega(J+2) is >T/2. Markov applied to the preceding finite sum gives

    |D|=O(X log B * 2^(-T/2)).
    Dedge := sum_{J in D} d_y(J)
          =O(X (log B)^2 * 2^(-T/2))
          =O(X/(log B)^4).                             (1)

The last bound follows because 10 log 2>6. No moment or uniformity estimate on the actual adaptive source distribution is used. The exponent 4 is a convenient weakened value. The definition and elementary estimates are uniform in y.

## 3. NEW: reverse set expansion for arbitrary rare horizon sets

For S0 subset V (in this section S0 denotes a SET; elsewhere use Sigma0 for the sieve cost sum), form

    Lminus(S0) = { C-e in V : C in S0, e even, 0<=e<L },
    Rev(S0) = { J-p+1 in V : J in Lminus(S0), p in P_y(J) }.

These are relaxed candidate sets, ignoring time, exact clock competition and source cutoffs. They overcount actual ancestors. All distinct horizons are counted once, even when many reverse paths reach the same horizon. Since |Lminus(S0)|<=(L/2)|S0| and d_y<=T outside D, (1) implies for EVERY set S0,

    |Rev(S0)| <= sum_{J in Lminus(S0)} d_y(J)
               <= (TL/2)|S0|+Dedge
               <= g |S0|+Dedge,                       (2)

with g=max(2,TL). No independence between S0 and D is needed; the entire exceptional edge mass is used at each iteration.

Take any initial set A subset V, define A_0=A, A_{j+1}=Rev(A_j). Induction using g>=2 gives

    |A_j| <= g^j (|A|+Dedge).
    |union_{j=0}^k Lminus(A_j)| <= O(L g^k (|A|+Dedge)). (3)

If an actual original root visits a horizon in A after at most k completed non-LOW events, its initial horizon is in that union. Proof: compress each LOW block into its even gain <L, and reverse the non-LOW jumps one at a time using the actual post-event divisibility. The final LOW offset reaches the original initial horizon. The map M -> 2M-2 is injective. Consequently

    #original roots visiting A at depth<=k
       <= O(L g^k (|A|+Dedge)).                        (4)

This counts distinct root tags, not the potentially enormous number of reverse words and not physical vertices. Unlike the fixed-word CRT argument, arbitrary interleaving and repetitions of small and large non-LOW labels are allowed. It is an upper bound for any prefix or whole actual path within the horizon window.

For |A|=O(X (log B)^(-sigma) poly(ell)), fixed 0<sigma<=4, the right side is o(X) whenever g^k<= (log B)^(sigma-eta) with fixed 0<eta<sigma. Here poly(ell) denotes a fixed power of ell, and L=ell^o(1). In particular k can be a constant multiple of ell/log ell, tending to infinity. Only this distinct-root deletion is claimed; (4) does not bound the total number of source-state incidences in A, or all pair products at those horizons.

## 4. NEW: prune exceptional-degree shallow histories to get a uniform actual root cap

Include D in A, and permanently remove the original roots that visit A at depth<=k. No clock is rerun. For any retained root visiting horizon C at depth<=k, all of its earlier actual post-non-LOW horizons J have depth<=k and lie outside D. Thus the compressed reverse word from C has at most L/2 possible LOW offsets at each step, followed by at most T possible non-LOW predecessor labels at each ACTUAL post-non-LOW J. In counting candidate paths discard the branches with J in D. There are at most k continuation steps, and a final LOW offset. The number of leaves of all depths <=k is bounded by

    m_k := (L/2) sum_{i=0}^k (TL/2)^i
           <= O(L g^k).                               (5)

Each actual initial horizon identifies exactly one original M. Hence for every C the number of retained actual roots visiting C at depth<=k is <=m_k, even at a common physical state with many other root tags. The count is uniform, not an average. It does not require every relaxed leaf to correspond to an actual root.

Call a retained tag GOOD until it first exceeds k completed non-LOW selections. The good-prefix property is monotone. For any physical vertex v let g_v be its number of GOOD original tags and e_v the number of those whose last GOOD vertex is v. As proved in the parent expiry lemma, the unordered pairs F_gg that first meet while both GOOD satisfy

    F_gg = sum_v (e_v(g_v-e_v)+binom(e_v,2))
         <= N max(0,floor(m_k)-1).                    (6)

Indeed both tags follow the same physical suffix until either leaves the truncated path; charge the pair at the earlier GOOD expiry. This identity also includes terminal vertices and final post-event vertices. Each unordered pair contributes at most 2B to the ORDERED shared-state slab energy of its entire later common suffix (including after either becomes bad). Therefore

    E_same,gg <= 2B F_gg = O(XB L g^k).                (7)

With U_g(C)=sum of fractional occupation weights of currently GOOD retained tags at C, (5) also gives

    E_kept - E_kept_notgood <= 2 m_k R_kept
                            = O(XB L g^k),            (8)

including different-arrival-time pairs and good-bad incidences. Thus if Lg^k=o(log^2 B), the above terms are unconditionally negligible at the short-slab target scale XB log^2 B. They may overlap, so combine by a union upper bound. No bound for the whole suffix of good-bad first-meeting pairs follows from (6), unless one has a separate root-deletion or pair estimate.

## 5. Application A: high-divisor exposure at growing MEDIUM depth

Retain Q=ceil(B/exp(sqrt(ell))) from d30e535. High exposure means p>=Q, p<=B divides any of C-1,C,C+1,C+2. Let A_high be this horizon set. The earlier elementary prime harmonic estimate gives

    |A_high|=O(X sqrt(ell)/log B).

Set A=A_high union D, k_h=floor(ell/(2 log g)), for sufficiently large B. Then g^k_h<=sqrt(log B), and (4) proves

    #marked roots = O(X L sqrt(ell)/sqrt(log B))=o(X).
    m_{k_h}=O(L sqrt(log B)).
    E_same,gg=O(XB L sqrt(log B))=o(XB log^2 B).         (9)

In particular k_h~ell/(2 log ell)->infinity. The fixed-depth interleaving restriction of the previous CRT+Kraft proof is no longer needed. The same argument with k=floor(theta ell/log g) works for any fixed 0<theta<1, giving a smaller saving as theta approaches 1.

For the following equivalence, MEDIUM is y<p<Q, LARGE is p>=Q. In a retained root, every state with <=k_h MEDIUM selections has had NO LARGE selection. Otherwise, just before its first LARGE, the non-LOW depth equalled the medium count, <=k_h, and the state had a high pre-event divisor, so the root would have been marked. Thus in this class MEDIUM count and non-LOW depth agree. It follows:
- Every first LARGE event of an unmarked root occurs after >k_h completed MEDIUM selections.
- Any first physical meeting at a high-exposed horizon where at least one history has <=k_h completed MEDIUM selections loses that shallow tag under the deletion. In particular this covers all such meetings with ANY incoming LARGE label, even if the other history is arbitrarily deep. The entire common suffix of that pair is absent from the retained energy.
- At a retained shallow state, all prior selected non-LOW p and the next p (if any) are <Q. The completed gain <=k_h(Q-1)+(k_h+1)(L-2); completed elapsed <=3 times this gain and the next wait <=2Q. The waiting interval ends by age <=(3k_h+2)Q+3(k_h+1)L=o(B), since k_h=O(ell/log ell) and exp(sqrt(ell)) grows faster. Thus in the late slab [2B,4B) all retained occupied states have >k_h completed MEDIUM events, eventually. In (6)-(9) one may define GOOD by medium count<=k_h on these retained paths.

The deleted source count is o(X) and the remaining shared-suffix deletion (9) is a genuine energy bound for pairs of retained GOOD histories. These are different types of bounds.

## 6. Application B: rough-clock exposure allows greater total depth

Let Z=ceil(B^(1/4)). Define A_rough={C in V: r(C)>=Z}, using only positive active r, not twin r=0. The established two-dimensional upper-bound sieve for C-1,C+1 (the S0 bound of 73458de8 and 25473614) implies

    |A_rough|=O(X/log^2 B).

Indeed both neighbors have no odd prime factor <=floor(B^(1/8)) for C in A_rough, and the two forbidden residues modulo each odd prime are distinct. Apply the same rough-count estimate at this smaller cutoff; the sieve remainder is negligible. This is an upper bound for rough pairs, not a lower bound for twins.

Now choose A=A_rough union D and k_r=floor(3 ell/(2 log g)). This is about THREE TIMES the displayed k_h. By (4),(5),

    #marked roots = O(X L/sqrt(log B))=o(X),
    m_{k_r}=O(L (log B)^(3/2)),
    E_same,gg=O(XB L (log B)^(3/2))=o(XB log^2 B).       (10)

GOOD here means <=k_r completed non-LOW selections (any size, including near-B primes). This restriction does NOT require high exposure to be absent.

Every occupied GOOD state of a retained root has r(C)<Z. There have been <=k_r non-LOW selections and <=k_r+1 contiguous LOW blocks; each LOW block has <=(L-2)/2 selections because each gain >=2. The number of completed waits and the possible pending wait is <=k_r+(k_r+1)(L-2)/2+1 <=(k_r+1)L. Each wait is <=2Z. Since all prior states on the path are also good,

    age at end of any good wait <=2 Z (k_r+1)L=o(B).    (11)

Hence for sufficiently large B there are NO retained occupied GOOD states in [2B,4B). If a retained root has not reached a twin before age 2B, it must already have completed >k_r non-LOW selections by that age. This is a growing lower bound on depth, not termination or a bound on the remaining clock budget. It applies even when some of the selected labels were near-B but their actual waits were short. Under a no-twin window, all but o(X) roots therefore have depth >k_r by age 2B.

Both root deletions (sections 5 and 6) can be imposed simultaneously (union of o(X) original tags); their pair cap conclusions remain valid on the smaller retained family. The two good predicates have their own depths and must be kept distinct. A near-B incoming mixed meeting with a shallow MEDIUM history is covered by A; a mixed meeting at an actually rough horizon with shallow non-LOW history is covered by B, regardless of the depth of the other history. In the latter case the shallow tag is marked simply because that horizon belongs to A_rough. Neither theorem covers arbitrary mixed meetings at unexposed, low-degree, nonrough horizons.

## 7. Actual audit

Standalone ECMAScript research/min_clock_reverse_growth_audit.mjs, exact remote readback at 55b22460c03f8e85b0ffcf3151165e44149d2d06, blob ac0b0b4effd2dc7a0360b9c138e956a9b004756f. Run:

    node research/min_clock_reverse_growth_audit.mjs 1024 4096 16384 65536 262144

Executed the actual JS audit function in the available runtime, all five windows in each of five modes (25 runs). 4658 literal parity-GCD checks per X1024 mode. Constructs exact distinct-horizon relaxed reverse layers, counts edges including exceptions, checks (2) with the exact measured Dedge, and verifies that every ACTUAL marked original root is in the relaxed reverse union. Checks real clock and LOW-block constraints, original-tag deletion linear budget, good history horizon cap including terminals, exact first-meeting/expiry pair equality and actual retained fractional energy. For X<=16384 explicitly enumerates the charged good-good unordered pairs and their whole later shared suffix energy. Counts are integer, fractional energy uses numerical tolerances. Does not simulate a new wheel after deletion. The actual analytic growth depths both evaluate to k=0 in all tested windows; therefore fixed-depth diagnostics are needed to exercise the new recursion. Analytic modes do not empirically validate the growing-depth asymptotic regime.

Largest X262144, B1355, N131072, y3,L6, full prefix events3941922, R2373997.5, E184229117.19:

| Mode | Rare set | k | Actual marked roots | Relaxed candidate roots | Retained max good mass | Retained F_gg |
|---|---|--:|--:|--:|--:|--:|
| analytic | high Q333, T40 |0|88778|106745|2|0|
| narrow diagnostic | high Q1288, T40 |5|23405|130960|50|598012|
| degree diagnostic | high Q1288, T4 |3|98730|131024|17|45071|
| rough analytic | r>=7, T40 |0|63618|72968|2|0|
| rough diagnostic | r>=136, T40 |5|40098|130958|42|407705|

Narrow diagnostic reverse distinct horizon layers at X262144: [17836,93566,323871,568624,623065,625734]. Degree diagnostic has 93486 exceptional-degree horizons, edge mass508569, layers [107535,485274,617790,625696]; 94905 roots flagged by degree, 16840 by high exposure, intersection13015. Rough diagnostic layers [13419,112076,371604,588510,624477,625800]. These reverse relaxations nearly saturate the finite original source interval after several steps, despite actual marked root counts being smaller. This is an important limitation of finite arithmetic-only enumeration. The asymptotic theorem is the degree tail and recursion, not an extrapolation of these finite layers.

At X16384 narrow diagnostic: 1247 marked roots, 6945 retained, 92343 total retained unordered first meetings, F_gg=32281 exactly equals expiry count; whole ordered good-good shared suffix energy616435.89 vs retained distinct-pair shared-state energy1561510.98 (~39.5%). Rough diagnostic: 4105 marked, retained F_gg=10873, corresponding whole suffix energy27533.78 vs retained shared energy98110.36. At X262144 suffix energy not individually enumerated, but integer counts/expiry/cap verified. Retained E respectively 107289348.89 narrow, 9279464.21 degree, 50512658.26 rough diagnostic. These are finite diagnostics with many deleted roots; not proof that a negligible fraction is deleted at these sizes.

## 8. Remaining problem

This improves the previous two-medium rare-root deletion to a growing-depth theorem with arbitrary interleaving and repeated labels, and provides a simultaneous uniform good-ancestry bound by deleting exceptional-degree roots. It also supplies a deeper growing-depth rough-clock result. The remaining short-slab energy problem still requires control of high-depth first-meeting original-source products (including one good history at an ordinary low-degree unexposed horizon) and the asynchronous residual. In particular the very slow growth ell/log ell does not bound unrestricted long histories, and the exact reverse-time competition is still relaxed in this theorem. A next concrete target is to use the rare-set theorem at a moving depth boundary together with suffix transfer: count actual pairs first entering a common high-depth history from different incoming classes, retaining source-specific times. A uniform o(XB log^2 B) bound for the entire remaining energy has NOT been obtained. Main unchanged, no new Lean compilation, twin-prime conjecture OPEN.
