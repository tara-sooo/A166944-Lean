# Fourth-root roughness, cube-band packing, and a global three-way alternative

Continuation of [8b30078](https://github.com/tara-sooo/A166944-Lean/commit/8b30078811529f94c7ecafb1b66b4a646d266069) on the independent direct-arithmetic branch. This connects the previous square-band obstruction to the cofactor-composite regime by lowering the roughness threshold from a cube root to a fourth root. No short-return geometry, reset, historical merger estimate, or prime-pair distribution assumption. Paper proof, not Lean kernel verification. Twin infinitude and A166944 remain open.

## 1. Fourth-root long-wait events

At an adaptive event, H=pq+e, e=+1 even/-1 odd, q odd>=p, gain g=p-1, wait w<=2p<=3g, p^2<=H+1. Let all pre-horizons of a contiguous block be <=Y. Set B=1+floor(8*(Y+1)^(1/4)), C=floor sqrt(Y+1). Call an event fourth-root qualified if p>B and 4w>=p-1.

Every prime factor f of H-1 or H+1 satisfies f>=w/2. Indeed f<w/2 implies f<p, hence eligible, and its clock would occur within 2f<w. Thus for a qualified event f> (Y+1)^(1/4). Each neighbor has at most THREE prime factors counting multiplicity. The selected neighbor is composite, so either
    H-e=pq, q prime (type II),
or
    H-e=pab, a,b prime (type III).
There is no requirement that p,a,b be distinct. In type III,
    a,b >= (p-1)/8,
    q=ab >= (p-1)^2/64,
    p(p-1)^2 <=64(Y+1),
    p <= (144(Y+1))^(1/3)
using p-1>=2p/3. In particular q/p tends to infinity as p grows; these are automatically far-from-square in the previous sense for any fixed eps<1. This does not assert that all far events are qualified.

## 2. Exact three-way interval inequality

Write G total gain, W elapsed ticks, d initial ordinary deficit. Let U be gain from p<=B, V2,V3 qualified gains of types II,III. Other events satisfy 4w<g. The canonical envelope and individual clock bound give
    2W>=G-d,
    4W<=G+11(U+V2+V3),
    11(U+V2+V3)>=G-2d.
Thus for D=G-2d>0 one of U,V2,V3 is >=D/33.

For every sufficiently large crossed [X,16X], Y=16X, of a canonical infinite ray, previous global-roughness argument gives G-2d>=Y/4: start overshoot <=sqrt(X+1), d<=6+5(H-H0), and G-2d>=Y-11H_start-12. Therefore at least one of the three gains is >=Y/132. Under finite twins all canonical roots above the last twin center give such infinite rays.

Small-label branch U>=Y/132 now implies some p<=B has at least Omega(Y^(1/2) log Y) occurrences, because sum_{prime p<=B}(p-1)=O(B^2/log B)=O(Y^(1/2)/log Y), by elementary Chebyshev counting. This strengthens the required concentration compared to the previous cube-root cutoff (Omega(Y^(1/3)log Y)), at the expense of allowing type III.

## 3. The two-residue sieve works for type III too

The upper sieve proved in c27a25f requires avoidance of the two distinct roots, not primality of q. For fixed selected p and sign e, q and pq+2e have no prime factor <=(Y+1)^(1/4). For every odd prime l<=z=floor N^(1/12), N=floor((Y+1)/p), we have l<p and l below this roughness threshold for all sufficiently large Y. Thus q avoids 0 and -2e/p modulo l, even if q is composite. Also log N comparable to log Y, and repeated p>=5 visits have strictly increasing q. Summing the two signs gives per-label count O(Y/(p log^2Y)) and gain O(Y/log^2Y), for either type or their union. This uses the earlier elementary sieve proof, without external asymptotics for prime tuples.

If V2>=Y/132, discarding labels with fewer than Y/(264 A(C)) type-II visits, where A(z)=sum_{odd primes<=z}(p-1), loses <=Y/264 gain. Consequently Omega(log^2Y) distinct p each have Omega(log Y) type-II visits. The near-diagonal sieve from c27a25f also applies since q prime and p>B, so one may discard q-p<=alpha log^2Y for a sufficiently small fixed alpha>0, adjusting constants.

If V3>=Y/132, use C3=(144(Y+1))^(1/3) instead of C. Since A(C3)=O(Y^(2/3)/log Y), the corresponding rich-label threshold is Omega(Y^(1/3) log Y), and the per-label cap still gives Omega(log^2Y) distinct p with that many visits EACH. Total type-III event count is Omega(Y^(2/3)), because each gain <=C3. This is genuinely stronger recurrence for the triple-factor case. The lower bound on the span of q for m repeated qualified visits from the prior two-root sieve applies unchanged: span+1>=Omega(m log^2(2m)). None of these conclusions supplies a twin gap.

## 4. Elementary cube-band packing

Consider type-III events and define x=(p+a+b)/3, a positive multiple of 1/3; define deviations u=p-x, v=a-x, z=b-x, with sum zero. For any 0<eta<=1, call a triple narrow if max(|u|,|v|,|z|)<=eta sqrt(x) and x>=4. By AM-GM and expansion,
    pab = x^3 - (x/2)(u^2+v^2+z^2)+uvz,
    x^3-2 eta^2 x^2 <= pab <= x^3.
Indeed |uvz|<=eta^3 x^(3/2)<=eta^2 x^2/2 for x>=4. Thus the pre-horizon H=pab+e lies in [x^3-2 eta^2 x^2-1, x^3+1], a band of width 2 eta^2 x^2+2. A narrow event with this center has gain <=p<=x+eta sqrt x<=2x. For all events with the same center on any strictly increasing path, their jump intervals [H,H+p-1) are disjoint and contained in the band extended by 2x on the right. Hence their total gain is <=2 eta^2 x^2+2x+2. No assumption that such events are consecutive or share a label is needed.

Since x>=4, H>=x^3/2-1, so x<=2(Y+1)^(1/3). There are at most 6(Y+1)^(1/3) possible positive centers (multiples of 1/3). Summing the center capacity using the maximum center gives
    V3_narrow <=48 eta^2 (Y+1)+24(Y+1)^(2/3)+12(Y+1)^(1/3).
For sufficiently large Y, qualified type III has x>=4 automatically. Choose eta=1/200. Then 48 eta^2=0.0012<1/264. For sufficiently large Y, narrow triples contribute <Y/264. If V3>=Y/132, at least Y/264 gain remains on triples satisfying
    max(|p-x|,|a-x|,|b-x|) > sqrt(x)/200.
The same rich-label proof of section3 on this subset (discard low multiplicities using threshold Y/(528 A(C3))) gives Omega(log^2Y) distinct p, each Omega(Y^(1/3) log Y) such imbalanced triple visits. In particular their number is Omega(Y^(2/3)). Since x>=p/3 and p>B, the factor spread is at least Omega(Y^(1/8)); a stronger Omega(Y^(1/6)) spread would require x comparable to Y^(1/3), not asserted universally. In crossed [X,16X] actually H>=X and AM-GM gives x^3>=H-1>=X-1, so in those windows specifically x>= (X-1)^(1/3), and the spread is Omega(Y^(1/6)). This is a quantitative obstruction to a composite-only long-wait regime concentrated around cubes, not a proof that individual balanced triples are impossible.

## 5. Global result and stopping criterion

Every sufficiently large crossed [X,16X] of any infinite canonical adaptive ray satisfies at least one of:
(A) a selected prime <=8(Y+1)^(1/4)+1 has Omega(Y^(1/2) log Y) visits;
(B) Omega(log^2Y) distinct selected primes each have Omega(log Y) fourth-root qualified prime-cofactor visits;
(C) Omega(log^2Y) distinct selected primes each have Omega(Y^(1/3)log Y) fourth-root qualified triple-factor visits, with factor spread >sqrt(x)/200; all type-III q>= (p-1)^2/64, p=O(Y^(1/3)), and at least Omega(Y^(2/3)) such visits total.
Y=16X; constants absolute. All counted visits in (B),(C) refer to one contiguous path, not pooled sources.

If every fixed p occurs finitely often and its total multiplicity M(p)=o(p^2 log p), alternative A is eventually excluded: uniformly p<=B the multiplicity is o(B^2 log B)=o(Y^(1/2)log Y), separating finitely many primes. Thus an infinite ray with this multiplicity bound must have B or C in every sufficiently large window. In particular, if in addition all sufficiently large selected labels have composite cofactors, C must hold in every large window. If such a ray also has all sufficiently late fourth-root qualified triple-factor events confined to max deviation <=sqrt(x)/200, it must terminate (conditional stopping criterion). Equivalently eventual composite-only plus balanced-cube long-wait geometry cannot sustain an infinite ray with the stated multiplicity restriction. This is weaker than ruling out all composite-cofactor rays; neither low-label concentration nor the imbalanced triple regime is excluded. Finite twins alone does not imply that the prime-cofactor branch disappears.

## 6. Diagnostics

[Audit dd45a41](https://github.com/tara-sooo/A166944-Lean/blob/dd45a419d6e34dd7b9f2a3f477673f1c8e193730/research/min_direct_fourth_root_cube_audit.mjs), blob 2b4bb9da9f9b92d8bb64520479c552c6f6abfa2c, exact remote readback. Run node research/min_direct_fourth_root_cube_audit.mjs 200000 180. Actual ECMAScript execution in tool runtime (not separate Node process). All odd M<=200000, <=180 nonunit events: 2,278,154 actual events, 98,065 nonempty paths, zero range truncation, 4,031 literal GCD comparisons. 185,044 full-prefix/suffix interval checks; 138,837 positive demand; small branch valid 137,959 times, prime branch 54,390 times (overlapping). 91,398 qualified prime event-window incidences, zero qualified triple event-window incidences. 288,929 rough-factor checks. Therefore canonical scan does NOT provide empirical examples of the triple branch; it is a theorem of the inequality.

Two independent actual adaptive events from abstract plateau states (not canonical ancestry) with exact cube selected neighbor, positive envelope and fourth-root qualification: p5003, H125225135028,t62612573767,n62612575018,w1251,H-1=5003^3,H+1=11483*10905263; p5039,H127947874320,t63973943458,n63973944718,w1260,H-1=5039^3,H+1=127947874321 prime. Literal tickwise GCD checked all 2511 ticks. Thus balanced triple events are realizable locally. Independent relaxed cube-packing controls on odd integer factors (not requiring prime or clock realization), centers S/3 for odd S<=501, eta=1,1/2,1/4,1/200: 9102 band checks, 788 group checks. Initial scan attempt had an incorrect smallest-prime-factor sieve that overwrote earlier entries; literal comparison detected it, corrected to write only previously unset entries before running the reported counts. All final checks passed. No Lean kernel verification, no full-window asymptotic numerical claim. No external novelty claim. Main and sibling branches unchanged.

Next mathematical target: the new triple branch has long waits and much stronger per-label multiplicity than the prime-cofactor branch; exploit its two-factor cofactor decomposition, or derive an upper bound for the low-label concentration. The global trichotomy does not yet contradict finite twins.
