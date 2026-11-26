# Lag-descent support sieve without an event-count restriction

2026-11-26 JST. Continuation of 47b169424a3e2706914ebf59818b9614690e3e09. Paper results, finite arithmetic certificates and audits; no Lean verification, external novelty claim, or proof of twin infinitude.

## 1. Stronger finite-certificate reset deficit

Use the previous offset MIN, reset (X,v)=(12k,6k+3), d=2v-u, G=u-X. For positive integers a,b define reward b delta d-a delta u=2bw-(a+b)(p-1). As in the previous paper, a run of labels from a finite alphabet is a prefix of its restricted MIN and cannot cross its horizon wall Q=2 product A. The maximum prefix reward F(u,v) on even u in [0,Q] and v mod Q obeys the exact descending-u recurrence

    F=max(0,2bw-(a+b)(p-1)+F(u+p-1,(v+w) mod Q))

if an A-event exists, and F=0 otherwise. The maximum B over all states and I over reset residues (12k mod Q, (6k+3) mod Q) give a global certificate if every large event followed by a restricted run has reward <=0.

First use A={3,5,7,11}, a=11,b=3. The exact values are B=14,I=6. For p>=17 the reward <=14-2p<=-20; for p=13,w<=25 it is <=-18. The only remaining case is p=13,w=26: the source cannot have an A-neighbor factor, as its A-clock would fire within 22 ticks. The maximum F over all time residues at offsets u+12 mod Q with such a rough source u mod Q is 12. Thus the large-event-plus-run reward <=-12+12=0. This proves 3(d-6)-11G<=6.

More strongly use A={3,5,7,11,13}, Q=30030, a=18,b=5. The exact values B=28,I=12 were computed by a rolling-row NumPy implementation and an independently written C++ scalar implementation. The domain has (Q/2+1)Q=450930480 entries (including the known zero wall). The C++ implementation needs only seven rolling rows, since the largest restricted gain in units of 2 is six. For any p>=17, reward <=23-3p<=-28, so all large-event-plus-run blocks have nonpositive reward, without any further phase restriction. The initial run has reward <=12. Therefore for every finite prefix from an arbitrary integer reset,

    5(d-6)-18G<=12,
    d<=42/5+(18/5)G.

This is an unconditional finite-computation-assisted bound, not an estimate obtained from sampled rays. At a false doubling u=X+G, the previous necessary d>=u-2sqrt(u-1)-2 gives

    13G>=5X-10sqrt(X+G-1)-52.

For G<=3X/8 and X>=10000 this would require X/8<=10sqrt(11X/8-1)+52, which is false at 10000 and remains false by the increasing difference (or elementary rationalization). A non-doubling first label p>r=X/2+1 requires G>=X/2+8 as before. Thus for X>=10000, G(r)<=3X/8 suffices for the first label >r to be twin-derived. The asymptotic sufficient fraction is any fixed value below 5/13 (~0.384615), versus 13/35 (~0.371429) previously. No upper bound on G(r) has been obtained.

## 2. Subset lag-floor budget

Write L=u+3-v>=2 and call an event descending if L'<L. Its lag loss is w-(p-1), so w>=p and loss <=p+1. Let B be the set of DISTINCT labels of descending events on any finite segment; let A be ANY subset of B (including the empty subset). Put Q=2 product_{p in A} p, and

    F_Q(L)=Q floor((L-2)/Q).

The earlier dual lag wall at J+2 for 2p|J implies F_Q(L')>=F_Q(L) whenever p in A. Nondescending events of any label also cannot decrease F_Q. For a descending event with p outside A,

    F_Q(L)-F_Q(L') <= L-L'+Q-1 <= p+Q.

Write D=L_start-L_end, and N_p for the count of descending events of label p on this segment. Telescoping and floor rounding give the exact budget

    D-Q+1 <= sum_{p in B minus A} (p+Q) N_p.        (1)

For A=B this gives D<Q; importantly only labels that actually decrease L are needed in the product, not all the labels on the segment. Arbitrarily many nondescending events do not affect the wall argument. Taking a smaller A turns its wall into a budget for the remaining labels.

## 3. All-scale fixed-label descent supply

Consider any envelope-valid segment with u>=X>=6 and u<=A0 X, where A0>1 is a fixed constant. Each descending event at u is necessarily non-twin: at a twin center u>=6 the selected label is u+1, its post-lag is u, and its pre-lag is at most u/2+3<=u. Consequently a composite neighbor has some factor q<=sqrt(u+1). The first-clock property gives w<=2q for EVERY odd prime factor of EITHER neighbor. At a descending event with label p, w>=p, so all those factors are >=p/2 and

    p<=2 sqrt(u+1)<=2 sqrt(A0 X+1).

Fix p and one sign. Since p divides a neighbor, write that neighbor as pk, so the other neighbor is pk+2 or pk-2. Both k and pk+-2 have no prime factor <p/2. The multiplier k is an integer, not assumed prime or semiprime. It lies in an interval contained in [1,N], N=floor((A0 X+1)/p). In the permitted scale p^2<=4(A0 X+1) we have N>=p/4-1.

The uniform two-form Selberg upper-bound sieve from research/2026-11-26-min-primorial-record-displacement-and-supply.md, section 3, applies at D_sieve=floor(p^(1/10)) instead of T^(1/10). For sufficiently large p every odd sieve prime ell<=D_sieve is distinct from p and has two distinct forbidden roots for k(pk+-2). Squarefree d counts are N g(d)+O(2^omega(d)), g(d)=product 2/ell. The same explicitly diagonalized Selberg quadratic form gives main term O(N/log^2 D_sieve), with weights |lambda_d|<=d and error O(D_sieve^6)=O(p^(3/5)). Since N>=p/4-1, the error is absorbed uniformly in O(N/log^2 p). For bounded p enlarge the absolute constant using the trivial count. Summing both signs, and using strictly increasing offsets on one segment, we obtain

    N_p <= C_A0 X/(p log^2 p).                     (2)

Unlike the earlier critical-square-root event supply estimate, (2) requires neither a bound on the event count nor a lower polynomial scale for p. It counts descending events only, which are the ones relevant to lag collapse. It remains valid if the overall segment contains twin events (they cannot descend). It does not claim every sieve candidate is reachable.

Combining (1) and (2) gives, for EVERY subset A of descending support B,

    D-Q+1 <= C_A0 X sum_{p in B minus A} (1+Q/p)/(log p)^2.   (3)

This is a family of necessary constraints on the actual descending support, with one uniform constant. In particular, if Q=o(X), all remaining labels exceed Q and are >=X^epsilon for fixed epsilon>0, and D>=delta X for fixed delta>0, then the remaining distinct labels number Omega_{A0,delta,epsilon}(log^2 X). This extends the previous support obstruction to a gap-separated collection of labels without assuming the block has O(sqrt X) events.

## 4. Mixed-scale support must diverge, quantitatively

Assume D>=delta X, delta>0 fixed, in the segment of section 3, and sort the distinct descending labels p_1<...<p_K. Define Q_j=2 product_{i<=j}p_i, Q_0=2. For large X, Q_K>D>=delta X by (1). Let j_* be the first index with Q_j>=delta X/2; it exists and j_*<=K. For j<j_* the left side of (3) is >=delta X/2. If p_{j+1}>=Q_j, then all i>j have 1+Q_j/p_i<=2, so

    delta/2 <= 2 C_A0 (K-j)/(log p_{j+1})^2,
    log p_{j+1} <= C'_{A0,delta} sqrt(K).

If instead p_{j+1}<Q_j, we have log p_{j+1}<log Q_j directly. Therefore for every j<j_*,

    log Q_{j+1} <= log Q_j+max(log Q_j,C' sqrt(K))
                 <= 2 max(log Q_j,C' sqrt(K)).

Induction gives log Q_j<=2^j max(log 2,C' sqrt(K)) until j_*. Since Q_{j_*}>=delta X/2,

    log X <= O_{A0,delta}(2^K sqrt(K)).

Equivalently (all unmarked logs natural),

    K+(1/2)log_2 K >= log_2 log X-O_{A0,delta}(1),
    K >= log_2 log X-(1/2)log_2(log_2 log X)-O_{A0,delta}(1).

For the second line, if K>=log_2 log X it is immediate; otherwise substitute that upper bound in log_2 K. This proves an unconditional growing-support obstruction to a macroscopic lag decrease on a bounded-ratio horizon interval. In particular uniformly bounded descending support, or K<=(1-epsilon)log_2 log X, cannot cause D>=delta X along unbounded X. The result is about distinct downward labels, not the number of events or of all labels. The product barrier alone would not imply it, since two square-root-scale primes can have product comparable to X. Conversely this logarithmic support requirement does not exclude general large-support paths.

At a false doubling pre-state reached from reset X with u<=A0 X, L_start=X/2 and L_end<=sqrt(A0 X-1)+4. Thus D>=X/3 for all sufficiently large X. The theorem applies with delta=1/3 to the prefix ending BEFORE the false doubling. It does not need an upper bound on its event count. It does not exclude false non-doubling records that do not undergo such a lag collapse.

## 5. Executed diagnostics and reproducibility

C++ independent finite certificate: research/min_primorial_descent_certificate.cpp, commit d6105149c1df3c7615e9c4716aab95bdb60ca653, executed and remote-verified blob edf9da8e54467121f262e33016bbb353176042e2. Build/run:

    g++ -O3 -std=c++17 research/min_primorial_descent_certificate.cpp -o descent_certificate
    ./descent_certificate

Output: a=11 b=3 Q=2310 states=2670360 B=14 I=6; p=13,w=26 rough-source successor bound 12; a=18 b=5 Q=30030 states=450930480 B=28 I=12; all certificate checks passed. The larger certificate uses independent scalar clock minimization and rolling-row recurrence, matching exploratory NumPy results. No Lean proof.

Finite descent budget audit: research/min_primorial_descent_supply_audit.py, commit 06968adabe54ee2d6eb2088521ef4ad7711768bd, executed and remote-verified blob 3370f2d3a095501f6c8b89041b881b8b6f441f68. Run (requires sibling record-supply audit and SymPy):

    python research/min_primorial_descent_supply_audit.py 100000

All 16666 integer resets r=7,13,...,99997, stopping BEFORE the first label >r: 317671 pre-record events, 140738 lag descents, 1270684 subset-budget checks for subsets defined by thresholds 3,7,13,31. All descent roughness, scale, full-product and subset budget checks passed. Largest observed D/X among r>=1000 was 140/5892 (~2.376% at r=2947); among r>=10000 it was 150/20052 (~0.748% at r=10027). Maximum distinct descending support was 17 at r=75535. These finite statistics do not imply a uniform support bound, and the asymptotic sieve and mixed-scale conclusions are paper deductions, not numerical estimates.

## 6. Remaining target

The new sieve applies to lag loss at every label scale and makes the previous primorial phase barrier useful even with arbitrary intervening nondescending events. To exclude a general false doubling one still needs an upper bound on its descending-label support, or a sharper supply argument for large support. To prove twin infinitude via the first-record criterion one must additionally control non-doubling records and/or displacement to the first record (an unbounded sequence of integer resets suffices). Neither the mixed-scale lower bound nor the larger finite deficit certificate supplies that missing unconditional upper bound. The next focus is whether ordered phase ancestry restricts the distribution of descending labels rather than just their support size.