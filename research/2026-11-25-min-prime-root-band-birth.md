# Frozen natural band chains: recurrent asynchronous births and four-form predecessor support

2026-11-25 JST. Continuation of fdec6e92519c8cb7d36cc3a7d918f66867c6b18c. This note changes the chain reference lists to the ORIGINAL natural relative-expensive high hits, so that later source-specific accounting deletion cannot create artificial births. Three unconditional young-chain exclusions and a four-form arithmetic support bound for close distinct predecessors follow. This is a reduction of the high residual, not a proof of the medium moment, the remaining birth/young energy, or the old-chain energy. No Lean compilation or external novelty assertion.

## 1. Natural frozen lists and retained energy

Use X dyadic, B=ceil(sqrt(7X)), u=log B, l=log u, T=floor(X/u^(1/4)), N=Theta(X/u), prime roots M in [X,2X), and the canonical MIN prefixes stopped at first postgain>=T or original terminal/cutoff. Each gain G_M<T+B. For every root freeze the list I of ALL its actual selections with
    p>=Q=ceil(B/u), r(C)>p/sqrt(log p).
Here p is the selected prime and r the least eligible odd prime at the pre-horizon C. This test depends only on the actual state and its selection, not on the root or later accounting marks. All I clocks satisfy r>=B/u^(3/2) and r<=B. Split each frozen list by dyadic clock band [2^b,2^(b+1)). There are O(1+l) possible bands.

Let J be ANY subset of I, including the final retained high set after the previous root, donor, rank, source-cell and history deletions. At each shared high hit of two roots their band agrees because r depends only on C. In the FROZEN I band lists a shared hit is a birth if either immediate band predecessor is absent or the two predecessors differ; otherwise it extends the chain from their common immediate predecessor. Define the age of a shared hit in its unique maximal chain by age 1 at birth, incrementing at each continuation. A chain lies in a single band; all its clocks are within a factor 2. Neither time equality nor identical MIN event lists are required.

For k=max(1,floor(u^(1/8))), partition the actual ordered off-diagonal energy on J into young hits of age<=k and old hits of age>k, always using the age on I. Then
    E_J=R_J+E_young(J|I;k)+E_old(J|I;k).
The young energy of ANY chosen set of frozen births is at most 2k times their total ordered birth weight (even if their births are not retained in J), and at most 2kB times their number as unordered birth pairs. In particular arbitrary later holes in J cause no artificial birth. This is intentionally a different, valid reference choice from the final-J band chains in fdec6e9. Neither old energy is automatically smaller than the other.

## 2. Candidate root pairs and initial births

Any pair of distinct roots sharing a pre-horizon C in I must have |M-M'|<T/2: both satisfy C-T<2M-2<=C. The uniform prime interval upper bound and log T~u give a bound
    P_* = O(N T/u)
on the total possible unordered root pairs with any shared I hit. This counts all candidate pairs, not only observed contacts. No extra multiplicity for the number of different horizons is needed in this count.

Write F=T² B u for the improved target from f8d81fc. Notice
    B P_*/F = O(N/(T u²)) = O(u^(-11/4)).
Choose L=floor(u^(9/4)). For each root pair order its I band births chronologically by horizon, across all bands; at a shared C the band is unique. The first L births of each pair generate at most
    2kB L P_* = O(F/u^(3/8)) = o(F)
young energy on J. This includes all births of pairs with at most L births, and the initial L of pairs with more births, even when each birth belongs to a very large ancestor group. It does NOT dispose of the old hits (age>k) of these chains. In particular one must not replace this by a bound on the entire energy of the pair.

A birth with an absent predecessor on either side occurs at most twice per pair per band (each root has only one first hit in that band). Hence ALL such births, regardless of their chronological rank, generate at most O(k B (1+l) P_*)=o(F) young energy.

## 3. Physical synchronization excludes recurrent post-meeting births

Two roots physically synchronize at a common vertex (t,C) of their ORIGINAL full MIN lists, including terminal vertices. From that point the actual successors are deterministic functions of the common state until one path stops at its own cutoff or gain crossing. If one stops there is no future shared vertex with it. Thus all subsequent natural high selections that exist in both prefixes coincide, including their band. The first shared natural hit after synchronization in a given band can be a birth; every later shared hit in that band has the same previous band hit on both paths. A birth AT a physically common vertex is included here. Each pair has at most one such birth per band. ALL post-synchronization births therefore generate O(k B (1+l) P_*)=o(F) young energy. This is why natural rather than source-specifically thinned lists are frozen in section 1. The result would not hold for arbitrary recomputed J band predecessors.

For a new birth in a band that already had a shared hit, at least one of the two paths has an unmatched band hit between the immediately preceding shared hit and the new birth. Otherwise the two immediately preceding band hits would coincide. More quantitatively, let i_a,i_b be the two indices of the preceding common hit in their respective frozen band lists, and i'_a,i'_b the indices at the new birth. Then (i'_a-i_a-1)+(i'_b-i_b-1)>=1, and every intervening hit counted this way is unshared in that band (there is no common horizon between consecutive shared hits). These intervening gaps are disjoint for a fixed pair within a band, and bands are disjoint incidence sets. Thus a pair with n births has at least n-O(1+l) unmatched natural high incidences across both paths. If n>L before synchronization, these unmatched incidences before synchronization have total selected gain >=(Q-1)(L-O(1+l)) across the two paths. This is a necessary condition, not a sufficient bound on their birth count.

After exclusions in sections 2-3, the remaining young energy is associated exclusively with births with two distinct existing predecessors, chronological birth number>L and no prior physical synchronization (different times at birth). In particular each such pair has already experienced many genuine asynchronous discrepancies. The exclusions are energy bounds on J, not linear deletion of every tag in the associated chains.

## 4. Four-form sieve for close distinct preceding horizons

Let H={even C in [2X-2,7X]: B/u^(3/2)<=r(C)<=B}. All natural I pre-horizons belong to H. For sufficiently large X every such C has r>3, hence C=0 mod 6: otherwise one of C±1 is divisible by 3. In particular distinct D,E in H have positive difference h>=6 divisible by 6; the exceptional coinciding-form shift h=2 does NOT occur in the asymptotic theorem. (For finite relaxed thresholds allowing r=3 a three-form bound instead applies; not needed below.)

For 6<=h<=7X, uniformly
    #{D,D+h in H} << X(1+l)^5/u^5.                (1)
Here h is fixed. Proof: fix p=r(D) and the unique sign sigma with p|(D+sigma), and write D=p(2n+1)-sigma. The n interval has O(X/p+1) terms. For each odd sieve prime q>u², q<=z=floor(B^(1/16)), omitting divisors of h(h-2)(h+2), the four forms
    D-1, D+1, D+h-1, D+h+1
exclude exactly FOUR residues of n, because p>z and their constants are distinct mod q. Both endpoints in H ensure absence of these q. The signs contribute at most factor two. We deliberately omit all q<=u² and exceptional primes; the count of omitted exceptional primes >u² is O(u/log u) since h<=7X, so their reciprocal sum is O(1/(u log u)).

For completeness the earlier uniform quadratic sieve proof (32d4185) extends from dimension two to four here as follows. On squarefree d<=z formed from the allowed q, set g(d)=prod_{q|d}(4/q), h_4(d)=prod_{q|d}(q-4)/4. There are g(d)d residue classes modulo d. The quadratic main term diagonalizes as sum_l h_4(l) Y_l² with Y_l=sum_{l|d} lambda_d g(d); the inverse optimal choice is Y_l=mu(l)/(h_4(l)G_4(z)), G_4(z)=sum_{d<=z}1/h_4(d). It has lambda_1=1 and |lambda_d|<=prod_{q|d}(1-4/q)^(-1)<=d (all q>u²>=7 eventually), by the same Möbius inversion. The integer counting remainder summed over d,e<=z is bounded by sum d²e²=O(z^6), since 4^omega(lcm(d,e))<=de. To lower bound G_4, take the complete product over allowed q<=w=z^c with fixed sufficiently small c>0. Its mass prod(1-4/q)^(-1) is >> (log w/log(u²))^4 >> (u/(1+l))^4 by Mertens and the bounded reciprocal sum of excluded exceptional primes. The normalized product distribution has inclusion probability 4/q, expected log d=O(log w)<=.5 log z for small c. Markov retains at least half the mass with d<=z. Hence the number of surviving n is
    O((X/p)((1+l)/u)^4+z^6).
The error z^6<=B^(3/8) is uniformly absorbed by the main bound since X/p>>B and l grows slowly. Summing over p>=B/u^(3/2), p<=B uses sum 1/p=O((1+l)/u) by the elementary prime upper bound and partial summation, proving (1). This sieve is on one quotient variable, not an assumption that r(D),r(E) are independent or that both large primes can be used simultaneously as moduli. It does not claim a local cubic-log bound in short intervals.

For integer A=floor(B sqrt u), the total number of unordered distinct predecessor horizon pairs (D,E) in H with E-D<=A is therefore
    K(A) << X A (1+l)^5/u^5.                     (2)
The same argument works for any 6<=A<=7X. Unlike a product of global and local rough supports, (1) uses the least factor of one endpoint AND the simultaneous four-form restriction. It is a support count, not a count of roots or a statement about the actual transitions.

## 5. Exact predecessor flow product and capped close-birth exclusion

In the frozen natural I, define F(D,C) to count actual original tags with a band hit at C whose immediately preceding hit in THAT band is D. The band is determined by r(C); if F>0 then r(D) is in the same band. All D<C. For fixed D the sets of tags counted over C are disjoint, since every source has at most one next hit in the same band. Thus sum_C F(D,C)<=W_I(D).

For each distinct predecessor pair D<E define the actual overlap of their next-destination flows
    P(D,E)=sum_C F(D,C) F(E,C).
This is exactly the number of unordered birth pairs (counted with their birth horizons) whose distinct immediate predecessors are D,E: the two groups at any C are disjoint, and their cross product gives all such births. In particular
    P(D,E)<=W_I(D) W_I(E).
No multiplication by the number of possible destination horizons is necessary. The same two roots cannot contribute twice to this fixed D,E, because each has a unique next band hit. The formula remains valid for the natural lists even if one or both birth incidences are later deleted. It is an exact count of births, not a bound on the full future energy of all roots in the two predecessor groups.

Choose A=floor(B sqrt u) and cap c=X u^5/A. All births with two distinct predecessors at distance<=A and P(D,E)<=c generate at most
    2kB sum_{close capped pairs} P(D,E)
       <= 2kB c K(A)
       << k B X²(1+l)^5
       = O(F (1+l)^5/u^(3/8))=o(F)              (3)
young energy on arbitrary J. In the last equality F=Theta(X² B sqrt u). This includes polynomial-sized predecessor masses: for example both W_I(D),W_I(E)=O(B^(1/2) u^(9/4)) with appropriate constants satisfy the cap (X=Theta(B²)); larger raw products may pass if the groups mostly have different next destinations. The exact P replaces raw mass products. This exclusion has no limitation on original depth or on the number of events between the predecessors and the birth. It requires close predecessors AND the actual product cap. No general cap on P is proved.

The bound (3) applies even if the other exclusions already cover many of these births. Use a disjoint priority partition: missing predecessor, postphysical, first L births, close capped, remaining. All of the first four classes contribute o(F) young energy, with overlaps harmless. A residual young hit now belongs to a frozen birth at different physical times, after >L chronological births of that pair, with distinct predecessors either separated by >A or having P(D,E)>c. It is NOT asserted that its own current time is different (the young chain may synchronize later). The entire old class is still separate.

## 6. Integration and open criteria

After all preceding linear root and incidence deletions, let J be the final high set as above. All pair classes previously shown to have total energy o(F) may additionally be omitted; this does not affect the validity of the upper bounds for the new young classes. Define E_recurrent(J|I;k) as the remaining young energy after the priority exclusions; define E_old(J|I;k) using frozen natural chains, optionally also removing the earlier whole-pair classes. The diagonal O(NT) is negligible. We obtain
    E_J = E_recurrent + E_old + o(F)
with the indicated pair exclusions, without claiming that the accounting-deleted portions of the original full energy were negligible. The sufficient joint estimates can now be written
    Z_m=O(N B u³),
    E_recurrent(J|I;k)=o(F),
    E_old(J|I;k)=o(F)
on the same unbounded dyadic windows. Equivalently a bound o(F/k) on the remaining frozen birth weight suffices for the young term. The new recurrent condition is substantially narrower than an unconditioned birth moment; its bound and the old-chain bound remain OPEN. No contraction of the old-chain energy is claimed. The original gain-prefix contradiction then follows by the earlier least-factor support and medium/LOW accounting, not by finite data.

## 7. Reproducible audit

Standalone ECMAScript research/min_prime_root_band_birth_audit.mjs, exact remote readback at d303f95de60eaf20505d776ed09a11e77c9c9dff, blob 6670b995c80ffeed145f528b30be56f655c6ddb8. Run:
    node research/min_prime_root_band_birth_audit.mjs 256 1024 4096 16384 65536 262144
Executed the function in the available ECMAScript runtime, not a separate Node process. All 18 final runs (three modes x six X) passed. Literal parity-GCD comparator on X256/1024: short1183, wide1707, analytic1719. Exact full original vertex sweep including terminal, source support and gain budget, synchronization and common suffix check, natural band predecessor equivalence to consecutive common index, at most one postphysical birth per pair per band, unmatched intervening hit count, all young classes and exact energy decomposition. Independently enumerates arithmetic predecessor support for the finite rmin, checks high r>3 implies spacing6, and verifies finite quotient residue counts for nonexceptional q in [5,31]. Independent flow cross-product oracle equals counted close births; raw products and exact overlap products compared. Tests an arbitrary deterministic submask J of natural I (deliberately creates holes; not claimed cheap), preserving frozen ages and verifying E_J from horizon multiplicity squares. Does not apply cumulative previous marks, prove the limiting sieve estimate numerically, or test the asymptotic parameter ranges.

Modes: analytic T=X/u^.25,Q=ceil(B/u), relative r>p/sqrt(log p), k=max(1,floor(u^.125)), L=floor(u^2.25), A=floor(B sqrt u), asymptotic c (finite guard for shift2). Wide T=4B,Q=7,r>p/2,k2,L1,A=floor(B/8) min2,c16 (shift2 cap32 for small finite ranges). Short T=B,Q=max(5,ceil(B/8)), same diagnostic k,L,A,c. The analytic L exceeds every observed birth count at these sizes, so its late class is vacuous. Wide is intentionally a much broader high definition and a tiny first-birth allowance to exercise nonzero recurrent terms.

At X262144, B1355,N20390, wide T5420: 612685 events,633075 vertices, natural I hits224748,R_I14658404,E_I311130640. Unordered pairs sharing a full vertex366974; pairs sharing I hit300402; synchronized full pairs126505. Natural band births1059701, of which425987 at/after physical sync (including missing predecessor), max total births per pair15, max chain length23, unmatched intervening hits113653, 3541950 later common physical suffix checks. Disjoint birth priority counts: missing730664, postphysical94227, firstL80148, close capped8176, close above cap51721, far94765. 7438 observed close predecessor pairs; total raw product481604 vs exact flow product127252, strictly smaller on4465 keys. 1737 close keys with late births pass cap and918 fail; support envelope5618043 finite close candidate pairs (no shift2). Largest wide residue rank checks1174. These finite counts are not estimates of the analytic support upper bound.

| Wide X262144 energy class | Natural I | Arbitrary subset J (frozen ages) |
|--|--:|--:|
| diagonal |14658404|8012222|
| young missing predecessor |236622364|66517898|
| young postphysical (remaining) |8142090|3909632|
| young first L (remaining) |5672112|2399420|
| young close capped (remaining) |544002|244298|
| young close above cap |4283640|1952748|
| young far |9701376|4123566|
| old |31506652|17575896|
| total |311130640|104735680|

J has134016 tags; 364956 chain continuation pair-hits have both current tags retained but not both preceding tags retained, illustrating why recomputing predecessors on J can create artificial births. Wide remaining young on J=6076314 and old=17575896, but these diagnostic fractions are NOT limiting evidence. Short largest: births88399, postphysical41513, late nonmissing asynchronous46, close capped10/far36, max births4, max age4, E_I87599870, E_J24195643. Analytic largest: births191233, max births4 vs L85, zero late class, E_I218152748, E_J68209187, old on J19477514. At largest analytic high-r support all horizons are spaced by multiples of six; all 18 arithmetic and dynamic runs pass. No Lean compilation, main or other branches unchanged.

## 8. Next target

The young obstruction now consists of genuinely recurrent asynchronous overlap, requiring >u^2.25 births per root pair and many unmatched high hits, or a very large cross-product of actual next-band flows. Investigate whether the MIN time offsets bound the number of such pre-synchronization discrepancies; separately estimate the long shared chains (including common physical suffixes) and the medium moment. The first-birth counts do not bound those old chains.
