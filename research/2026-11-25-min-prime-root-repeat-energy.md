# Prime-root repeat/energy hybrid: unrestricted light-donor deletion and small-label moment
2026-11-25 JST. Branch based on 6d2f6bf9c38730703d431f574aecdf232bfed429 (prime-root energy). Combines the source-label moments of Issue #4 (adapted to MIN, NOT transferred from the different squarefree-GCD paths), full-horizon weighted clock of 73458de8, prime-root density of 6d2f6bf9, and CRT/return arithmetic of 640482a6, 1bd657be and 7b90eee8. New paper deduction, exact finite audit; not Lean-checked. No assertion of a solution or external novelty. The two remaining estimates below are OPEN.

## 1. Setup and exact finite contradiction
Let X be dyadic, B=ceil(sqrt(7X)), and P_X the primes M in [X,2X), N=|P_X|. Each source runs exactly the canonical MIN, initial (M+2,2M-2), through its own K(M)=floor((7M-1)/4). Choose the earliest parity clock, ties by least prime; C increases by p-1. All pre-event C lie in [2X,7X) for prime roots in sufficiently large dyadic windows. r(C) is the minimum odd prime <=B dividing (C-1)(C+1), or 0. Every actual event has wait <=2r(C), r(C)<=p, and each source visits a pre-horizon at most once. Put R=sum over original source events r(C), S0=sum over even C in [2X,7X) r(C), H=sum_M(K(M)-M-2).
The parent paper gives R=O(XN), S0=O(XB/log^2 B), N~X/log X, H~(9/8)XN. If no source terminates at twins, H<=2R+2BN. This means it suffices to bound R=o(XN) on unbounded dyadic windows. No claim about full A166944 records is needed.

## 2. New unconditional full-horizon deletion for arbitrary light-background returns
Consider two consecutive selections of the SAME p>=Q (consecutive among p-hits, not necessarily adjacent events). Let q!=p be any intervening selected label whose gain accounts for all but J of the intervening p-free gain, with J>=0. All events before and after q inside this return interval are allowed; write their respective total gains e1,e2 (nonnegative even integers), e1+e2<=J. Denote the signs at the first p, q, last p by sigma0,tau,sigma in {-1,1}. Let C be the pre-horizon of the LAST p.

The exact recharge identity gives
    q = k p + c, c=2-e1-e2+sigma0-sigma, -J<=c<=4,
where k is odd, positive if Q>2J+8. In fact the endpoint difference (p-1)+(q-1)+e1+e2+sigma-sigma0 is a positive even multiple of p for p>=5; q>=p-J. Since q,p are distinct primes, c cannot be zero for Q>2J+8. The final and donor divisibilities give
    p | C+sigma,
    q | C+1-e2+tau.
The second follows because the pre-q horizon is C-(q-1)-e2. Both are necessary regardless of clocks, other labels, source mergers or cutoff. Define A(X,Q,J) as the union of all EVEN C in [2X,7X) satisfying these two congruences for some p,q in the pool, p>=Q, p!=q, some even c in [-J,4] with q=c mod p, even e2 in [0,J], and signs sigma,tau. This relaxed set even permits infeasible histories; it includes every actual light-background return endpoint. Let S_A=sum_{C in A} r(C).

Claim (paper): with Q=B/log B up to rounding and J=floor(log^(1/4) B),
    S_A = O(X (log log B)^2 / sqrt(log B)) = o(X).
Proof: split p into dyadic bands U<=p<2U, U>=Q. For sufficiently large B, c!=0, q>=p/2 for every tuple in the relaxed set: if q=c mod p, q prime odd, c even with |c|<p/2, then k>=1 (k=0 would make q even); q>=p-J. There are O(B/U) choices of k, O(J+1) choices of c, O(J+1) choices of e2, four signs. For fixed c,k the two prime forms p and kp+c have nonzero determinant c. Use the uniform two-form upper-bound sieve proved in section 2 of 1bd657be (coefficients polylogarithmic, p,q>=U/2), giving O(U(log log B)^2/log^2 B) possible prime pairs per c,k. Briefly, ignore primes below a sufficiently large fixed power of log B to avoid every coefficient/determinant divisor; each remaining odd sieve prime excludes exactly two residues, with remainder O(2^omega(d)) on squarefree d. Ford's upper-bound sieve and Mertens give the stated uniform bound; truncation at U^(1/4) gives negligible O(U^(1/4) log U) remainder. No model independence is needed.
For each pair and signs and e2, CRT determines one C residue mod pq and gives O(X/U^2) possible horizons, since pq<=B^2=Theta(X). At those horizons r(C)<=p<2U, even if the visiting source does NOT follow the motif. Consequently the sum of r over the union is at most
    O((J+1)^2 * XB/U * (log log B)^2/log^2 B)
per band. Sum geometrically in U^-1 from Q to B to obtain
    S_A << X (J+1)^2 (B/Q) (log log B)^2/log^2 B.
The specified parameters give the claim. More generally Q=B/log^alpha B, J=O(log^beta B), alpha>0, beta>=0, alpha+2beta<2 works with this bound. Even without the two-form sieve, counting p alone gives S_A << X(J+1)^2 (B/Q)/log B (alpha+2beta<1).

Every original source visits any pre-C at most once, so the actual clock-budget contribution of ALL events at these horizons, not merely marked motif endpoints, is at most N S_A=o(XN). This requires neither prefix origin-span restrictions nor an estimate of physical-state ancestry. Compared with 7b90eee8's full-horizon fixed-LOW p,q,p deletion, it allows arbitrary background donor labels of polylogarithmic total gain, counts only the final return horizon, weights each horizon by r<=p rather than B, and reaches the wider p>=B/log B region. Compared with 1bd657be's light-background prefix estimate, it removes the prefix restriction by directly bounding the weighted horizon support. It is a clock-budget deletion, NOT an assertion that the corresponding quadratic pair energy is small.

## 3. New joint small-label moment and large-label energy criterion
Let k=max(1,floor(sqrt(log B))). Mark the first k selections of each p in each original source, using the entire original run. Their total r cost is <= N k sum_{p<=B}p=O(XN/sqrt(log B))=o(XN). Remove those events and all events at A. Both deletions are accounting only; do not rerun the dynamics. Remaining selected labels are necessarily repeated at least k+1 times in their original source. Split them into p<Q and p>=Q.

Let n_s(M,p) count retained small-label occurrences, and Z_s=sum_{M,p<Q} n_s(M,p)^2. Let W_h(C) count retained HIGH original tags at pre-C. Exact partition of clock cost: R=R_base+R_A+R_s+R_h, with R_A counting only not already removed by the base. Since r<=p,
    R_s <= sum_{M,p<Q} p n_s(M,p)
        <= sqrt(N * (sum_{p<Q}p^2) * Z_s).
The ordinary prime-count bound gives sum_{p<Q}p^2=O(Q^3/log Q). For Q=ceil(B/log B), the OPEN bound
    Z_s = O(N B log^3 B)
is sufficient for R_s=O(XN/sqrt(log B)). This allows logarithmically larger small-label moments than the full all-label O(NB) target; it is not assumed for the distinct full-GCD dynamics of Issue #4. More generally it is enough that Z_s=o(N X^2 log Q/Q^3). A tail bound on small-label multiplicities from deleted-p shadow would be one way to establish it.

For retained high labels define E_h=sum_C r(C) W_h(C)^2. By Cauchy R_h^2<=S0 E_h. As in the prime-root parent, trim near-origin gains <=T=floor(B log^(2-epsilon) B), fixed 0<epsilon<2, defining W_h,late and E_h,late. At fixed C at most O(T/log T) prime origins can be near, and (a+b)^2-b^2<=2a(a+b); hence E_h-E_h,late=O(T/log T * R_h)=o(X^2 B). This holds for arbitrary retained tags, no uniform CRT distribution or independence of histories.
Thus a sufficient **joint OPEN condition**, on the SAME unbounded sequence of dyadic X, is
    Z_s=O(N B log^3 B) AND E_h,late=o(X^2 B).
It implies R=o(XN), contradicting H<=2R+2BN. Every successful terminal grows unboundedly with X. An exact finite (sufficient, not necessary) certificate WITHOUT the asymptotic deletions is
    2 [R_base+R_A+sqrt(N (sum_{p<Q}p^2) Z_s)+sqrt(S0 E_h)]+2BN < H.
The large-label remainder has at least k earlier hits per retained source and cannot have a light-background final return; it includes arbitrary long histories and mixed donor patterns. The CRT set may delete extra events of other sources, but never changes the remaining original clocks. Low-label physical mergers may still create high-label suffix mass: the new high energy must count original tags, not representative physical states.

## 4. Exact finite audit and results
Standalone ECMAScript research/min_prime_root_repeat_energy_audit.mjs; remote source exact readback at 2b9d0c76705bc70e6f71afdadb125151a8ab4efb, blob eff8b78745fca39b1935c662dca753fc81355a47. Reproduce:
    node research/min_prime_root_repeat_energy_audit.mjs 256 1024 4096 16384 65536 262144
Executed the audit function in the available ECMAScript runtime, not a separate Node executable. SPF-based exact clock, full prime-source ensemble, each original cutoff, independent literal parity-GCD comparison for X256/1024 (1724 checks per mode), relaxed CRT horizon enumeration via modular inverses, exact disjoint budget and BigInt Cauchy inequalities. At finite X the analytic J rounds to 1; an extra diagnostic Q=max(5,floor(B/8)), J=12 deliberately tests actual light returns. T=B in the reported late energy to exercise a nonzero remainder; the larger asymptotic radius is not tested here.

| X | N | R | base | A after base | small | high | Z_s | E_h | E_h,late(T=B) | S_A |
|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
|256|43|2948|1810|170|772|196|974|584|516|199|
|1024|137|8760|7658|59|1043|0|1289|0|0|392|
|4096|464|77584|64970|107|12507|0|23835|0|0|1220|
|16384|1612|435124|364745|751|69293|335|178291|1675|1675|3531|
|65536|5709|2679611|2361111|1264|316572|664|922608|3204|3204|9201|
|262144|20390|16687054|15118832|2452|1565770|0|5285404|0|0|25453|

Actual full R and E reproduce the prime-root parent exactly on all six windows. All inequalities/assertions pass. Asymptotic parameter mode observed no actual light return, so separate diagnostic runs X256/1024/4096/16384/65536 check 61/14/21/1/0 actual light returns respectively, every one covered by the enumerated CRT horizon set (all original tags). Diagnostic high cost at X65536 is 931 and E_h=4005, E_h,late=3204. The full squarefree paths are NOT evaluated by this auditor. The high remainder vanishes at some finite windows, but neither the high-energy asymptotic bound nor the small-label moment bound follows from this. Most observed R was covered by the first k uses; the theoretical baseline bound need not be sharp at these finite scales.

## 5. Next steps
The new unconditional step removes the CRT-sparse light background class in the FULL prime-source horizon range, not only the first 2P events. The first k uses can be discarded without assuming their distribution. Need a genuine source-weighted estimate for the small-label tail, e.g. by the exact MIN leave-p-out shadow on original prime tags, and a bound on high late energy after the deletion. The latter might exploit the existing multi-donor return matrices/coupled blocks, but ghost probabilities cannot be transferred to the actual short prime-source interval without an arithmetic argument. Avoid treating the two OPEN estimates as proved or conflating the MIN and full clipped-GCD label counts. No main or Lean change.
