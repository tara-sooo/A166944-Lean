# Negative MIN: quantitative support, compressed CRT relays, and multiscan diversity costs

Continuation of the deadline/record-energy checkpoint 7d48b3955c5b10f8ef4226bd0c75e5160ca266c4 and forward-medium elimination c4204661641459617950d0db4ac4b5fe2d7306ed. The MIN rule and physical cap have not changed. This note gives a new uniform upper-bound reduction, NOT the missing growing-scale lifetime lower bound. The finite-support theorem is kernel checked; the asymptotic counting and multiscan transfer are paper-level proofs, not yet independently reviewed or formalized.

## 1. Explicit support limit (clock-free)

Consider any finite downward relaxed word of m events, on even integer states, with at most k distinct odd integer labels p>=3. An event with label p may occur at x=+/-1 mod p and changes x to x-p+1. For any positive even Q divisible by all used labels, the word cannot cross a multiple of Q downwards: a source at or above the multiple and less than p-1 above it cannot be eligible (the closest positive even representative of +/-1 mod p is p-1). Consequently the gain of such a word is <Q. The same argument on a reflected word handles upward moves.

Define F(0)=0 and

    F(k) = [2+2(F(k-1)+2)^k]^k-1.

Then m<=F(k). Induct on k (pad the label set if necessary). Two consecutive uses of a label enclose a word with <=k-1 labels, hence have event-index distance <=B=F(k-1)+1. At each pre-event state and the final state, record for each label one of: never used; expired (last use more than B event positions ago); active, consisting of its last source sign and the k counts of labels in the interval from its last use, inclusive, to the current state, exclusive. There are at most 2+2(B+1)^k possibilities per label. If signatures at indices i<j agree, every label used between them must already have been used before i, because the never-used flag cannot reappear. The consecutive-use bound implies it is not expired at i, and equality implies active at j. Identical counts and source sign determine identical residues of the current state modulo that label. Thus the positive even gain Delta=x_i-x_j is divisible by every intervening label. The wall with Q=Delta gives gain <Delta, contradiction. All m+1 signatures are different, proving the formula.

The bound is very coarse, not an estimate of the true maximal word length. From log(F(k)+2)<=k^2 log(F(k-1)+2)+O(k) one gets log(F(k)+2)<=C(k!)^2. Stirling implies k >= (1/2-o(1)) log log m / log log log m as m tends to infinity. This improves the nonquantitative finite-support compactness argument f239d2e1b38bd0697abbf3aff391f9b965745a8a. The actual negative clock rule, including idle ticks, is specialized in NegativeMINCore.lean: no_used_residue_return, supportSignature_no_return, finite_support_event_bound. Verified core 2579e12e2b728e6cdd020cbfcac824b86b4e7871, CI 46033272249. See final verification addendum for subsequent core work.

## 2. A first-use CRT compression that avoids enumerating words

Use L=log R and synchronized T=floor(ceil(sqrt(2R+1)) exp(-L^delta0)); M=floor L^beta, N~R/6. Each actual selected prefix has gain <=3T+6, total completed waits <=3 gain (including pre-observation). For each site and firing clock the physical cap implies at most O(M) contributing roots, since only O(1) windows can visit the site. For time rather than event mass use the earlier phase argument: at most M live tokens per tick, so at most O(Mp) integrated token-time at a source phase of label p. At fixed x,p, there are O(T/p) possible firing clocks (for actual p<=3T+7). Equivalently enumerate O(T/p) possible source postheights. Multiply by O(Mp) and divide by NT. For a charged completed medium event its charge <=2p, so the same counting normalization applies.

Let 0<gamma0<gamma1<1 be fixed, Y0=ceil exp(L^gamma0), Y1=ceil exp(L^gamma1), U=ceil L^3. Fix a positive integer h (the number of distinct successor high labels sought). Let z=D=max(3,floor(log log L/(16 log log log L))) for sufficiently large R, Qz=2 product of odd primes <=z, and B=F(z+D+h+2). Then log B=O((z+D+h+2)!^2) <= (log L)^(1/4+o(1)); B=L^o(1), Qz=L^o(1). Rounding choices are immaterial asymptotically.

Fix a first source x with label p and sign e, the postheight a after firing (postcenter x-p+1, clock a-(x-p+1)/2), and x mod 2Qz. The intermediate events use only the base labels <=z and at most D+h distinct nonbase primes q<U Y1. They may repeat. In the medium scan the source label p itself may occur among them; include it in the support but do not count it twice as a CRT modulus. Fix the distinct label set and prescribe its intermediate prefix length <=B (by section 1).

For each nonbase label q other than the already pinned p, prescribe the sign at its first use, the vector of counts of all nonbase labels before that use (each <=B), and the sum E of all base jumps before that use (<= (B+1)Qz, by the base wall applied to each consecutive base-only run). These determine the gain G from the postsource to that first use. Thus

    x = p-1 + G + sign(q) (mod q).

The complete data fixes at most one residue class mod p*m with m=2Qz times the product of distinct nonbase primes other than p. The CRT statement is a spatial pin, not an assumption that the prescribed counts are realizable. On that class, the deterministic calendar using just the base and prescribed intermediate labels has the same prefix as the full MIN rule whenever the actual intermediate prefix exists: deleting labels not used in the prefix cannot change any chosen earliest firing and its tie-break. A translation by p*m changes the clock by -p*m/2, preserving every restricted clock congruence. Therefore all intermediate positions relative to x, waits, and the height at the final intermediate state are determined on the class. Prescribing the prefix length is necessary; an external target may interrupt the restricted rule before it terminates.

After summing over base residues (cancels 2Qz), possible nonbase primes with reciprocal CRT weights, signs, count vectors and small gains, the multiplicative enumeration factor is bounded by

    A <= (D+h+2)(B+1)
      [ 2(B+1)^(D+h+2) ((B+1)Qz+1)
        (1+sum_{z<q<UY1, q prime} 1/q) ]^(D+h+1).

Here harmless fixed factors cover choosing whether p is included, and including its counts even if already pinned. By the elementary prime harmonic estimate, log A=o(log L), so A=L^o(1). The unweighted number of choices apart from source p, source height and base residue is R^o(1), and m=R^o(1) uniformly. The key distinction from the earlier word enumeration is that powers of B depend on the number of distinct primes, not the full event length B; enumerating all length-B words would not give this estimate.

### Counting rules for a reconstructed prefix

For fixed p, sign, height, intermediate data and base residue, consider fixed source positions x-d_j. A rough position means both neighbors have least prime factor at least r^d/2, where r is its firing label and d=3/5. A completed wait w>=r^d implies roughness by w<=2q(x). For a fixed number of distinct shifts x-d_j+-1, standard upper-bound Selberg sieve on the progression x=x0+pm t gives reciprocal logarithmic powers, one per excluded residue (two per rough position). Precisely the bound is O(R/(pm) times the product of reciprocal log-sieve-cutoffs) times L^o(1). The thresholds used below are at least exp(c L^gamma0). Distinct shifts follow from successive selected high source jumps >=Y0-1>2. Omit primes dividing pm, differences of the shifts, and primes <=number of forms. Their singular-factor loss is (log L)^O_h(1): the log absolute discriminant including pm is O_h(L), so split its prime factors at L and use Mertens. For mixed cutoffs, the number of excluded classes is the number of forms still active at each sieve prime; the Euler product gives the product of the corresponding logarithms. The quadratic Selberg majorant proof of section 3c in c420466 generalizes verbatim with bounded dimension: local rho(ell)<=2(h+1), squarefree weights |lambda_m|<=m for ell>dimension, error O(Z^6); truncate the Euler product at Z^c using its O_h(c log Z) expected log-product. Choose Z a sufficiently small fixed power of the largest cutoff, so the error is absorbed even when p=R^(1/2+o(1)), and the logarithms remain comparable to all intended cutoffs. This uses elementary prime estimates and the same Selberg argument as the previous paper-level checkpoint, not a lower sieve.

For a fast new target r at y=x-G-p+1, let b be the height at the reconstructed final intermediate state. At the target wait w, r divides 2(b+w)+1 or 2(b+w)-5 (even/odd firing respectively). For r large this odd integer is positive, nonzero and O(T) on the actual trajectory. For each dyadic band r~V and w<r^d, enumerate O(V^d) possible w and O(L/log V) prime divisors >=V of that integer. Each target is a new prime relative to the already pinned support, including p, so supplies an additional CRT modulus r. The count per class is O(R/(pm V)+1). For V<=R^0.2 absorb the +1 by the progression length. For V>R^0.2 ignore the intermediate congruences and count O(R/(pV)), since p,r<=3T+7 and p!=r, paying the unweighted R^o(1) enumeration cost. After height cancellation and harmonic summation in p, the fast target contribution is smaller than every fixed inverse power of L, because V>=Y0, d<1, A=L^o(1). The large-V case has an actual negative power of R. This proof does not discard fast or repeated intermediate events.

## 3. High-time scan

Set Ystar=floor(Y1/(2(B+1))) so Y0<<Ystar and log Ystar~L^gamma1. On an actual selected prefix, start at a completed source p>=Y1 and scan subsequent completed events up to the first of:

* label >=Ystar;
* first new label r in [Y0,Ystar) with wait <r^d;
* h-th distinct new label in [Y0,Ystar) with wait >=r^d (all previously new labels in this range were slow);
* (D+1)-st distinct label in (z,Y0);
* prefix end.

Cases are tested in the displayed priority. Before the stop, the intermediate support is bounded by section 2, and gain <= B Ystar < p-1 eventually. In the first case the target r cannot equal p (repeat_relay_gain, or the even spatial repeat-gap lemma). In both fast cases the target is new relative to intermediate support and source. A source with total phase wait <p^d has total time contribution O(Y1^(d-1)) by the gain ledger; otherwise the source is rough. For a slow large target the two rough positions give, after source clock cancellation and sum_{p>=Y1} 1/(p log^2 p)=O(1/log^2 Y1), a normalized contribution <=L^(beta-4 gamma1+o(1)). In the h-th distinct slow case use all h first-use rough positions plus source: normalized <=L^(beta-2 gamma1-2 h gamma0+o(1)). The fast case is covered by section 2. Terminal/tail and very large labels are treated as in the previous weighted live estimate: omit p>=Pmax=T exp(-L^alpha), terminal non-twin dwell and last partial phase. For p<Pmax a source whose scan reaches end is the last such source (another source would have triggered the first case); its per-root time is <=2Pmax/T. The original near-max and terminal errors are O(M(1+L^alpha+L^delta0)/L^3) plus super-polylog-small errors. This includes actual observation cutoffs, not only complete trajectories.

In the saturation case, the source's observed time <=2 exp(-L^alpha). Define Jsat by a counter on completed events, reset its seen set on a label >=Ystar, and increment Jsat and reset the set upon the (D+1)-st distinct narrow label (z,Y0). Each source p>=Y1 starts a different large block, so at most one high-source charge per block; the greedy Jsat counts at least one saturation in every block containing such a stop. This justifies charging the remaining high time to 2 exp(-L^alpha) Jsat, without counting individual repeated labels as paid high-time obstructions.

## 4. Medium elimination using many distinct successors

A charged source p in [Y0,Y1) is rough; its expense 2q(x)<=2p. Start with p in the used-high set and scan until the first narrow event z<r<Y0, a label >=UY1, the first new high label with wait <r^d, the h-th distinct new high label with wait >=r^d, or prefix end. Source p and previous new high labels may repeat. Before stop, there are at most h distinct nonbase labels including p, so section 2 gives at most B intervening events. Good stops (fast new or h-th slow new) are counted by the fast-target or the 2(h+1)-form sieve: the normalized sum of good medium charges is <= L^(beta-2(h+1)gamma0+o(1)) plus super-polylog-small error. Here the sum in source p is harmonic over [Y0,Y1). There is no repeated-label CRT double count.

Any bad stop can receive at most B+1 charges: each charge starts at most B+1 event indices before that stop. The narrow stop is the first narrow event of a low block (maximal run of labels <Y0); let Jlow count nonempty-narrow chunks in such blocks, splitting greedily at each (D+1)-st distinct narrow label. More precisely increment Jlow at the first narrow event of each chunk, reset at p>=Y0 or saturation. The number of first-narrow stops <=Jlow. The total tail charge is <=2(B+1)Y1 per root; the big-label charge is O((B+1) G/U) by gain G and big label >=UY1. Writing E*=sum over all N canonical roots divided by N, C_Q=sum medium charges/(NT),

    C_Q <= O((B+1)Y1/T)(1+E* Jlow)
           + O((B+1)/U)
           + L^(beta-2(h+1)gamma0+o(1)) + o(L^-C0)

for every fixed C0 in the last term. Uniform in the actual capped policy.

## 5. Low time and the new sufficient criterion

For each low block, split at the first occurrence of the (D+1)-st distinct narrow label, then reset. A nonempty-narrow chunk including its trigger has support <=z+D+1 and length <=B, gain <=B Y0. An empty-narrow chunk has gain <Qz, including any unfinished low-only tail. The latter count is <=1+#high+Jlow, where #high<=O(T/Y0) by gain. Completed waits <=3 gain. Thus low time is bounded by

    O((B+1)Y0/T) E* Jlow + O(Qz/Y0+Qz/T+Y0/T).

Nonrough medium time is O(Y0^(d-1)) by gain. For a partial phase use the earlier phase/last-source bounds. Terminal twins contribute <=B0 M #twins(I)/N with the same bounded-window constant B0.

Combining sections 3-5 gives the paper-level uniform inequality

    eta_live <= B0 M #twins(I)/N
                 + C E* [ exp(-L^alpha) Jsat
                    + (B+1)(Y0+Y1)/T Jlow ] + o(L^-sigma),

provided beta+sigma+alpha<3, beta+sigma+delta0<3,
4 gamma1>beta+sigma, 2 gamma1+2h gamma0>beta+sigma,
2(h+1)gamma0>beta+sigma, and beta+sigma>2 for the intended target compatible with the twin upper sieve. Take sigma<3 (as in prior target), U=L^3. The inequality itself does not assume finitely many twins. All cost counters are monotone completed-prefix history statistics; the exact history deadline/cap construction applies, not an additive state-cost minimizer with an invalid contact priority.

In particular retain beta=2.1, sigma=.25, alpha=.60, delta0=.50, gamma1=.85. ANY fixed 0<gamma0<.85 is permitted by choosing h large enough. For gamma0=.10, h=12 yields 2(h+1)gamma0=2.6>2.35 and 2gamma1+2h gamma0=4.1>2.35. Former upper cutoff exp(L^.45) is thus replaceable by exp(L^.10) (or any fixed smaller positive exponent). This is not a uniform limit gamma0->0 with R: h is fixed first, and all sieve dimensions and constants depend on h. With budget b_R=L^(-.30), a positive lower bound eta_live>=c L^(-.25) on unbounded slabs would imply >>R/L^2.35 distinct twin centers there. Integer weights can be rounded up after multiplication by a common scale at least T^2 exp(L^alpha); per-root rounding error after division is O(T/scale). The exact deadline selection of the earlier checkpoint optimizes lifetime for these individual budget deadlines and never changes the MIN trajectory.

### Joint trigger strengthens comparison with the earlier broad band

For gamma0<.45, keep the SAME new z and put Yb=exp(L^.45), k=floor(c log L/log log L) with c sufficiently small. The earlier bounded-word high-pair sieve (section 3 of 5a221805964d0d023f1577e066e67ec984d0aa66) at Yb,Y1 applies: its enumeration factor is <=L^(.1+o(1)), since log Qz=o(log log L), and beta+sigma+.1<2(.85+.45). High source time with <=k intermediate broad-narrow events before the next >=Yb label is negligible. Tail is also negligible. Any remaining high source must BOTH encounter >k broad-narrow occurrences before its next >=Yb label AND trigger the new saturation scan. Both properties occur in its same large block (<Ystar), since Yb<Ystar and the large stop is earlier than or equal to any later large source. Each large block can pay at most one such source. Let Jjoint count large blocks (including incomplete prefix blocks) which have >k occurrences z<p<Yb and >D distinct labels z<p<Y0. Replace Jsat by Jjoint in the displayed bound, with another o(L^-sigma) error.

Jjoint <= Kb/(k+1) and <= Jsat, with Kb the old broad-narrow count at the SAME z. Also Jlow<=Kb. Consequently the joint cost per root is at most (1+o(1)) exp(-L^alpha) Kb/(k+1), because (B+1)(Y0+Y1)/T is super-small even after division by exp(-L^alpha)/(k+1). This is a pointwise comparison, not an expected independence model. It cannot be directly compared to the old cost with a different lower cutoff z~sqrt(log L). Repeated-only broad traffic that never encounters enough distinct small primes now pays no leading high-time charge.

## 6. Actual closure attempts and remaining obstruction

The gain-only bound Jsat<=K/(D+1)<=O(T/((D+1)z)) is still too large. Even charging only once per large block gives <=O(T/Ystar+1) blocks, whose exp(-L^alpha) price is too large: T=R^(1/2-o(1)) and Ystar=R^o(1). Jlow<=K<=O(T/z) gives O(BY1/z), not a small error. Raising Y1 to a power of R near sqrt R to reduce the block count would invalidate the R^o(1) modulus and unweighted enumeration bounds when several different successor labels occur. Thus the new sufficient criterion has not yielded the required lifetime lower bound. It is now specifically a joint diversity/survival problem, rather than a bound on every repeated narrow event. One should seek a lower bound for deadline-clipped live mass with these counters, e.g. by controlling frequency of joint triggers relative to useful first-contact/record energy; previous record energy was for an additive objective and cannot be transferred to the history cost without proof. No twin-prime infinitude result, and no new asymptotic lower bound for twins.

## 7. Reproducibility

* Support and first-use relay audit at 496e193a8381b3f3d798bfc95f03931d588f4760, research/lean/negative_min_support_signature_relay_audit.mjs. Exact remote replay: 179 relaxed supports, 1077 signatures, sampled maxima 2,6,18,54 (NOT claimed universal maxima for four labels); 739059 assertions. R=12000,48000,192000, 42003 canonical roots, 28195500 literal gcd ticks and 775263 events; 29347 high relays, 23715 compressed, 208 with >4 narrow occurrences but <=2 distinct labels, 2085 with repeated narrow labels. 70638 intermediate events reconstructed. The finite combined counter here resets at both count and diversity trigger within low blocks; it is not the new large-block counter.
* Multiscan audit at c235240054e53a3574d4b676b62932a469abb9d1, blob 14318b48839b47ad92e59879b795c77f73011b75, research/lean/negative_min_multiscan_diversity_audit.mjs. Executed before write and exact remote readback: 2540873 assertions over the same three slabs, 392638 intermediate event reconstructions across overlapping scans, 1545 medium scans with source label recurring in the intermediate prefix. Fixed finite z=5,Y0=17,Yb=31,Y1=97,Ystar=47,D=2,h=2,k=4,U=4; not asymptotic cutoffs. Checks first-use pins, restricted prefix reconstruction, waits, gain walls, fresh target and separated repeat conditions, distinct rough forms, source-to-stop charge multiplicity, low chunks, large saturation and joint injection. R192000: 1991 high saturation stops, 597 satisfy also the broad count condition with completed next broad-high event; 10611 large saturations, 91256 nonempty low chunks. Good medium charge 1245170 out of 6221520. These are finite combinatorial controls, not evidence of a growing-scale survival lower bound. No full project build, standalone Node, or independent human review.
