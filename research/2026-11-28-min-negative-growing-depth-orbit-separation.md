# Negative MIN: growing-depth separation of actual rough-source trajectories

2026-11-28 JST; Issue #10. Continue from e51533d712eff0abc4fba442ce90282d2c4551c5. User goal 4.85, including alternate trajectory-distribution route. Checked core c9b2d47f7cf473e3f8768a7c9292d4b2205c536a (614 declarations) unchanged. This is a paper deduction using the previous unconditional rough-source supply, elementary uniform Selberg upper sieve and checked local identities. No new external theorem, Lean compile or independent human review. The earlier .295 sieve proof draft is not used or promoted.

## 1. Main statement

Fix theta>0, rho>0, theta<1/2-rho, and 0<c<1. Write L=log R. Let F be ANY subset of canonical roots A in [R,2R], qmin(A)>=R^theta, not twin centers, for which the actual first firing is plus (even clock), with winner
    R^theta <= p <= R^(1/2-rho).
Set, for all sufficiently large R,
    k=floor(c log L/log log L),
    Z=R^(rho/(4k)), K=floor(Z/L^5).
Then except for o(R/L^2) roots of F, the following hold simultaneously:
- After the first event, at least k further actual events occur; their labels are <=Z, their full waits are <2K, and the k-th further event is completed within 2kK additional ticks.
- Every one of the k+1 centers after the first event, up to and including the k-th further event's destination, has qmin<K. All of these centers are non-twin; the initial source is non-twin by hypothesis.
- After discarding the exceptions, the sets of all visited positions from birth through those k+1 actual events are pairwise disjoint between DISTINCT retained roots. This concerns all positions, irrespective of arrival clocks, and hence implies no physical-state mergers during these (individually terminated) prefixes.

In particular, if |F|>=a R/L^2 for fixed a>0, retain >=aR/(2L^2) roots for large R. Their distinct visited positions are at least (k+2)|F_ret| >> R log L/(L^2 log log L). This is a growing-depth theorem, not a common retirement at the square-root horizon. The length of the initial wait is >=(p-7)/2 and <=(3p-7)/2; all listed events complete by O(R^(1/2-rho)). The additional event interval is at most 2kK=R^o(1); its elapsed time is at least k. No polynomial lower bound for elapsed time AFTER the first firing follows. We prove a further spatial separation statement in section 6.

## 2. Word-weighted CRT compression

The first destination is x0=A-p+1 with p|x0. For the plus first firing the exact canonical birth calendar is
    w0=((v mod 4)p-7)/2, v=(A+1)/p,
and the height h=x/2+n just after it is h0=0 or p. Here p>=11 eventually, and v is odd. Both statements follow directly from the positive clock residue, or from the previous exact calendar in 8aa47ea.

Represent the next j completed events by a signed word
    w=((r1,s1),...,(rj,sj)),  r_i odd prime<=Z, s_i=+1 or -1,
where sign denotes the even/odd firing branch. Let g_i=sum_{l<=i}(r_l-1), g=g_j, y=x0-g. An actual such prefix implies the following spatial congruences:
    y+g=0 mod p,
    y+g-g_i=1-s_i mod r_i (1<=i<=j).
This is the checked incoming pin at the actual postevent center, translated to the final y. For a fixed word and p, inconsistent repeated-prime pins give no solutions; otherwise they fix ONE residue class for y modulo
    M=p prod_{r distinct in word} r.
Do not multiply a repeated label into the modulus again. No order or timing converse to these necessary congruences is claimed. The source is A=y+g+p-1, so A+1=pv where
    v=(y+g+p)/p,   A-1=y+g+p-2.
Both forms are R^theta-rough; v>1 for large R. We do not require the source itself to be a prime or semiprime pair. For all relevant words j<=k, g<=kZ=R^o(1), M<=R^(1/2-rho+rho/4); every relevant position lies in [R/2,2R] for large R.

For any m, write H_Z=sum_{3<=r<=Z prime} 1/r = O(log L). The reciprocal weight of all signed words of length m, with each DISTINCT label paid once, obeys
    sum_words 1/prod_{distinct labels} r <= [2(H_Z+m)]^m.
Proof by sequential extension: each new label adds a factor 1/r (sum <=H_Z), whereas repeating an existing label adds no factor and there are at most m possibilities; each sign adds two options. This also bounds two words of lengths i,j by treating the concatenation as one word of length i+j, using the distinct-prime product over their union. All lengths 0..k and 0..2k contribute at most
    L^(c+o(1)), L^(2c+o(1)),
respectively, including the polynomial-in-k count of choices of lengths. Indeed log(2(H_Z+2k+1))<=log log L+O(1). The initial label p is much larger than kZ, and sum_{R^theta<=p<=R^(1/2-rho)}1/p=O_theta(1) by Mertens. We never bound word count by Z^k; the reciprocal-weight compression is what allows k to grow.

## 3. Exclude rough centers throughout the growing-depth prefixes

Recall the elementary fixed-dimension Selberg upper from e51533d and 8aa47ea: r=2 or 4 affine integer forms with nonzero coefficients and pairwise nonzero determinants of size R^O(1), in an interval of length X>=R^eta (eta fixed positive). To count those all rough to Y, set D=floor(min(X^(1/12),Y/2)). Omit primes dividing the fixed-size product of coefficients/determinants, and primes<=2r+1. CRT error O(D^6) and the diagonal Selberg denominator give
    count << X (log L)^r/(log D)^r + O(X^(.5)).
The omitted-prime loss follows from the R^O(1) bound for that product, and is uniform even as k grows, because the number of forms stays FIXED. The polynomial-size X ensures the second term is negligible compared to X/L^4. If Y=R^theta, log D >> L; if Y=K, log D >>_rho L/k. These estimates hold with uniform constants in the word and initial labels.

For each fixed p and low word of length j<=k, suppose the endpoint y has qmin(y)>=K. In the single CRT class above, the four forms
    (y+g+p)/p, y+g+p-2, y-1, y+1
are all K-rough (K<R^theta). They are integer affine forms in the class parameter, with distinct rational roots: their four undivided shifts are g+p,g+p-2,-1,+1, all distinct since p large. Coefficients and constants, hence all determinants, are uniformly polynomial in R; choose the least nonnegative CRT representative. With X comparable to R/M, the upper is
    O(R/M * k^4 (log L)^4/L^4).
Sum over p, words and lengths, using section 2. The number of roots having such a rough endpoint at any low prefix of length <=k is
    B_rough <= R L^(-4+c+o(1)) = o(R/L^2).            (1)
This includes j=0 (the first destination) and j=k; the proof does not assume the next label is small or the endpoint is a twin. It is a bound on root/prefix records; it also bounds the number of roots.

## 4. Exclude a fast large-label interruption, then bootstrap the actual depth

The previous roughness exclusion only controls a WAIT, not the label that wins it. In particular when h0=p, a large prime can fire quickly. The following new height pin estimate handles that issue, rather than inferring the winner's size from the wait alone.

Suppose j<k low events have occurred, each of their waits <2K, and qmin(y)<K, so the next actual event has wait <2K by the static calendar. Assume its winner r>Z. Write u for total elapsed ticks after the first big event through this next event; 1<=u<=2(j+1)K. The postevent height is
    h'=h0+u-(g+r-1)/2.
The checked height pin implies h'=m r+b, b=0 or3 according to the firing sign, m a nonnegative integer for r>=11, and hence
    r | (2h0+2u-g+1-2b)=(2m+1)r>0.                 (2)
Nonnegative height gives r<=2(h0+u)+1<=3R^(1/2-rho) for large R. Also r != p: at y=x0-g, a repeated p would divide y+1 or y-1, but x0=0 mod p, g even and 0<=g<=kZ<p-1. The only possible congruences g=+/-1 mod p cannot hold in this range. In particular r is distinct from p and all low labels.

For FIXED p and word (and the two h0 options), g is fixed; u ranges over <=2kK integers, and b over two values. Each positive integer in (2) has size O(R) and at most O(log R/log Z)=O_rho(k) prime divisors >Z. Therefore the total reciprocal weight of all possible fast large labels for this word is
    sum_{r candidates}1/r <<_rho k^2 K/Z <= O_rho(k^2 L^-5).
We may also count each r under each of its two signs, a constant factor. The next spatial pin y+s=0 mod r adds a new independent modulus r to M; the enlarged modulus satisfies
    M r <= 3 R^(1-2rho+rho/4).
If the necessary congruences are consistent, one class remains. The two source forms (y+g+p)/p and y+g+p-2 stay R^theta-rough. Their two-form upper, using X comparable to R/(Mr) with polynomial room, is O(R/(Mr) * (log L)^2/L^2). Sum first over r with the reciprocal bound above, then over p and words. The total fast-interruption exceptions obey
    B_fast << R/L^2 * L^(c+o(1)) * L^-5
           = R L^(-7+c+o(1)) = o(R/L^2).             (3)
All elapsed times have been summed by the divisors of (2), not by enumerating the possible wait of every low event. In particular no factor K^k occurs. The count includes only a necessary subset of possible fast labels, not an assumption of their independent probabilities.

Remove the roots in (1),(3). From j=0, qmin<K ensures the next actual event exists within <2K ticks. By (3) it cannot have label >Z, hence extends the actual low word. Induct up to j=k. Thus every retained root truly completes all k additional events by 2kK, and every visited endpoint including j=k has qmin<K. Since the positions are of order R, a neighbor with factor <K is composite. This proves the first two parts of the main theorem. In particular we have bootstrapped existence of the low words rather than conditioning the separation theorem on unproved typical labels.

## 5. Pair energy of all visited positions, not only the final endpoints

Consider two DISTINCT roots A,B, each with a low prefix of length i,j<=k after their first plus event, at a common endpoint y. Let their first labels be p,q and suffix gains g,h. If p=q, both y+g and y+h are multiples of p; |g-h|<=kZ<p forces g=h and hence A=B. This is impossible. Thus p,q distinct and both exceed Z. The two sets of incoming pins together either are inconsistent or prescribe a single CRT class mod
    M=pq prod_{low distinct labels in union} r
      <=R^(1-2rho+rho/2).
All four source forms
    (y+g+p)/p, y+g+p-2, (y+h+q)/q, y+h+q-2
are R^theta-rough. Their four undivided shifts are pairwise distinct: the two roots' source centers differ by A-B, a nonzero multiple of 6, so no neighbor coincidence A±1=B±1. The same-root neighbors also differ by 2. Thus determinants nonzero, coefficient product polynomial in R. Apply four-form upper with X comparable to R/M, log D>>L; the bound for the fixed pair of words and p,q is O(R/M * (log L)^4/L^4).

Sum with the union-word reciprocal weights of section 2. The number of pairs of distinct roots' actual low-prefix records at a common position, across ALL lengths i,j<=k, is
    E_depth <= R L^(-4+2c+o(1)) = o(R/L^2) for c<1.    (4)
There is no requirement of a common sign at the last event, of synchronized ages, or of equal word lengths. (4) is a stronger spatial condition than common-clock coalescence. Also no polynomial lower bound on the time spent in those k events is obtained. Discard both roots of every pair in (4), at most 2E_depth roots. The retained low-prefix position sets are pairwise disjoint. Because every low-prefix position is not K-rough, while every root in F is R^theta-rough, no low-prefix position can equal ANY source position in F. Initial source positions are distinct by definition. Within each path the firing centers strictly decrease, so the number of visited positions per root is k+2 including the birth. This establishes all the claims in section 1.

## 6. Extension to spatial buffers and later motion without prescribing labels

Fix also eta>0 with 2c+eta<2, e.g. c=.75, eta=.4. Let J=floor(L^eta). Strengthen (4) to count records with distance <=4J, using one additional integer offset d between the two positions. For fixed d, if p=q, |g-h-d|<=kZ+4J<p, and the two first destinations (multiples of p) must coincide; equal p then forces A=B, excluded. For p!=q, translate the second word pins by d, yielding the same CRT modulus; translate its two source forms by d as well. Their determinants still nonzero for distinct canonical sources. The same per-d bound applies, so
    E_near <= R L^(-4+2c+eta+o(1)) = o(R/L^2).         (5)
The identical shifted-form argument in section 3 excludes every even K-rough center within distance 4J of any low-word endpoint, at cost
    B_near_rough <= R L^(-4+c+eta+o(1)) = o(R/L^2).
Initial source positions at distance <=4J from one another are also negligible pairs: for each nonzero d multiple of 6, |d|<=4J, sieve A-1,A+1,A+d-1,A+d+1, four distinct forms, at R^theta. Their total is O(R J (log L)^4/L^4)=o(R/L^2). The shifted roughness exclusion prevents near meetings between any low endpoint and any original source. Consequently after removing o(R/L^2) roots, EVERY visited position of each retained prefix is farther than 4J from every visited position of a different retained prefix.

This buffer can be used for subsequent unrestricted events. Let y be the destination of the k-th low event of a retained prefix. Every even site in [y-J,y] has qmin<K, hence no twin and full next-event wait <2K from any clock. Without any restriction on subsequent labels, the actual orbit must cross below y-J within at most 2K(floor(J/2)+1) additional ticks, since every firing decreases position by >=2. Until that crossing, every newly visited site is within J of its own y, so paths of different retained roots cannot merge during these extended prefixes (including any earlier visited positions). The crossing landing positions themselves may coincide or be twin, and are NOT included in the noncollision statement. This yields many disjoint extended actual histories with additional gain >J at the crossing, distinct crossed cuts and time bound O(KJ) after the k-th low event. It is an extension in actual movement and path length; it does not yield disjointness through an arbitrary common fixed deadline.

## 7. Apply the new theorem to two unconditional supplies

A. Use the previous unconditional source-composite population from e51533d section 4: A=pv-1, p,v prime 1 mod420, p in [R^.198,R^.199], pv-2 p-rough, >>R/L^2 distinct roots. First plus firing at (p-7)/2, h0=0, actual first destination p(v-1). For section 1 take theta=.198, rho=.25, any fixed c<1. The entire population meets the initial hypotheses. Removing o(R/L^2) still leaves >>R/L^2 actual paths with k+1 completed firings and pairwise disjoint visited non-twin positions. Total completed age <=(3/2)R^.199+2kK<=2R^.199 for large R (indeed first wait shorter). By section 6 with c=.75, eta=.4, additionally get separated buffers and cut crossing after at most O(KJ) further ticks, still by 2R^.199. This does not depend on finiteness or infinitude of twin primes. Unlike the earlier local crossing result with only the first reset, the actual additional firing depth now grows at an explicit rate.

B. Use the accepted previous .285 shifted-prime supply from 8aa47ea: at least a R/L^2 roots A with A-1 prime, A+1 rough above R^.285. Either at least aR/(4L^2) of them are twins or the rest are non-twin and first event necessarily plus as in e51533d. We must trim the very largest possible first labels to get a fixed polynomial CRT margin. For first label p>=R^(1/2-rho) up to C sqrt R (from p<=4qmin+7), write A+1=pv; v and pv-2 are R^.285-rough. For fixed p, two-form upper in v of interval length O(R/p) gives O(R/(p L^2)) with a constant UNIFORM in rho in (0,.05], since log X>=.49L for large R, cutoff R^.285, determinant 2, only potentially omitted large prime p and 2. No loglog loss is needed here. Mertens on the prime range gives sum 1/p = log((1/2)/(1/2-rho))+o(1)=O(rho)+o(1). Pick fixed sufficiently small rho>0 depending on a and this uniform constant, so the roots lost are <=aR/(4L^2). Thus unless there are >=aR/(4L^2) twins there remain >=aR/(2L^2) admissible roots in section 1 with theta=.285. Apply (1)-(5). In particular under finite twins, EVERY sufficiently large slab has >>R/L^2 actual non-twin histories, each with a first wait >=(R^.285-7)/2, k subsequent events and pairwise spatially separated prefixes through those events. All listed events complete by O(R^(1/2-rho)), with an unspecified fixed small rho. This is a near-square-scale upper deadline for individually stopped prefixes, not a lower bound on time of the first exit or the subsequent motion at the exact sqrt scale. The result remains valid as an unconditional dichotomy without assuming finite twins. No dependence on the earlier .295 draft.

## 8. Verification, limits, and next use

The executed audit research/lean/negative_min_growing_depth_separation_audit.mjs @5892786a15360bca40290b42a3ec262bb8568110 blob 9f17713797f5932cecaa46113ff4dc40aa22c24d, exact pinned readback. Finite proxies R=12000,48000,192000,768000; k=2,3,4,5; Z=11,13,17,19; K=7,11,11,13. Select rough non-twin plus-first roots with p>kZ+1, not the asymptotic cutoffs. 7219 first events (5238 prime-minus sources), 16021 subsequent events compared to independently trial-factored literal tick recurrence, 5756 rough-frontier stops, 350 fast large-label stops (height and spatial pins checked), 3592 repeat-label occurrences; 22890 visited records, 993 exact-position pairs, 2519 shifted pairs at offsets 2,4,6 under strengthened p>kZ+6, 13876 shifted rough records, 126518 pin checks, 138864 determinant checks, 5461 exact reciprocal word-weight controls, all final checks passed. Initial replay implementation disagreed on a simultaneous eligibility tie; replaced literal evaluator by independent trial division and explicit minimum over all eligible labels, then reran. These proxies exercise arithmetic conditions, including failure branches; the survival fraction at these small cutoffs is NOT the asymptotic claim. No finite sampling is used to establish (1)-(5). Both source supplies use the earlier accepted ordinary BV/linear-sieve or BFI theorem (source locators in e51533d/8aa47ea). No new external literature consulted.

The distribution breakthrough is limited to explicit growing event depth k and subpolynomial elapsed time after the first event. It does not yet control collisions at a common near-square-root retirement, where the number of small events could be much larger. The method's word penalty L^(2c+o(1)) consumes the two logarithms of four-form saving: for much larger depth, a different compression is required. The next useful problem is to replace signed-word enumeration by a substantially shorter description of the set of CRT pins and total displacement, or a first-contact-only flow estimate charging only novel labels. Reuse the exact height pin (2) to bound fast exceptional jumps with that compressed history. The .40 low-gain target at T=ceil(8 sqrt(2R+1)) and the .295 analytic proof draft remain unresolved. 4.85 is not claimed. No new Lean kernel check, independent human review, or modifications to main/siblings.
