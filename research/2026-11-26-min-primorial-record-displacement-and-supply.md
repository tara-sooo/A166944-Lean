# Reset displacement and the square-root semiprime supply obstruction

2026-11-26 JST. Continuation of universal-ray checkpoint a2bbf3af890d720f749aba636af0b0704d26631f. Theorems below are paper deductions, not Lean verified. Finite numerical audit executed separately. Twin infinitude is still open. No external novelty claim.

## 1. A displacement-based next-record certificate

Use the uncut offset MIN of the previous note. After any doubling u->2u with label r=u+1>=7, let X=2r-2, v0=r+2, d0=6. Such a doubling has u divisible by 6 (otherwise the 3 clock blocks it), hence r=1 mod 6 and X=0 mod 3. The next record p>r exists by the finite-prime primorial barrier argument of that note. Write u=X+G for its pre-offset, d=2v-u, and m for the number of events from X through the record, inclusive. In fact the following displacement bound applies at EVERY pre- or post-event state of the reset block.

For an event, w<=2p, and delta d=2w-(p-1)<=3p+1. If p>=5 this is <=4(p-1); if p=3 and w<=5 it is also <=4(p-1). The sole possible exceptional pair is p=3,w=6, with delta d=10. Consecutive 3 labels can only be plus then minus, with second wait exactly 1 (odd clock 5 mod 6 to even clock 0 mod 6); after a minus 3, the offset is 0 mod 3. Thus an exceptional event must be preceded by a label a>=5. It cannot be the first event of the reset block since X=0 mod 3. Pair each exception with its immediate predecessor, with all these pairs disjoint. The pair increases d by <=3a+11, for total gain a+1; (3a+11)/(a+1)<=13/3. All unpaired events have the bound 4 per unit gain. Hence

    d <= 6+(13/3)G.

For a non-twin doubling, previous exact classification gives d>=u-2 sqrt(u-1)-2. It follows that

    10G >= 3X-6 sqrt(X+G-1)-24.

In particular for any fixed epsilon>0 and sufficiently large X, G<=(3/10-epsilon)X excludes non-twin doubling. A non-doubling record p>r has 3p<=u+1, so u>=3r+5 and G>=r+7=X/2+8. Consequently the same G bound is sufficient for the NEXT record to be a twin, with no restriction on m. For example G<=X/4 is sufficient for all sufficiently large resets. This is an alternative to a short-event-count bound; neither asymptotic upper bound has been established.

## 2. Stronger unconditional lower bound on false-record event count

If the next record is non-twin, every pre-offset from X through this record is non-twin (an intermediate twin would already be a record). With Phi(v)=sqrt(2v+1), every event increases Phi by <2, as proved in the previous potential argument, since a composite neighbor has a factor <=sqrt(u+1), bounding w<=2sqrt(u+1), and u<=2v.

For a non-doubling record the post-offset U=u+p-1>=4r+6. For a doubling record U=2u>=2X=4r-4. In both cases

    2m > sqrt(4r-3)-sqrt(2r+5).
    m >= (1-1/sqrt(2)-o(1))*sqrt(r).

This improves the earlier coefficient 1/(4sqrt(2)) to approximately 0.292893. In the non-twin doubling case alone section 1 even gives U>=(26/5-o(1))*r, hence coefficient (sqrt(26/5)-sqrt(2))/2. A bound m<=sqrt(r)/4 for every sufficiently large reached reset would suffice for twin infinitude by repeated resets. The existence of a sufficiently large starting reset is understood here: a uniform inequality valid only beyond an unknown threshold does not by itself show that the distinguished ray reaches a doubling above it. Equivalently, a version valid for all resets above a concrete already reached threshold can be iterated. Under finite twins, any last reached reset may be smaller than an unspecified asymptotic threshold, so this quantifier condition must not be dropped. Another way to close the argument would be to show doubling resets are unbounded and the non-twin ones are excluded above a threshold. Neither closure is established.

## 3. Critical-scale false records require many large semiprime labels

Fix C>0 and suppose a false next record occurs after m<=C sqrt(r) events from a reset. Put T=sqrt(r), A=(2+2C)^2. The preceding potential estimate yields 2v_end+1<=A r for r>=7, so all pre- and post-offsets lie in [X,A r]. Total physical gain is <=A r, and total wait is >=(r-5)/2 from the nonnegative final deficit and final gain p-1>=r+1.

Let epsilon=1/(16 max(C,1)), a=epsilon/2, B=2 sqrt(A+1). Short waits w<epsilon T have total at most r/16. For sufficiently large r, long waits w>=epsilon T therefore have total at least r/3. Every wait is <=B T, so there are at least T/(3B) long-wait events. Every odd prime factor q of either neighbor of such a pre-offset satisfies q>=w/2>=a T; otherwise its eligible clock would have fired earlier. All pre-offsets are non-twin. At least one neighbor is composite, and for large r each composite neighbor consists of exactly two primes (with multiplicity): a product of three factors >=a T would exceed A r+1. The prime factors of any composite neighbor thus lie in [a T,(A+1)T/a].

Choose H=24AB. Long-wait events with selected p>H T number at most 2A T/H=T/(12B), by the total gain bound. There are therefore at least T/(4B) long-wait events with aT<=p<=HT. Since p is much smaller than u±1, it divides a composite neighbor, and its complementary factor k is prime with k=O_C(T). Both k and pk±2 are free of all primes <=z for z<aT (choose sign according to the neighbor). Pre-offsets are strictly increasing.

Uniform two-form upper-bound sieve lemma: for fixed C, fixed p in [aT,HT] prime, and either sign, the number of integers k in [1,K T] with both k and pk±2 free of primes <=T^(1/10) is O_C(T/log^2 T). Here K can be any fixed constant, and T sufficiently large. Only odd sieve primes are needed. Proof follows, including the upper-bound sieve construction.

Set D=floor(T^(1/10)); for each odd prime ell<=D the two forbidden roots of k(pk±2) modulo ell are distinct since ell!=p and ell!=2. For squarefree d composed of these primes the number of k in an interval of length N<=KT occupying all forbidden residues modulo d equals N g(d)+O(2^omega(d)), where g(d)=product_{ell|d} 2/ell. For real weights lambda_d supported on such d<=D with lambda_1=1, the count is at most

    sum_{k<=KT} (sum_{d|k(pk±2)} lambda_d)^2
    = N Q + O(sum_{d,e<=D} |lambda_d lambda_e| 2^omega(lcm(d,e))),
    Q=sum_{d,e<=D} lambda_d lambda_e g(lcm(d,e)).

Let h(l)=product_{ell|l} (1-g(ell))/g(ell) and W=sum_{l<=D} 1/h(l), over the allowed squarefree indices. Multiplicativity and 1/g(gcd(d,e))=sum_{l|gcd(d,e)}h(l) diagonalize Q as sum_l h(l)y_l^2 with y_l=sum_{d:l|d} lambda_d g(d). Invert on the divisor-closed support. Choosing y_l=mu(l)/(h(l) W) gives lambda_1=sum_l mu(l)y_l=1 and Q=1/W. Inversion also gives |lambda_d|<=product_{ell|d}(1-g(ell))^(-1)<=d, since the residual sum of 1/h(j) for j<=D/d coprime to d is at most W. The error is thus O(D^6)=O(T^(3/5)).

For completeness W>>log^2 D: 1/h(l)>=2^omega(l)/l. Consider the Euler product F=product_{3<=ell<=z}(1+2/ell), with z=D^eta, eta a sufficiently small positive absolute constant. It is >>log^2 z because the ratio to product(1-1/ell)^(-2) is a convergent positive product, and the ordinary reciprocal prime product is at least half the harmonic sum up to z. With weights 2^omega(l)/l for squarefree divisors of the product of those primes, the normalized mean log l is sum 2 log ell/(ell+2)=O(log z) by the elementary Chebyshev prime bound and partial summation. Choose eta so this is <=(log D)/2; by Markov at least half the weight lies at l<=D. Hence W>=F/2>>log^2 D. All constants are uniform in p (which exceeds D). This proves the lemma without assuming any distribution of twin primes.

For a fixed selected p, the long-wait event count in the restricted set is at most O_C(T/log^2 T) by the lemma, summed over signs. Since at least T/(4B) events occur, the number of distinct such selected labels is Omega_C(log^2 T). The same argument for a chosen factor q of a composite neighbor, without restricting the selected p, proves Omega_C(log^2 T) distinct composite-side prime factors as well. This is a necessary condition for the hypothetical false record with m<=C T, not a universal upper bound on m. In particular sparse square-root-scale labels cannot realize that scenario. It connects the offset problem with the source-support sieves in the original direct-arithmetic lane without importing any of their extra hypotheses.

## 4. Executed independent reset audit

Source research/min_primorial_record_supply_audit.py at 5f3bd96dd6cc94524cf14fe8fe10dfe89c0bf6dc; remote blob acfbd8ca2509e27dc24c976d24ac6c9a41517e43 equals the locally executed blob (git hash-object). Python 3/SymPy. Run:

    python research/min_primorial_record_supply_audit.py 1000000 1000000000000000000

All 8,168 twin pairs (r-2,r) with 7<=r<=10^6 were used as separate starting resets (X,v)=(2r-2,r+2). This is not a claim of distinguished-ray reachability for these seeds. The cap is 100000 events per seed; zero incomplete, zero false next records. The largest m was 251 at r=822973, with G=9078, next p=1655023. Largest G/X among seeds:
- r>=7: 324/696 (r=349), about 46.55%.
- r>=1000: 726/7704 (r=3853), about 9.42%.
- r>=10000: 1770/23400 (r=11701), about 7.56%.
- r>=100000: 3576/204396 (r=102199), about 1.75%.

The distinguished ray to cap 10^18 repeats 5326 events and 58 records. For the 56 complete reset-to-next-record blocks (starting with r>=7), all next records are twins. Maximum m=533 from r=3029912737198903, G=35479428. Among ray blocks starting r>=1000, maximum G/X=102/5316 at r=2659, about 1.92%. Last complete block r=387828833711245471, m=203, G=5590572, max d=11046732, next p=775657667428081513. Every pre-record state in the audited seed and ray blocks passed 3(d-6)<=13G; all intermediate steps passed the exact squared-potential check and the exceptional 3-clock predecessor check. The false-record-specific checks were not triggered (no false records observed). The finite experiments do not verify the asymptotic supply lemma or prove that new records are always twin-derived.

## 5. Remaining mathematical problem

The new target is to bound displacement G before the next record by, e.g., X/4, or derive the short-event upper bound m<=sqrt(r)/4 from the actual ancestry. Critical-scale false records would require extensive support of square-root semiprime labels, so merely bounding support is useful only together with an upper bound on m or a further argument excluding long blocks. Neither counting ambient primes nor finite favorable reset experiments supply these missing upper bounds. The seed scan tests a larger family than the distinguished ray but is conditional on the already known twin seeds and cannot imply unbounded resets.
