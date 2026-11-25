# Discovery-only CRT packing and per-prime time capacity

Continuation of [4ab10f6](https://github.com/tara-sooo/A166944-Lean/blob/4ab10f680dcc6b10231ba172ebbbcfeff1ad2ae0/research/2026-11-26-min-direct-short-time-word-packing.md). The former short-time counting proof enumerated every tick symbol and used distinctness of large labels over a short clock interval. Here only first occurrences of previously unknown large primes need to be encoded. Given the initial small-prime residues, a newly selected prime determines its initial horizon residue, and every later selection of an already known prime is determined without another branching choice. This allows arbitrary quiet ticks, smaller relays and repeated large labels in a substantially longer polylogarithmic interval. A separate gain capacity per prime turns this into an upper bound on rapid completed recoveries under explicit size/duration/label conditions. No finite-twins contradiction.

## 1. Finite discovery-only compression

Use adaptive MIN, with even horizon H, prior tick t, ordinary deficit d=2t-H>=0 along a canonical ray, next tick n=t+1, I=n mod2, e=1-2I. The selected prime is the least eligible odd prime dividing gcd(n-2I,H-e), or there is no event. Its gain is s-1, and d_new=d+2-(s-1), or d+2 on quiet ticks. The raw gcd is exactly gcd(F,H-e), where F=d+3-6I is odd and nonzero, since 2(n-2I)-(H-e)=F and H-e is odd.

Fix a starting horizon interval [A,A+G], an initial deficit bound D>=0 and an integer maximum length L>=1. Assume
    D+2L+3 <= sqrt(A+1).                                (1)
This ensures every possible prime factor of a tick defect during such a prefix is eligible under the adaptive cutoff, since d<=D+2L and H>=A. The upper counting result concerns prefixes staying in d>=0, including canonical ones. Let S>=3 be an integer small-prime cutoff, P_S the product of the odd primes <=S, and
    b= floor(log(D+2L+3)/log(S+1)).
The number of distinct possible selected primes >S at any tick is <=b because each divides F, and their product is <=|F|. If b=0 no such discovery is possible.

Call a prime >S new at its first selection in this prefix. We count start states whose next AT MOST L ticks select at least j distinct primes >S, for an integer 1<=j<=L. Stop encoding at the j-th new prime, whether or not the original trajectory later continues for all L ticks. Specify the following data:
* initial even d0 in [0,D], initial time parity I0, and H_start mod P_S;
* the j tick positions of the first selections of the distinct new primes, in [1,L];
* at each such position the chosen new prime.

To reconstruct the prefix, keep a list of known primes with their residues of H_start. Initially these are all odd primes <=S, with residues given by the specified H_start mod P_S. The initial congruence H_start=2I0-d0 mod4 is also known. At each tick the current deficit d, current side I, and prior cumulative horizon gain g are known from the reconstructed previous ticks. Every known prime f is eligible to fire exactly when f divides F=d+3-6I and H_start+g=e mod f. The cutoff is automatic by (1).

At a tick not specified as a discovery, an actual word must select the least known firing prime, or be quiet if no known prime fires. Indeed if an unknown prime won, it would be a new discovery. Unknown primes that do not win have no influence. At a specified discovery, choose a prime >S that is not already known and divides F. There are at most b choices at that step, regardless of the previous choices. Reject any inconsistent data (including a smaller known firing rival). Selection of this new prime s forces
    H_start=e-g mod s,
so add s and its residue to the known list. Update d and g, and continue. The possible starts for a given specification are thus restricted to a single residue class modulo
    4 P_S prod_{i=1..j} s_i.
This is necessary, not sufficient; the reconstruction may accept extra congruence candidates where an unrecorded prime would actually win. Every actual prefix is encoded and reconstructed correctly. No complete word enumeration or independence hypothesis is used.

There are <=D+2 initial d0,parity pairs, P_S residue choices, binom(L,j) sets of discovery positions, and at most b^j branching choices (new labels are chosen from the current defect, not arbitrarily from all primes). Each CRT class contains at most 1+floor(G/(4P_S(S+1)^j)) starts in the horizon interval. Consequently the number of distinct starting states is at most
    (D+2) binom(L,j) b^j [P_S + G/(4(S+1)^j)].          (2)
An integer floor can be taken of this upper bound. The same bound applies to start ticks on one ray, since fixed H,d determine the absolute t uniquely. Overlapping prefixes are allowed. Unlike the previous B^L word count, the combinatorial cost here depends primarily on the number of distinct newly selected primes, not the number of ticks or total selected events. The cost P_S records the small-prime residue data; it is not omitted when the interval is shorter than the combined CRT period.

## 2. Longer polylogarithmic windows

Let X tend to infinity, starting horizons in [X,lambda X] with lambda>1 fixed, initial deficit D=O(log^C X) for fixed C>0. Let
    S=floor(a log X), 0<a<1,
    L=floor((log X)^B), fixed 1<=B<2,
    j=ceil(theta log X/log(S+1)), theta>0 fixed.
For large X, condition (1) holds, j<=L, b=O_{B,C,a}(1), and by the unconditional prime number theorem P_S=X^(a+o(1)). Since (S+1)^j>=X^theta and binom(L,j)<=(eL/j)^j,
    log binom(L,j) <= theta(B-1) log X+o(log X).
The factors D+2 and b^j have logarithms o(log X). Thus (2) gives the uniform occurrence upper bound
    #starts <= X^(theta(B-1)+max(a,1-theta)+o(1)).      (3)
If a+theta<=1 this becomes X^(1-(2-B)theta+o(1)). For theta=1-a the exponent is a+(1-a)(B-1). This is a power saving over X, allowing time lengths up to (log X)^B for any fixed B<2, unlike the earlier short-time enumeration that required a time interval o(log X) for its stronger count. The new theorem requires distinct labels (rather than merely many selected events), but repeated selections of already known labels impose no extra encoding cost, and the whole intervening low-prime evolution is included.

There is no claim that a short prefix with large total event count must have j distinct large primes for arbitrary L; this will instead follow under a gain condition from section3. If labels are restricted to <=R~rho log X, then j cannot exceed pi(R)-pi(S). To use (3) nontrivially for that band choose theta<rho-a, not theta=1-a at a balanced rho=1/2 cutoff.

## 3. Clock gain capacity per prime

Consider an arbitrary consecutive interval of at most L integer ticks. Let m_s be the number of times a fixed odd prime s is selected, and suppose m_s>=1. At its selected ticks n_i with I_i=n_i mod2, the adjusted coordinates u_i=n_i-2I_i are all divisible by s. For consecutive selected ticks of this prime, u_{i+1}-u_i is a positive multiple of s: for the same side the positive difference is even and divisible by s; for even-to-odd it is odd and >=-1, so cannot be a nonpositive multiple of s; for odd-to-even it is positive. Consequently
    (m_s-1)s <= u_last-u_first
               = n_last-n_first-2(I_last-I_first)
               <= L+1.
In particular
    m_s <= 1+floor((L+1)/s),
    gain from s <= (s-1)(1+floor((L+1)/s)) < L+s.        (4)
The strict last inequality follows by replacing the floor with (L+1)/s and simplifying. It improves the naive bound with a factor two in the possible clock-edge losses; it also applies when the same prime is selected on both sides. For a prime that does not occur its gain is zero and the upper bound remains true.

Define the exact small-prime upper capacity
    C_S(L)=sum_{3<=s<=S, s prime}(s-1)(1+floor((L+1)/s)).
Then
    C_S(L) <= L*pi_odd(S)+sum_{3<=s<=S, s prime} s.
For a prefix with all selected labels <=R, if it uses fewer than j distinct labels >S, its gain is at most
    C_S(L)+(j-1)(L+R).                                 (5)
This inequality includes all small-prime relays and repeated selections. It is independent of the deficit path. In particular if gain exceeds (5), at least j distinct labels in (S,R] must have been discovered by that time, so (2) applies when initial deficit and cutoff satisfy its assumptions.

## 4. Application to rapid recovery after A1

Recall A1 label p>=47, pre d+3<=p/5, post adjusted D_adj=2p, hence post ordinary deficit d1=2p+6I and x1=d1+3>=2p+3. Count A1 marks with starting horizons in [X,lambda X], p>R, p<=log^C X. Consider only marks for which the first subsequent recovery to x=d+3<=p occurs within L ticks after the mark, using only labels <=R (quiet ticks and smaller relays allowed). If the recovery has elapsed T_rec<=L and gain G_rec, then
    G_rec=2T_rec+d1-d_end >= p+3.
Thus if
    p+3 > C_S(L)+(j-1)(L+R),                            (6)
at least j distinct new primes >S occur in the completed recovery, by (5). No minimum wait assumption or distinctness of all selected labels is made. The initial post-A1 horizon lies in [X,(lambda+1)X] for large X by the adaptive label bound, and initial deficit is O(log^C X). Distinct marks give distinct start ticks. Apply (3) to bound the number of these marks.

For clarity take R~rho log X, with 0<a<a+theta<rho<=1 fixed, 1<B<2, and S,L,j as in section2. The prime number theorem gives
    C_S(L) <= (a+o(1))*L*log X/loglog X,
    (j-1)(L+R) <= (theta+o(1))*L*log X/loglog X,
since R/L->0 and sum of small primes <=S*pi(S)=o(L log X/loglog X).
For any fixed epsilon>0, (6) therefore holds for
    p >= (a+theta+epsilon)*L*log X/loglog X
for sufficiently large X. The recovery count is bounded by
    X^(1-(2-B)*theta+o(1)).                             (7)
This is a genuinely longer recovery interval than the earlier result, permitting many repetitions and arbitrary low relays, at the price of a different size/density requirement. If a+theta+epsilon>rho the range can be vacuous by the total clock capacity; one may choose epsilon with a+theta+epsilon<rho.

Example at the previous balanced cutoff R largest prime with P_R<=sqrt X, so rho=1/2. Take
    a=1/20, theta=2/5, B=6/5, epsilon=1/100,
    L=floor(log^(6/5) X),
    p >= .46*L*log X/loglog X, p<=log^C X.
Then the number of A1 marks that recover to x<=p in <=L ticks using only labels <=R is
    <= X^(17/25+o(1)).                                 (8)
The exponent .68 is strictly less than the previous necessary far-A1 count exponent9/11=.81818... under sparse N,B_R. The two populations are NOT shown to coincide. In particular the large-count theorem does not force enough marks in the size range (6), or enough recovery completions within L ticks, or the exclusion of all labels >R. Thus this is not a contradiction with that lower count. At a near-X cutoff rho=1 the same general formula allows theta closer to1-a, and hence smaller exponents for B close to1, but it counts a different population.

One additional disjointness observation: within a dyadic band [T,2T], recovery intervals from post-A1 to first x<=p cannot contain another mark from the same band before that recovery is completed. An intervening A1 q<=2T would need pre x<=q/5<=.4T<p, contrary to the old pending condition x>p. The pre-event deficit for A1 is at its preceding event time, so if that state is already <=p the old interval ended no later than that time. Therefore same-band completed recovery intervals have disjoint tick interiors. If a band has m marks of the size condition above, all completed inside the given block using <=R, at most the count (7) have duration <=L, and the remaining ones use at least L ticks each. In a crossed horizon block with total elapsed time O(X), this yields m<=O(X/L)+X^(1-(2-B)*theta+o(1)). This does not conflict with the previous lower counts, but the time cost can be charged without overlap in a dyadic band. No claim is made for recoveries that have not completed within the block or that use labels >R.

## 5. Diagnostics and preservation

[Discovery audit d7932a5](https://github.com/tara-sooo/A166944-Lean/blob/d7932a5bca5425eb1a68268a566c19f295a1828e/research/min_direct_discovery_word_packing_audit.mjs), blob a61cbbdf2572c5e517c77636dc9c15887fb64370, exact remote readback. Run node research/min_direct_discovery_word_packing_audit.mjs 8000. Actual ECMAScript in tool runtime: 83,539 exhaustive abstract starts across five L,S,j,D controls, starting H large enough that all possible defect primes are eligible. Also 3,998 odd canonical roots through8000,482,540 ticks and50,559 events with cap3000 ticks (not all termination asserted). 55,367 prefixes encoded and reconstructed,809,921 reconstructed tick labels,96,089 new discoveries,1,687 repeated high-label selections,76,173 low-label selections;30,446 prefixes include smaller relays and1,576 include repeated high labels. 54,498 code groups,869 CRT spacing checks,11,999 aggregate capacity bounds,229,733 per-prime clock checks using (4),828 forced-discovery gain tests. All final assertions passed. Small integer prime factoring; BigInt support products and combinatorial bounds. No qualifying completed A1 recovery was found in this small canonical scan under its 60-tick diagnostic limit; the separate witness below exercises a real completed recovery. The initial version tested a looser per-prime clock bound; the final committed version was rerun using (4).

[Canonical recovery witness 3914143](https://github.com/tara-sooo/A166944-Lean/blob/3914143b42967a67811464577d949598262850a0/research/min_direct_discovery_recovery_witness.mjs), blob 454cd86a77ac5cf9d2af55bb24f046671fcc4fbb, exact remote readback. Run node research/min_direct_discovery_recovery_witness.mjs. Reconstruct the previously obtained 9,962-digit canonical root with word7687/5233/3541/2389/1621/1093/733/7369. 22,195 literal BigInt GCD ticks and20,600 CRT residue checks; all selected labels eligible and intended post deficits verified. After A1 p7687, the first recovery to x<=p is completed in240 ticks by selected labels5233 and3541, with ordinary deficit15374->7082 and gain8772. At S=7 the exact C_S(240)=568; at S=47 it is3244. In both cases gain exceeds C_S(240)+(240+5233), forcing at least two distinct high labels, which matches the actual word. At S100 the forced count is1, at S1000 it is0. Four independent residue-based reconstructions of all240 recovery ticks succeed, with discovery positions162 and240. This is a prior root reconstructed and retested, not a newly discovered root or an infinite ray.

The arguments concern arithmetic counts and actual finite diagnostics. No historical novelty claim, Lean kernel verification or stopping theorem. No new Fourier exponent. Main/sibling branches unchanged. Next investigate recovery intervals longer than the polylogarithmic scale, or whether high-label discovery can be forced by the earlier cluster matching without imposing a rapid-completion hypothesis. The gain capacity and discovery encoding do not establish such a forcing implication.
