# Fresh rough plateaus: exact first-clock scores and the reset/nonreset law

Continuation of [defdfc7](https://github.com/tara-sooo/A166944-Lean/commit/defdfc72092befe337e8bd6b30e3680813d5ab6d), on the independent direct-arithmetic branch. The previous one-sided record attrition theorem concerns a restrictive closed two-event return class. Here we return to the general MIN rule. For plateaus with no small prime factors and sufficiently small ordinary deficit, the first-clock problem has an exact solution, and both adjusted resets and nonresets are asymptotically equally represented. A finite inclusion-exclusion transfer gives this law for actual large canonical integer roots. This is not an independence assertion along one fixed ray or a twin-prime proof.

## 1. Exact clock scores

At a plateau (t,H) put d=2t-H. Let L>=7, assume 0<=d<=L-3, H even, and no odd prime <=L divides either H-1 or H+1. For each odd prime p>L put c=1-H mod4 (c=1 or3), and k_p=1 if p=c mod4, else 3. For an eligible p dividing H-e, with e=+1 even or e=-1 odd, its first strict future clock is
    w_+(p)=(k_p*p-d-1)/2,
    w_-(p)=(k_p*p-d+5)/2.
Proof: the even-side raw gcd divides the signed defect 2n-H+1=d+2w+1, and the odd-side raw gcd divides 2n-H-5=d+2w-5. At its appropriate tick both defects are c mod4. Their smallest positive multiples of p in that class are k_p*p. Since d<=L-3<p-3, these occur strictly after t. Any nonpositive multiple cannot occur earlier: the defects are nonzero odd and are greater than -p for future ticks. If p divides H-e, divisibility of the defect by p is equivalent to divisibility of the corresponding clock argument by p. The formulas therefore give exact first clocks (including parity), not approximations.

Define the score S_+(p)=k_p*p and S_-(p)=k_p*p+6. Both give w=(S-d-1)/2. The actual next event minimizes these scores over eligible divisors of the respective neighbors. The scores are distinct: even-side scores are c mod4, odd-side scores c+2 mod4; within one side k_p*p values are distinct because p>7 prime and p'=3p cannot be prime. No tie rule is needed in this special plateau. At the winner, post horizon Z=H+p-1 and adjusted deficit D=2(t+w)-Z-6I, I=(1-e)/2, satisfy
    D=(k_p-1)*p.
Thus if H=0 mod4, p=1 mod4 gives D0 and p=3 mod4 gives D=2p; if H=2 mod4 the roles reverse. The side itself is not fatal. D0 on odd side immediately gives a canonical reentry; D0 on even side gives one in <=7 further ticks, or termination, by 123bbd4 for large H. Nonreset D=2p gives ordinary post deficit 2p+6I, not a proof of later failure. This calculation applies to arbitrary actual plateaus satisfying the two hypotheses, not just canonical roots.

## 2. Formal conditional score distribution

As in previous residue papers use independent uniform initial residues at odd primes with prescribed parity, for analysis of integer families. A finite history that determines the current gain, absolute tick parity, H mod4 and d using only primes <=L may be conditioned upon, together with no divisors <=L of H+-1. Then at each p>L the two residues H=1 and -1 modp are disjoint and independently uniform across different p. The shift from the initial horizon is fixed by the conditioned information. The following formulas hold for the uncut formal process after such a plateau. They do not assume all actual MIN records satisfy the plateau hypotheses; in particular a new actual record may preempt an existing small clock.

Let S denote the winning score. For real s>=L, put
    rho_p(s)=1_{k_p*p<=s}+1_{k_p*p+6<=s}.
The exact conditional survival law is
    Q_L(s)=Pr(S>s)=product_{p>L}(1-rho_p(s)/p),          (1)
where only finitely many factors differ from 1. For an individual score a=S_e(p), the probability that it is the winner is
    Q_L(a-)/(p-rho_p(a-)).                            (2)
The denominator is p at the first clock of p and p-1 at the second, since one residue at that prime was already excluded. Derivation: all earlier scores missed, and at p exactly one still-allowed residue gives the current hit. No independence between the two sides at a single prime is asserted. All formulae depend on H mod4 but not on d within the assumed range.

For s>=L the full two-residue product q_L(s)=prod_{L<p<=s}(1-2/p) differs from (1) only at primes in (max(L,(s-6)/3),s]. The sum of their reciprocals is O(1/log L), uniformly for s>=L as L->infinity: if s<=4L use (L,4L], and otherwise a bounded multiplicative interval comparable to s; elementary Chebyshev prime counting suffices. Therefore
    Q_L(s)=q_L(s)*(1+O(1/log L))                       (3)
uniformly. In particular Q_L(s)->0 as s->infinity by the divergent prime reciprocal sum. A formal winning score exists almost surely.

## 3. Limiting joint law: two sides and two adjusted deficits

Use the classical prime number theorem in the two reduced classes mod4 (or the corresponding Mertens reciprocal-prime asymptotic). This is a standard theorem, not a prime-pair conjecture. For fixed 1<=a<b<infinity, as L->infinity,
    sum_{L^a<p<=L^b, p=c mod4} 1/p -> (1/2) log(b/a)
for either c. The corresponding unrestricted sum tends to log(b/a), by partial summation. The estimates also hold with endpoints shifted by fixed multiplicative factors, whose reciprocal sums are O(1/log L). The convergence of cumulative sums is uniform on compact ranges of exponents, by monotonicity and continuity of log. Combining with (3), for fixed v>=1,
    Pr(S>L^v) -> v^(-2).                              (4)
In detail log q_L(L^v)=-2 sum_{L<p<=L^v}1/p+O(1/L), uniformly on compact v intervals.

For each e in {+1,-1} and k in {1,3}, equations (2)-(3) give the probability mass at its p as (1+O(1/L))*Q_L(S_e(p)-)/p. On a compact exponent range this survival factor is (log p/log L)^(-2)+o(1) uniformly, since S_e(p) differs from p by at most a bounded factor. Summing these weights over the required mod4 class, using the reciprocal sum limit (equivalently Riemann sums with arbitrarily fine fixed exponent partitions), gives
    Pr(L^a<S<=L^b, side=e, k_p=k)
        -> (1/2) integral_a^b v^(-3) dv
        = (1/4)*(a^(-2)-b^(-2)).                     (5)
No atom at either limiting boundary. To pass b->infinity, use the uniform elementary bound Q_L(L^b)<=C/b^2 from q(x)=Theta(log^-2 x) and (3). Thus
    Pr(S>L^a, side=e, k_p=k) -> 1/(4*a^2), a>=1.
In particular each of the four pairs (side, reset/nonreset) has limiting probability 1/4. The logarithmic size of the winner, log S/log L (equivalently log p/log L in the limit), has tail a^-2, jointly asymptotically independent of the four types. The two reset types together have limiting probability1/2; the two nonreset types together1/2. This is a conditional distribution over unexposed residues at a rough low-deficit plateau. It is not the unconditional law at arbitrary stopping times of a fixed integer trajectory.

## 4. Integer-family transfer beyond the complete CRT period

We give a uniform finite counting argument for ordinary canonical roots. Let N->infinity, fix 0<b<1, put
    L=exp((log N)^b), U=exp(log N/(1024 loglog N)).
For large N, 7<=L<U, L^a<U for every fixed a>0 eventually, and U^2=o(N). Nonintegral cutoffs mean primes at most that real number. Start odd integer M in [N,2N], H=2M-2=0 mod4, d=6, and require H+-1 avoid all odd primes <=L. Thus the plateau hypotheses are satisfied, and every score <=U uses p<=U, automatically adaptive eligible. Any winning score <=U is determined exactly by the finite congruences; untested larger primes cannot have earlier scores. A root for which none of the scores <=U hits may be terminal or have a later event; it is included in the tail.

We count the roughness condition, the tail S>U, and each individual winning candidate score <=U. Each count is of odd integers M in the interval. For any one candidate p,e, force the residue H=e modp (equivalently M one residue modp), and for every other prime through U impose up to two forbidden residues, including both for all primes <=L and the earlier tested sides for the rest. The previous same-prime miss, if any, is automatic under the forced residue. For roughness or survival alone no forced prime is needed. Conditions are independent across distinct primes by CRT for complete residue periods, but the full period may be huge.

Here is the needed finite truncation. Let q_0 be 2p for a forced candidate, or 2 without a forced prime, and let rho(l) in {0,1,2} count the forbidden residues at unforced primes l<=U. Each subset J of violated prime conditions has count
    N/q_0 * product_{l in J}(rho(l)/l) + O(2^|J|).
Indeed the number of residue classes is product rho(l), and counting each class has error <=O(1), by CRT. Let m be the least odd integer >=100 loglog U. The elementary bound sum_{l<=U}2/l<=3 loglog U holds eventually (from the earlier prime reciprocal estimates). The main-coefficient Bonferroni upper and lower truncations at m+1,m differ by at most
    (3 loglog U)^(m+1)/(m+1)! = O((log U)^(-3)).
The product coefficient beta=prod(1-rho(l)/l) is >=prod_{3<=l<=U}(1-2/l)>=c/(log U)^2, so the relative main-coefficient error is o(1). The total residue-class counting error is O((2U)^(m+2))=O(N^(1/4)) for all sufficiently large N, since m+2<=101 loglog N and log(2U)<=2 log N/(1024 loglog N). This is negligible uniformly even for q_0<=2U: N/(q_0 log^2 U)=N^(1-o(1)). Thus every such count equals its independent-residue density times N/2, with multiplicative 1+o(1) uniform across all individual candidate scores and the roughness/tail tests. This is an elementary finite count, not a lower-bound sieve for actual primes. Summation over disjoint winning candidates preserves the uniform relative error.

The rough roots themselves have cardinality (1+o(1))*(N/2)*q(L), q(L)=prod_{3<=p<=L}(1-2/p)=Theta(log^-2 L), i.e.
    Theta(N/(log N)^(2b)).
Conditional on belonging to this family, the proportion with no event score <=U is at most (1+o(1))*C*(log L/log U)^2=o(1). Equations (4)-(5) therefore transfer in full:
    proportion of rough actual roots with winning S>L^a, side=e, k_p=k
       -> 1/(4*a^2), for every fixed a>=1.
Any unclassified outcome beyond U has relative density o(1); no assumption of nontermination is needed. In particular half the rough roots have first adjusted reset asymptotically, half have adjusted deficit 2p, and each of the four categories has Theta(N/(log N)^(2b)) roots. The prime class for reset here is p=1 mod4. All counted winning scores <=U give genuine actual adaptive events. Since S>L and p>L, the labels and the nonreset deficits exceed every fixed polylogarithmic scale for b>0. The reset branch normalizes to a later canonical root in at most seven further ticks or terminates; the nonreset branch has d'>=2p. These are actual families of initial roots, not statements of successive record independence.

## 5. Relation to finite twins and next target

The previous closed-cylinder attrition argument kills a chain on a wrong-side record. The exact general law here shows why that interpretation does not carry over to general MIN: either side can reset, and the nonreset type is not fatal. Under finite twins every sufficiently large rough canonical root extends to an infinite trajectory, and the four initial types remain present in the above asymptotic proportions. This does not contradict finite twins. Nor is it proved that infinitely many rough low-deficit plateaus occur on every ray, or that the fresh-residue distribution can be repeatedly applied at an arbitrary late plateau. Any global use needs control of the information already exposed and of preemption of known clocks. The next target is a deterministic criterion that forces such rough low-deficit plateaus or an alternative global invariant, rather than an assumed generic half-probability of stopping.

## 6. Verification

[Audit a4f47d5](https://github.com/tara-sooo/A166944-Lean/blob/a4f47d5ae24caabb981efc65198ab6582da10268/research/min_direct_fresh_plateau_score_audit.mjs), blob 4f8a8a040003a52463b0fcb19c9bdae9a7eb3013, exact remote readback. Run node research/min_direct_fresh_plateau_score_audit.mjs. Executed ECMAScript audit function in tool runtime, not a separate Node process.

Five finite prime ranges (L,U)=(7,19),(11,23),(13,29),(17,31),(19,37), both H mod4 classes and every even d<=L-3: 62 configurations, 23,884,886 complete fresh-residue assignments, 496 score/parity checks, 558 exact count checks. Compared the predicted score winner with direct factor-clock modular waits. Finite enumeration is known-only through U; only scores <=U (or quiet prefix through U) were checked as actual integer outcomes. In addition 24 exact CRT controls for p=29,31,41,43,101,103, both horizon classes and sides, isolate each reset/nonreset type through all possible earlier defects. Total 287 literal integer path/prefix controls, 3,895 BigInt gcd ticks, 213 reset outcomes, 12 nonreset outcomes, 62 quiet controls. All assertions passed. These finite samples do not estimate the asymptotic fractions. No Lean executable/kernel verification, external novelty claim, or actual infinite integer ray. Main and sibling branches unchanged.
