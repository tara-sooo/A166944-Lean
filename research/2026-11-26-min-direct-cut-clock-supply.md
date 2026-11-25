# Fixed deficit-cut clock supply and canonical unit-wait recovery cylinders

Continuation of [6980a31](https://github.com/tara-sooo/A166944-Lean/commit/6980a312496a3f7d0747b12471d3bae9fa82d8c8), using the earlier factor clocks (395e9ea) and downward deficit barriers (a3f181e). At a fixed deficit cut and fixed recovery label the multiplier and horizon residue are determined. Here the competing clocks give exact forbidden residues for candidate horizons, rather than just the earlier spacing bound. A long minimum wait produces a sieve saving. However the unit-wait case can saturate the whole abstract horizon progression. More strongly, there are genuine canonical MIN prefixes with arbitrarily large multipliers at an arbitrarily long fixed finite sequence of distinct small labels, all at unit waits following A1. This is an obstruction to local uniform multiplier bounds, not a contradiction with finite twins.

## 1. Fixed ordinary-deficit cut and exact competing clocks

Use adaptive MIN: even H>=8, prior tick t, selected odd prime s with s^2<=H+1, earliest tick n=t+w, side I=n mod2 in {0,1}, e=1-2I, s|H-e, s|n-2I, gain g=s-1, post H'=H+g. Ties are broken by least eligible prime. Ordinary deficits d=2t-H, d'=2n-H', adjusted D=d'-6I. At nonreset s>=5, D=2sh with integer h>=1. Fix a positive even ordinary deficit cut b and require d'<b<=d. Then
    h=floor((b-6I-1)/(2s)),
    r=b-6I-2sh,
    r in {2,4,...,s-3},
    1<=w<=(s-1-r)/2.                                   (1)
Indeed b-d'=r is positive even and d-d'=s-1-2w<=s-3<2s, giving the unique h and inequalities. If h<1 or r is outside this set, there is no nonreset crossing with the indicated s,I. Write q=(H-e)/s odd. From the post-deficit formula,
    n=(H+s-1+2sh+6I)/2=s*((q+1)/2+h)+2I.
The parity condition gives q=2I-2h-1 mod4, hence
    H=e+s*(2I-2h-1) mod4s.                              (2)
These identities refine the old fixed-cut spacing only after the following rival exclusions.

Let f be an odd prime different from s, eligible at H (f^2<=H+1), and J in {0,1} its possible side, e_J=1-2J. If H=e_J mod f, its firing ticks are 0 mod2f for J=0, f+2 mod2f for J=1. Let ell be the backwards lag from the candidate n to the most recent such tick, in [0,2f-1]. The parity and residue of ell are determined by s,h,I,f,J, independent of H inside the selected congruences:
    ell = I-J mod2,
    2ell = (2h+1)*s+6*(I-J) mod f.                      (3)
Proof: subtract the rival clock tick residue from n and multiply by2, then use H=e_J mod f in 2n=H+s-1+2sh+6I. Since f is odd, the two congruences determine exactly one ell in [0,2f-1].

Fix an integer minimum wait W with 1<=W<=(s-1-r)/2. Define the forbidden residue set F_f subset of {+1,-1} (mod f) by
    e_J belongs to F_f iff
        (ell=0 and f<s) or (0<ell<W).                    (4)
Every actual crossing at this cut with label s, side I, wait w>=W has H not in F_f mod f for every eligible f!=s. If 0<ell<W<=w the rival tick is strictly after t and strictly before n. If ell=0 and f<s it wins the tie. A lag exactly W is not forbidden for the candidate wait W, because the starting tick is excluded. If a larger rival ties, it is allowed.

Conversely, for an even H>=8 with s^2<=H+1 satisfying (2), avoidance of (4) for ALL eligible f!=s is sufficient to produce an abstract state with a crossing at wait exactly W: set n by its displayed formula, t=n-W. Then d=d'+s-1-2W>=b, d'<b; s's own previous clock is 2s earlier and W<2s, and no rival earlier tick or smaller tie is possible. This gives the exact set of H permitting a crossing with some wait>=W from some abstract starting state. It says nothing by itself about whether that start is reached from a canonical root. The strict future convention and the adaptive cutoff are essential.

## 2. Deterministic supply count

Fix a horizon interval [A,B] with A>=max(8,s^2-1). Count the integers H satisfying (2) in that interval, call their number M. They are consecutive terms of a progression of step4s. Choose any finite set F of odd primes f!=s with f^2<=A+1, so they are eligible everywhere in the interval. Let
    P_F=prod_{f in F}f,
    a_F=prod_{f in F}(f-|F_f|),
    alpha_F=a_F/P_F.
The progression parameter runs bijectively through residues modulo each f. Thus exact CRT gives a_F allowed progression parameters per complete P_F-period, and every partial period contributes at most a_F. In particular the number of actual crossings of this b,s,I type at wait>=W on a monotone horizon trajectory in [A,B] is <=
    alpha_F*M+a_F.                                    (5)
One may use floor(M/P_F)*a_F plus the exact allowed count in the remaining interval if its initial residue is known. This is an upper bound for actual occurrences since the horizon increases strictly at events, so the same pre-H cannot occur twice. It can be minimized over choices of F and capped by M. No distribution assumption on H or t is needed.

For each odd f<=W/2, f<s by (1), and every lag is either zero (smaller tie) or in [1,2f-1]<W. Both residues are forbidden. Thus a long wait gives a two-root sieve saving. For example let z=min(W/2, log M/(8 log 2)) when M>=2, choose F all odd primes <=z. Chebyshev's primorial bound P_z<=exp(4 log2*z) gives P_F<=sqrt(M), and the primes are eligible because f<s. By the standard Mertens product bound, prod_{3<=f<=z}(1-2/f)=O(1/log^2(2+z)) (using 1-2/f <= (1-1/f)^2 and the usual prime product). Hence, uniformly in the cut, label and side, the occurrence count is
    O(M/log^2(2+z)+sqrt M),                              (6)
with the trivial bound for M<2. The full residue bound (5) also captures h-dependent exclusions beyond these small primes, without invoking any analytic theorem. In the logarithmic-size recovery band s=Theta(log X), even for W=Theta(s), this generic fixed-label/cut sieve improvement is logarithmic rather than a fixed power of X. It does not exclude the necessary X^(9/11)/log X recovery-population scale from 6980a31. Further, that necessary population includes short-cluster precursors that need not themselves downcross the cut; (5) applies only to actual nonreset downcrosses, not automatically to every such precursor. No stronger global supply ceiling is claimed.

## 3. Unit-wait saturation and why a universal local saving fails

At W=1 no positive lag is forbidden. The only exclusions come from smaller-prime ties, on the same side (opposite-side parity gives odd lag). For f<s and same side, (3) gives ell=0 iff f|(2h+1), since f!=s. All such smaller primes are eligible. Therefore the exact criterion at unit wait is simply
    H not congruent to e mod f
          for every odd prime f<s dividing 2h+1.        (7)
If 2h+1 has no prime factor below s, every H satisfying (2), H>=max(8,s^2-1), is a valid abstract unit-wait recovery candidate with the chosen cut and label (when (1) is feasible). In particular for any fixed s>=5 choose 2h+1=s^k, k>=1, and b=2sh+6I+2. Then (1) allows W=1 even at s=5. This saturates the entire abstract progression of spacing4s. It does not exhibit a canonical orbit visiting those consecutive candidates. It shows that a universal extra sparsity factor for high multipliers cannot follow from the single-cut clock congruences alone.

## 4. Genuine canonical prefixes with fixed small labels and unbounded multipliers

The abstract saturation does not establish ancestry. The following independent CRT construction does establish canonical ancestry, for a fixed finite word of small labels and arbitrarily large first A1.

For every fixed integer k>=1 there exist k distinct fixed odd primes s_1,...,s_k>=11 such that for arbitrarily large primes p (in fact infinitely many p in one arithmetic progression), a canonical root H0=2M-2, t0=M+2=H0/2+3, M odd, has first k+1 labels
    p, s_1,...,s_k
at respective waits
    (3p-7)/2, 1,...,1,
with p the even-side A1, and every subsequent event a nonreset ordinary-decreasing event. For every j>=1 its multiplier tends to infinity with p while the s_j are held fixed. There are arbitrarily large canonical roots for each chosen p in this construction. The word is chosen to satisfy the construction; arbitrary prescribed words are not claimed.

Proof. Let B0=max(7,k+2). Define G_j=sum_{i<=j}(s_i-1), G_0=0, I_j=j mod2, e_j=1-2I_j, and
    c_j=2j+1-6I_j-G_{j-1}.
Choose the s_j successively by Dirichlet's theorem, each congruent to1 modulo the product of all odd primes <=B0 and all preceding s_i, and larger than B0, all previous labels, and a sufficiently large fixed bound depending only on k and G_{j-1}. More explicitly require
    s_j > 20+10k+4G_{j-1}.
Then c_j is odd and nonzero, |c_j|<s_j, and the integer 2j+5-10I_j-3G_{j-1} differs from +2 and -2 by nonzero integers of absolute value<s_j (odd minus even cannot vanish). Also any earlier-stage difference G_{i-1}-G_{j-1}+e_j-e_i, i<j, is nonzero of magnitude<s_j, since each previous gain>=10. This explicit size bound suffices for all the exclusions below.

Choose p large in the arithmetic progression given by
    p=3 mod4,
    p=1 mod f for every odd prime f<=B0,
    2p=-c_j mod s_j,
    2p+c_j !=0 mod s_j^2   for each j.
Choose one of the nonvanishing lifts for the last condition. The residue of p at s_j is nonzero since 0<|c_j|<s_j. All moduli are coprime after combining each s_j condition into one lift modulo s_j^2, so the resulting residue class is reduced and Dirichlet gives arbitrarily large primes p. Take p>=47 and large enough compared with the fixed G_k,k,labels that every F_j=2p+c_j is positive, less than3p+6, and p^2 bounds all s_j^2.

Construct H0 modulo4 and all odd primes f<=3p+6. Require H0=0 mod4 and H0=1 mod p. At all other primes forbid H0=+1,-1 mod f to make the initial neighbors free of competing small factors. The first even p event then occurs at wait (3p-7)/2, since p=3 mod4, H0=0 mod4, t0=H0/2+3 is odd, H0=1 mod p; the first positive even-side p clock has that relative tick. The earlier quiet-tick raw GCD defects divide nonzero odd integers bounded in magnitude by3p+6 (from the canonical formulas gcd(M+j,2j+1) or gcd(M+j+2,2j+7)). Therefore no other prime can fire before it. At the selected tick the raw even gcd is exactly p: it divides3p, contains p, and H0-1 is not divisible by3. The selected tick is n1=(H0+3p-1)/2, even, and the post ordinary deficit is2p. With p>=47 this is A1 since the initial deficit is6.

At the j-th desired unit step after this event, pre H=H0+p-1+G_{j-1}, tick n=n1+j, side I_j, and the raw gcd is
    gcd(n-2I_j,H0+p-1+G_{j-1}-e_j).
It is odd and equals
    gcd(F_j,H0+p-1+G_{j-1}-e_j), F_j=2p+c_j,            (8)
by multiplying its first argument by2 and subtracting the second (the second argument is odd). To obtain exactly s_j impose
    H0=-(p-1+G_{j-1}-e_j) mod s_j.
The target s_j divides F_j exactly once by the choice of p. For any other prime f dividing F_j forbid that same horizon residue modulo f.

Check simultaneous feasibility for all f<=3p+6:
* f=p: H0=1, and p does not divide any F_j because 0<|c_j|<p.
* f=s_j: the prescribed H0 has 2H0=2j+5-10I_j-3G_{j-1} mod s_j, so it is not +/-1 by the size bound. For earlier i<j the offset difference G_{i-1}-G_{j-1}+e_j-e_i is nonzero with magnitude<s_j. For later i>j it equals -1+e_j-e_i mod s_j, since the included gain s_j-1 is -1 mod s_j and all subsequent s_l are1 mod s_j. This is -3,-1,or1, never0. Thus none of the other stages conflicts even if s_j also divides their defects.
* For odd f<=B0 choose H0=0. All s_i=1 mod f and p=1 mod f, so every stage argument H0+p-1+G_{j-1}-e_j=-e_j mod f is nonzero. The initial +/-1 exclusion also holds.
* Every remaining f>B0 is not a target or p. There are at most k+2 forbidden residues (two initial and at most one for each stage with f|F_j). Since f>k+2, a residue remains.

CRT now provides H0 simultaneously in all required classes; choose it arbitrarily large with H0>=p^2+8. It defines the canonical odd M=H0/2+1. All selected primes are eligible. Formula (8) gives exactly s_j at the very next tick, so the adaptive MIN rule necessarily selects it. Induction confirms the whole prefix. At step j,
    d'_j=2p-sum_{i<=j}(s_i-3),
    D_j=d'_j-6I_j=F_j-s_j,
    h_j=(F_j/s_j-1)/2.                                  (9)
The quotient F_j/s_j is positive odd and tends to infinity, so h_j>=1 for sufficiently large p. Each drop s_j-3 is strictly positive, the wait is1, and all h_j grow linearly in p. This proves the construction.

The k labels are fixed as p tends to infinity but may grow very rapidly as k increases. The total recovery of this fixed word is a fixed number, not a fixed positive fraction of the unbounded initial deficit. The constructed horizons can grow much faster than p because the CRT modulus involves primes up to3p+6. This is not a construction of polynomial-in-H multipliers, of a single infinite ray, or of a repeated word with positive asymptotic frequency. The theorem isolates an actual local obstruction: neither canonical ancestry nor an arbitrarily long finite string of fast high-multiplier recovery events can be ruled out by a bound on each fixed label's multiplier or the length of such strings uniform over all finite supports.

## 5. Diagnostics and preservation

[Audit d8ea6c3](https://github.com/tara-sooo/A166944-Lean/blob/d8ea6c33795494c7a857066e916bda3bd29d6b25/research/min_direct_cut_clock_supply_audit.mjs), blob b660b335a3e4281dc2a4bb8e8a2703ba2bb40626. Exact remote readback. Run node research/min_direct_cut_clock_supply_audit.mjs 30000. Actual ECMAScript execution in the tool runtime:
- 20,160 abstract fixed-cut candidates, 11,379 valid and 8,781 invalid, compared against independently factored exact adaptive earliest-clock selection; 51,795 rival lag checks, 7,560 unit-wait equivalence tests, 2,160 saturated cases with 2h+1=s^2 or s^3.
- 336 exact CRT counts across 303,324 progression parameters, fixed rival sets through11; all passed. The initial diagnostic had represented forbidden odd-side residue as -1 instead of its normalized f-1 in one count; it failed, was corrected and all counts rerun. The theorem's signed residues are always taken modulo f.
- 14,998 odd canonical roots through30000, 243,497 actual events within180 event cap; 27,488 nonreset ordinary-decreasing events, 168,205 actual even-cut incidences, 254,636 rival exclusion incidences at those cuts. No false exclusions.
- Four canonical CRT controls reconstructed using a general residue chooser and literal BigInt GCD at every tick, with all adaptive eligibility tests. They are finite witnesses chosen by congruence search, not necessarily the larger recursively selected primes of the existence proof. New 98-digit root p79, word31/7/41/13, waits115/1/1/1/1, post ordinary deficits158/130/126/88/78, multipliers1/2/9/1/3. Prior 1634-digit p1279/7 control, waits1915/1, post multiplier182. Two new roots with the SAME fixed two-label word31/7: p13099 (16969-digit root), post recovery multipliers422/1869, and p18307 (23727-digit root), post multipliers590/2613. Across four controls 49,141 literal ticks and 40,781 stage/residue checks. Exact BigInt arithmetic for CRT and GCD; small abstract counts exact integers. All final assertions passed.

No new Fourier exponent. No historical novelty claim, Lean kernel verification, actual infinite ray or finite-twin contradiction. Main and sibling branches unchanged. The proposed direct local supply route has an explicit limitation at unit waits; next seek joint restrictions across many returns to a fixed cut (or constraints on their global density), rather than treating high multipliers as locally impossible. The large-A1 and B supply lower bounds from earlier work remain necessary but are not contradicted here.
