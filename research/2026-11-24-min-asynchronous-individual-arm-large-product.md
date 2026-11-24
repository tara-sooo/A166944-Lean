# Individual clock congruences remove the entire large-product short-lag residual

2026-11-24 JST. Continues 788861785ea298c6137f0405f1a5f98d7a21efdb on the same research/min-cycle-forest-2026-11-24 branch. Paper deductions using the previously established upper-bound sieve and exact finite audit; not Lean-checked. The full matching deficit and twin-prime conjecture remain open.

## 1. Stronger local input than the difference of the two arms

Use original canonical MIN roots, individual cutoffs, LOW7 L=210, B=ceil(sqrt(7X)), N=X/2, source-preserving projected-key absorption and a globally disjoint matching of stopped cohorts as in the preceding notes. At a first shared proposed projected key (p,C) the two event clocks satisfy n-n'=2jp. Here j can be nonzero (asynchronous). The two previous executed high keys have labels q,q', pre-horizons D,D', post-horizons C-g,C-g', clock times u,u', and heights b+2kq,b'+2k'q' respectively. The low gains g,g' are even in [0,L); b,b' are 0 or 6. The current event parity constant b0 is the same for the two clocks. Write the two hypothetical post-heights as b0+2Kp,b0+2K'p with K,K'>=0. This includes a proposed stop before execution.

Rather than retain only the difference of the height identities, apply the previous single-arm identity (6f843505423e8efe3bcc1c645b17b34daaddb9df) to each:
    2kq=(2K+1)p+e1,
    2k'q'=(2K'+1)p+e2,
    e1=b0-b-2(n-u)+g-1,
    e2=b0-b'-2(n'-u')+g'-1.
The LOW time bound and actual clock wait imply 0<n-u,n'-u'<=3L+2r(C), hence |e_i|<=7L+4r(C)+7; both errors are odd. Also K-K'=2j and
    2kq-2k'q'=4jp+e1-e2.
Crucially the individual congruences are stronger than this difference:
    2kq=e1 mod p,   2k'q'=e2 mod p.
When p>2 max(k,k') and k,k'>0, each previous prime is in one residue class mod p. These identities were already known separately; the improvement here is retaining an individual residue while counting the asynchronous pair. The shifted-quotient quadratic methods of the last two notes remain valid but are unnecessary for the following entire large-product class.

## 2. Theorem: all distinct-label large-product contacts with bounded prior indices and lag

Fix positive beta,gamma,delta,lambda with lambda>max(beta,gamma) and 3 beta+2 gamma+delta<1. Set
    H=log^beta B, z=ceil(log^gamma B), W=log^delta B, U=log^lambda B.
Consider first shared proposed keys with distinct p,q,q', previous high events on both arms, 0<=k,k'<=H, 1<=|j|<=H, r(C)<=z and
    pqq'>X U.
Assume only that each executed previous key has mass at most BW (a constant factor is harmless). This holds for the uniform cap T=B, and for the hybrid cap ceil(W max(B^eta,q)) with fixed eta<1, up to rounding. There is NO requirement that the earlier mass be proportional to its own label for this large-product estimate. There is NO condition on either offset, relative label ratios, or p squared compared with the parent labels. Nor is any lower power bound on q or q' assumed.

Since q,q'<=B and B^2 asymp X, large product implies p>=cU. For sufficiently large B this gives p>2H and p>2E, where E=7L+4z+7. The individual arm equations and nonnegative K,K' then force k,k'>0; a zero prior index would imply (2K+1)p<=E. They also imply p<=2H min(q,q')+E, and hence p<=4H min(q,q'). Put qmin=min(q,q'). Then
    X U < p q q' <=4 H qmin^2 B,
so qmin>=c sqrt(B U/H). In particular both prior labels exceed c sqrt B eventually. This lower bound is a deduction, not an extra hypothesis.

Fix p,k,k',j,e1,e2. Since p>2H and k>=1, the first individual congruence restricts q to one class mod p, and that class is nonzero since p!=q. The difference equation determines at most one q' for each q:
    q'=(2kq-4jp-e1+e2)/(2k').
Ignore integrality/primality/size of the determined q' for the initial candidate count. The possible primes q in [c sqrt B,B] in one residue class mod p have count
    O((1+B/p)/(1+log(B/p))).
This is the ordinary uniform dimension-one upper-bound sieve used in the earlier equal-offset note: for n=1+B/p, the parameter interval embeds in one of comparable length n; use level n^(1/4) and cutoff a sufficiently small fixed power of n. Every actual q>c sqrt B exceeds the cutoff eventually. Omit p; the sieve product changes by a bounded factor, and the standard remainder O(n^(1/4)) is absorbed by n/(1+log n). For bounded n use the trivial count. No assertion of equidistribution of primes for moduli comparable to B is needed. This bound is uniform in the residue class.

Now retain only the admissible triples of distinct primes satisfying the large-product inequality. Fix the two LOW gains and three divisibility signs (O_L(1) possibilities). At a contact C the three congruences are
    p divides C+sigma,
    q divides C+1+sigma_q-g,
    q' divides C+1+sigma_q'-g'.
Together with even C these give a single residue class modulo 2pqq'. The length of the canonical horizon window is O(X), and pqq'>XU with U tending to infinity. Thus there is at most ONE candidate horizon for sufficiently large B (O(1) would suffice). For that C both earlier projected keys are determined by q,q',g,g'. Because the global matching has degree one, at most the smaller whole prior mass, here bounded by BW, of actual pairs can be charged to these keys. We do not count clocks, physical states, or a separate current-key mass. This is precisely where the earlier loss from the CRT +1 term disappears: that term is retained and the missing saving comes from the individual congruence in the prime variable.

Sum the candidate count over all p:
    sum_{p<=B prime} (1+B/p)/(1+log(B/p))
         = O(B log log B/log B).
For p<=sqrt B use 1+log(B/p)>=0.5 log B and sum 1/p. For p>sqrt B partition into logarithmic bands i=floor(log(B/p)); each band has harmonic prime mass O(1/log B) by pi(t)=O(t/log t). Sum 1/(1+i) over i=0,...,O(log B). In both ranges 1+B/p<=2B/p. Multiply by O(H^3(1+z)^2) coefficient/offset tuples and by BW. Using B^2=O(X) proves
    V_large = O_L(X W H^3(1+z)^2 log log B/log B)=o(X).
With beta=gamma=delta=1/8, lambda=1/4 this is
    O(X log log B/log^(1/4) B).
For uniform cap B the factor W may be replaced by 1, giving exponent -3/8 with these H,z. The proof uses only the previous canonical identities and a one-dimensional upper-bound sieve, not the distribution of inverses or the two-variable quadratic. It handles both equal and unequal offsets, including the intermediate p^2 regime left unresolved in 788861785ea298c6137f0405f1a5f98d7a21efdb.

## 3. Combined all-product theorem for the bounded-index, bounded-lag cheap regime

Use the same exponents beta=gamma=delta=1/8 and lambda=1/4. Fix any 0<theta<1 and assume q,q'>=B^theta and normalized executed parent masses m(q,D)<=qW, m(q',D')<=q'W (automatic in hybrid cap when theta exceeds its fixed floor exponent). Consider all first projected asynchronous contacts with both previous high events, indices 0<=k,k'<=H, |j|<=H, r(C)<=z. Exclude the both-reset class for now.

- If q,q',p are distinct and both prior indices positive, the small-product theorem of 8a452377fcb0c47af4912aeb40eb4933aa988b81 covers pqq'<=XU with bound O(X(log log B)^3/log^(1/8) B), since 3beta+gamma+delta+lambda=7/8. Section 2 here covers its entire complementary product range with bound O(X log log B/log^(1/4) B).
- Same prior label q=q' at distinct preceding projected keys is covered by section3 of that note: O(X(log log B)^2/log^(1/2) B). Same current and previous label p=q or p=q' is impossible for q>=B^theta eventually by the LOW horizon divisibility relation (q would divide a nonzero odd integer of magnitude <L+3).
- Mixed reset/nonreset is impossible here by section4 of that note: a reset arm forces p=O_L(1+z), and the short lag difference forces the other prior height index times its polynomially large prime to be O_L(H(1+z)), impossible. This also explains why the large-product estimate does not need a prior positive-index assumption.

Consequently, with precisely these hypotheses, the entire non-double-reset asynchronous class (no product restriction) has
    V_bounded_async = O_(L,theta)(X(log log B)^3/log^(1/8) B)=o(X).
For same-clock first projected contacts the older two-parent low-block matching theorem applies under the corresponding positive-index conditions. Thus one can now remove the bounded-index, bounded-lag, cheap-current, normalized-large-parent NONRESET class across every product range, synchronous or asynchronous. The large-product calculation itself has the weaker whole-mass bound BW and needs no lower power bound on the previous labels.

This is not an estimate on all matched pairs. It does not bound the population with both-reset parents, initial low-only parents, small or disproportionately heavy previous labels in the small-product range, large prior indices, large lag, or costly current clocks. The actual stop-cohort matching deficit is still unproved.

## 4. Exact finite verification

Extended research/min_asynchronous_quotient_audit.mjs with the separate arm equations, hypothetical post-height indices (including proposed stop), K-K'=2j, two odd bounded errors, and their difference. For every large-product distinct-label pair satisfying the stronger finite coefficient separation p>max(2k,2k',|e1|,|e2|), enumerate all residues modulo p and check unique roots on both arms. Also check the number of even horizons in [2X,7X) in the CRT class, using the exact period 2pqq'. The finite diagnostic uses product>X rather than XU, so at most three horizons are observed rather than the eventual one. The earlier root-conservation, matching, literal gcd and quotient checks remain. Executed at X=256,1024,4096,16384,65536,262144 with uniform cap floor(B/4) and hybrid cap 4 max(ceil(sqrt B),p). Exact remote readback of research/min_asynchronous_individual_arm_audit.mjs and research/min_asynchronous_individual_arm_results.json at 211dc256f66729dc62bcd2cc5ab78befd805668a.

At X262144, uniform: 3170 asynchronous first contacts with both previous highs; all 3170 satisfy both individual identities, 685 large-product distinct-label contacts (29 equal offsets, 656 unequal), 301 both-positive prior indices, 221 bounded finite indices and |j|<=4, 2 satisfy the finite coefficient separation and both unique residues check out. Hybrid: 8029 both-prior-high asynchronous contacts, all identities checked; 1879 large-product distinct-label contacts (274 equal offsets, 1605 unequal), 742 both-positive, 775 bounded finite indices/lag, 26 satisfy finite coefficient separation and both unique-residue enumerations pass. Only 1 of those 26 also has both indices and lag <=4. These small overlaps reflect the deliberately conservative finite coefficient tests, not a proof of an asymptotic population bound.

Example X4096 hybrid, p53, q37, q'11, k3, k'1, j1, K2 and K'0, e1=-43, e2=-31, C13620, offsets -4 and -2:
    2*3*37=5*53-43=222,
    2*1*11=1*53-31=22.
The roots mod53 are respectively 37 and11, with unique solutions. Note q'<p and unequal offsets: no square-separation condition is needed for the identity. Another example X262144 uniform p11,q137,q'179,k5,k'1,j23,K62,K'16,e1=e2=-5; each unique residue is still valid, although j is large for the finite diagnostic. No inference that these finite tests prove the sieve estimate.

## 5. Next proof priority

The preceding work on large-product quotient correlations no longer needs a separate hard unequal-offset estimate in the bounded-index/lag class: retaining one arm's modular condition closes that particular gap. The main remaining obstruction is global, namely to control the source populations outside the local hypotheses (particularly long-lag and reset/small-label paths) or to construct a matching with a provable deficit without controlling each class separately. The finite data show that strict local bounds can select few actual witnesses, so do not treat this conditional-class closure as proximity to a complete twin-prime proof. No new branch, no main edits, no Lean compilation.
