# Prime-root-attached crossing stars and shallow-contact progression sieve

2026-11-25 JST. Continuation of ab7c533bc8fa2acf9ad87996a9b975039108fd55 on the user-selected prime-root branch. A one-sided cut attached to the larger prime root covers every first projected contact, including the previous unit-grid exceptions. Age-band budgets have no inverse-grid-spacing loss. A new progression-sieve bound controls the arithmetic support of landing slots at prime starts, and gives a negligible LINEAR deletion of exceptional roots carrying shallow large-label contacts. Actual unpaid star ranks and weighted slot cores are audited. These results restrict the remaining origin groups, not their unrestricted mass. Twin infinitude remains open; no Lean compilation.

## 1. A cut attached to the larger root

Keep dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u) original prime roots in [X,2X), T=floor(X/u^.25), H=T+B, F=T²Bu, m_g=u^4.75/ell^4. Original gain-stopped histories include their actual terminal vertex. Each selection p<=B increases the even projected horizon by p-1; total gain <H, actual wait <=2r<=3(p-1). All earlier retained high and actual directed medium ledgers remain frozen as appropriate. For an unordered pair write U_high=3H and U_med=C_med H/m_g with a sufficiently large absolute constant, the whole-pair bounds of ab7c533b. The medium bound is on the sum of both actual directions.

For any two distinct original roots M<M' sharing a projected horizon, let C* be their first common projected horizon on FULL original histories. Set C0=2M'-2 and x=C0-1. The older root starts strictly below x and reaches C*>=C0. It crosses x on a unique completed original edge A<=x<D=A+p-1. The younger root is not required to cross x; it starts at C0. Thus this cut is defined for EVERY pair including C*=C0, regardless of how short the younger prefix is. There is no assertion that both original paths cross x.

Define younger contact age a=(C*-C0)/2 and landing offset i=(D-C0)/2. They are integers with
    0<=i<=a, 2i<=p-2, D<=C*.
The latter offset bound uses D<=x+p-1. Since p|D or D+2,
    p | M'+i-1  or  p | M'+i.                        (1)
If D<C*, the younger source cannot visit D at all: D is an actual older vertex and would be an earlier common horizon. At root contact a=0, necessarily i=0 and p|M'-1, since p<=B<M' and p cannot divide M'. The older arrival tick is even (the p|D side), whereas the younger initial tick M'+2 is odd. Thus a root first projected contact is never already a physical synchronization. Every older root that visits C0 forms a first projected contact with M'; there is no earlier younger horizon.

At fixed younger M', the full reference list of older sources crossing x has one tag per source. Its exact projected landing slots are (i,p), at most two per p by the crossing arithmetic of 509a0e7. Retain only i<=S for a shallow age bound S. Unlike the absolute grids, this reference list need not be counted over all roots for the next rank budget: there is only ONE focal younger source at each cut. The actual older tag sets may still be large.

## 2. Summable one-sided rank budget, without a fine-grid factor

Partition a into bands j>=0: j=0 for a<=1, j>=1 for 2^(j-1)<a<=2^j. Write S_j=2^j, theta_j=(j+1)^(-2). At the younger source M', order its full older crossing list by decreasing source. Also form disjoint occupied landing cohorts (i,p) with i<=S_j, each in the same order. Let a_(M',j) count these occupied cohorts. This count uses all older paths, not just unpaid pairs.

Let L_high=B u^1.5 and L_med=m_g/u^.25, and m_j=floor(L_metric theta_j). Admit an older partner if it is among the first m_j of the full older crossing list, or among the first floor(m_j/a_(M',j)) of its eligible landing cohort. At most 2m_j older partners qualify for this one younger focal source at a fixed j; an empty cohort family contributes zero. This rank test pays the WHOLE unordered remaining pair weight for either metric, including both actual medium directions: it uses the whole-pair bound U_med, not a one-direction estimate. It does not require physical synchronization, a medium partner reassignment, or closeness in absolute source separation.

Summing over younger roots and bands gives an absolute deletion
    <=2 N U_metric L_metric sum_j theta_j
      = O(F/u^.25) high, O(NT/u^.25) medium.          (2)
In particular there is no H/d_j factor, no vanishing cap caused by a short grid spacing, and no need to exclude root contacts. For small age a<=S the arithmetic count a_(M',j) is also <=sum_{i<=S} d(M'+i-1,M'+i)=O((S+1)u/ell) by the product/factorial divisor bound on O(X)-size integers. Here d counts distinct admissible odd primes <=B in the two displayed integers. This upper bound together with a<=2pi(B) gives a uniform thin-partner criterion at each star; e.g. at j=0 the asymptotic high cap per occupied cohort is at least c B sqrt(u) ell, even for a=0. The bound concerns the older cohort only. It does not imply that all such cohorts are thin.

## 3. Arithmetic support of prime-root landing keys

For a fixed p and i in (1), possible prime M' lie in at most two residue classes modulo p. The zero residue has no prime M' in [X,2X) because p<=B<X. For a nonzero residue use the standard Brun–Titchmarsh upper bound for primes in an interval of length X and modulus p<X:
    # {prime M' in [X,2X): M'=r mod p}
       <= 2X/((p-1) log(X/p)) = O(N/p).
Uniformity follows from p<=B=O(sqrt X), log(X/p) comparable to u, and N comparable to X/u. The same bound follows from the usual upper sieve on the quotient interval. No prime distribution lower bound in progressions is needed. The only prime-counting inputs are this upper bound, the dyadic prime-count scale N and the elementary upper reciprocal-prime estimates already used in the branch. No new external literature search.

The landing keys (M',j,i,p), with contact age in band j, have per-p support at most
    O(N min(S_j+1,p)/p),                             (3)
because the possible offsets 0<=i<=S_j, 2i<=p-2 number O(min(S_j+1,p)). Counting these keys does not multiply by the number of later possible C*, times, incoming source tags, or future meetings. Each actual pair has exactly one such key.

Put Y=B exp(-sqrt(u)), rounded up with min5 if necessary. Eventually Y>B^.125. Define the fee
    h(p)=ell                    for p<B^.125,
         1                     for B^.125<=p<Y,
         1/sqrt(u)               for p>=Y.
The last band has sum_{Y<=p<=B}1/p=O(1/sqrt(u)) by Chebyshev's upper prime-count bound and partial summation (log Y=u-sqrt(u)); the middle range has bounded reciprocal sum, and the whole small range has reciprocal sum O(ell). Hence sum_p 1/(p h(p))=O(1). No asymptotic equality or independence of the two shifted residue conditions is used.

Give an actual slot key (M',j,i,p) capacity
    b_slot=U_metric L_metric theta_j/
                   (min(S_j+1,p) h(p)).
By (3) the sum over ALL relaxed arithmetic landing keys is O(N U_metric L_metric sum_j theta_j). Give a younger-root/age key (M',j) capacity b_band=U_metric L_metric theta_j; its sum has the same bound. These two families therefore have total O(F/u^.25) high or O(NT/u^.25) medium. In contrast to splitting evenly over the maximum possible number of divisors at every younger root, the slot budgets exploit the TOTAL prime-progression support. In particular for j=0 and p>=Y a slot can receive a capacity of order U_metric L_metric sqrt(u), larger than the individual whole-star average scale U_metric L_metric. This is possible because those labels occur at few prime starts. It is not a claim that an individual slot has bounded mass.

On fixed nonnegative unpaid pair weights, remove every remaining incident pair when its actual weighted degree at either type of key is positive and <=capacity. The simultaneous core theorem of ab7c533b applies, with costs bounded by the total capacities, independent of the earlier feasible flow outcome. Every surviving pair's younger-root/age group has >L_metric theta_j distinct actual positive-weight partners and its own exact landing slot has >L_metric theta_j/(min(S_j+1,p) h(p)) such partners. Counts follow from the uniform whole-pair bound. These are one-sided stars; no symmetric claim about the older endpoint's own crossing group is made. The old global/cut constraints can be included simultaneously, or restored by an additional bounded-cost pass, if their stopping conditions are required at the same time. The finite audit runs the new star after a reoptimized previous flow, so does NOT assume the old core conditions remain true for that support.

## 4. Rare shallow large-label younger roots: a linear deletion

Let S0=floor(u^.25), with min1. Define the exceptional set of ORIGINAL prime roots
    R = {M': there exist 0<=i<=S0 and Y<=p<=B prime,
         2i<=p-2, with p|(M'+i-1) or p|(M'+i)}.
By (3), or just the prime progression upper bound summed over offsets and the narrow large-prime band,
    |R| <= O(N (S0+1) sum_(Y<=p<=B) 1/p)
         = O(N/u^.25) = o(N).                        (4)
If a pair's younger contact age a<=S0 and older crossing selection p>=Y, then i<=a and (1) imply M' in R. Therefore discarding the entire original high incidence history of each M' in R has LINEAR proxy/actual cost <=O(|R| H)=o(NT), since each original root's total clock is <=3H and proxy r-sum <=1.5H. All high pair products involving such roots disappear in the actual retained ensemble. This is not an assertion that their removed quadratic energy is o(F).

For the high reduction, perform this extra linear deletion BEFORE the final physical density gate and other necessary retained-reference recomputations, or rerun the gate with its frozen natural reference on the remaining incidences. The previous relative error absorption must be applied to the resulting retained ensemble. The older high pair masks remain valid on arbitrary smaller retained sets. Then EVERY surviving high pair with younger age <=S0 has older crossing p<Y=B exp(-sqrt(u)), a subexponentially smaller scale than B. The result includes exact root first contacts with large older incoming p. This is a genuine structural arithmetic restriction, not a quota for a few observed pair keys.

For medium actual charges, the same rare-root estimate pays all remaining charges with FOCAL root in R, using that root's own total actual time. It does not justify deleting all medium charges of other focal roots just because their partner lies in R. In particular the one-sided statement 'younger root in R' cannot by itself remove the opposite focal direction. No such deletion is implemented in the finite medium ledger.

More generally a choice of large-prime threshold Y'=B exp(-v) with 1<=v=o(u) gives O(N (S+1)(v+1)/u) exceptional roots for age <=S, so the product (S+1)(v+1)=o(u) is sufficient. The stated choice v=sqrt(u) and S0=u^.25 provides one explicit example. This theorem does not control older crossing labels below Y; nor does it control the entire later high energy of shallow pairs whose younger roots are not exceptional.

## 5. Finite audit and exact accounting

Standalone research/min_prime_root_rootstar_audit.mjs, final source commit 24866511d202a58f845956a7a0c6f122d7d1e78d, blob 6520e382cbed2b590b1944970cf184ea364b13ee, exact remote readback.
    node research/min_prime_root_rootstar_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_prime_root_rootstar_audit.mjs --crt-stress --gain-stress --window-stress --reverse-stress --ancestry-stress --birth-stress --anchor-stress --multi-stress --precut-stress --grid-stress --star-stress 256 1024 4096 16384 65536 262144

Actual audit function executed in available ECMAScript runtime, not separate Node process. Initial 14 runs (analytic/concurrent at four X256..16384, then normal/combined stress/analytic at X65536/262144) passed. Final version adds independent enumeration of every shallow support key by prime progression and verifies all actual root-contact controls. All18 final runs (three configurations across six X) passed. Other modes not rerun. Previous assertions retained; binary search older crossing at younger-root cut; age/landing/progression, earlier-contact exclusion, full reference crossing lists, rank degrees, whole-pair budget arithmetic, exact shallow factor support vs independent progression enumeration, root-contact parity, weighted core oracle, payment conservation and reoptimized flow. Integer counts exact, fractional weights/flows use tolerances. The new rank/core use only unpaid fractions of the preceding reoptimized flow; subtract just those paid amounts from original remaining pair weights and reoptimize, so old payments are not counted again. The optional rare-root LINEAR deletion of section 4 is NOT applied to the finite residual; it is a theorem and an independent support diagnostic. A new density gate would be needed to incorporate it into the retained high hybrid proof. 

Finite analytic settings Y=ceil(B exp(-sqrt(u))), S0=floor(u^.25), ranks/caps as in sections2-3 with diagnostic U_med=H/m_g. Normal Y=ceil(B/8), S0=4, rank caps4 high/2 med at each band, base for slot/core H/8 high and .15 med, age and label fees as above. Combined stress Y=ceil(B/4), S0=8, rank16/8, base H/2 high and1 med. Analytic earlier residuals empty at tested scales, but prime support and root-contact controls nonempty. Finite exceptional-set proportions are large, not evidence of their asymptotic size; no numerical root deletion was made. The normal high ledger is still the isolated natural high diagnostic, not the full cumulative hybrid.

| X | previous normal high | root-star final high | previous/final normal medium |
|--:|--:|--:|--:|
|4096|0|0|0|
|16384|0|0|9.252348|
|65536|36480.761572|36480.761572|8.320120|
|262144|1349549.303339|1313263.837279|10.636373|

Largest normal X262144: 1083 positive unpaid pairs across both metrics, all assigned to older crossing at larger root (no root-contact pairs remain in this particular unpaid support). Younger age max639, older landing offset max330,18 pairs with age<=4, none of those had p>=finite Y. Full queried reference memberships5313,745 occupied slots,296 rank-degree checks. High rank pays36285.466060 across19 pairs; star core itself removes zero at these finite caps, leaves1032 high pairs,147 slot keys, final1313263.837279, async0. Medium rank and core remove zero,32 pairs remain, never6.298526033689. At smaller normal scales star residual unchanged. Combined stress largest already zero under prior multigrid core, remains zero up to floating rounding; not a new reduction. 
Independent ALL-root controls largest normal: 38580 actual projected root-contact pairs (958 with p>=finite Y), max98 older sources at one root horizon. Every such older arrival is even and p divides M'-1. Complete independent shallow prime progression enumeration agrees with factor scan on212867 candidate landing keys including40992 at i=0;53564 large-label keys,16617 distinct exceptional roots. Exceptional full original linear proxy13545409, actual clock11626597 in finite normal window, not subtracted. Largest analytic control:38853 actual root contacts,1417 large-label;71773 shallow support keys,18307 large-label,12541 exceptional roots. Largest stress:38580 actual root contacts,519 large-label,362686 shallow support keys,68212 large-label,17579 exceptional roots. No claim of finite small exceptional proportion.

## 6. Remaining task

The root-attached cut removes the geometric inability to assign very shallow or initial contacts. Its arithmetic slot cap and rare-support lemma leave an actual one-sided star obstruction for small/medium older crossing labels or longer younger contact ages. Future work should control large actual older source sets at such slots rather than only adding ranks. The short-age large-label exceptional deletion can be incorporated into the full retained high ensemble with the density gate reapplied, and the small-label residual studied using the actual reverse prefix. For the medium opposite focal direction the rare-root deletion is not automatically available. Joint medium o(NT) and high o(F) on a common unbounded dyadic sequence remain OPEN. Main and independent branches unchanged.
