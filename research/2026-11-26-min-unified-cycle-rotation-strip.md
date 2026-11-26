# Integration XXXVII: rotation-strip four-condition sieve and short rational resonance alternative

2026-11-26 JST. Parent 14f18204b4e23643529cd1d529a3d1b0c6e2eee0. Direct preflight unchanged [14c6176](https://github.com/tara-sooo/A166944-Lean/blob/14c6176473bd6b30599d06a02e49cc2679c227ae/research/2026-11-26-min-direct-modular-hyperbola-three-root-source-sieve.md). New: avoid the fixed-shift CRT length restriction of XXXVI for distinct source primes by summing the near-fourfold shift inside a two-cofactor strip. An elementary rational-approximation block count gives a four-condition upper sieve on the NONRESONANT part at L>=Y^(1+epsilon), even L<<Y². The remaining possible near-saturation mechanism at top scale is localized to actual short rational relations between source primes and corresponding cofactors. We do not eliminate these relations.

## 1. Setup and exact strip

Use XXXVI's original tag-bins of length L<=H, actual ordered nonoverlapping up/down direct pairs, endpoint labels in [Y,KY], Y->infinity, <=B, K fixed. Let M be actual direct matched height mass, G_all<=NH, n number of pairs, Delta=G_all-4M/3+4n/3>=0. For consecutive retained pairs in a bin, p is starting upward-source prime and q the next upward-source prime, d their actual prehorizon difference. Their starting matched weight <=3KY+1. The exact XXXVI ledger gives sum |d-4p|<=6Delta+4n, and last-pair weight O(NHY/L). No low-relay or fast-target condition.

Fix distinct p,q and sides e,f in {-1,1}, source prehorizon C=p a+e in [C_*,C_*+L), next source C+d=q b+f. Here a,b are integer cofactors, not labels. For |d-4p|<=tau Y with 0<tau<=1/4, count the strip
    a in integer interval I, |I|=U_p=L/p+O(1),
    4p-tau Y+e-f <= q b-p a <= 4p+tau Y+e-f.
We may ignore the ending-bin restriction and parity, since this is an upper bound. The b interval for a fixed a has length w=2tau Y/q<=1/2. Every actual candidate fixes C and the actual next retained source, and at most one pair occurs on that tag at that C. Both endpoints upward, so at primes l>3, l<Y and 4l<min(p,q)-1, the four exclusions are
    a!=0, pa+2e!=0, b!=0, qb+2f!=0 mod l.
The two forbidden residues per coordinate are DISTINCT, including if a cofactor is composite. Hence EXACT forbidden density on F_l² is rho(l)=4l-4, g(l)=4/l-4/l²; no singular factor for these two-dimensional residue conditions. This differs from fixing d and then counting one progression mod pq. The strip itself still needs a residue distribution estimate; the density alone is not enough.

## 2. Uniform residue count via rational approximation

Assume L>=Y^(1+epsilon), fixed epsilon>0. Fix 0<kappa<min(epsilon/3,1/8), put U=L/Y and R=floor(U/Y^kappa), eventually R>=1. Call an ordered distinct label pair RESONANT if there exist integers 1<=h<Y^kappa and A with
    |hp-Aq|<=q/R.
Because p/q is in [1/K,K], A=O_K(h+1), and for large Y it is positive. Otherwise call the pair nonresonant. Dirichlet approximation (pigeonhole on fractional parts of j p/q for j=0..R) gives coprime A,h, 1<=h<=R, |p/q-A/h|<=1/(h R). Reduction of a nonprimitive fraction preserves the inequality. On a nonresonant pair h>=Y^kappa.

For any positive integer modulus k and any residue pair a0,b0 mod k, substitute a=a0+k x, b=b0+k y. The allowed consecutive x interval has length U_p/k+O(1), and y-(p/q)x lies in a translated interval of length w/k<=1/2. Thus the number is a rotation count on the circle by theta=p/q. Endpoints may be included; this changes the block discrepancy bound only by a constant. Split the x interval into blocks of h consecutive integers plus remainder of length <h. In each full block, after translating its initial point, replace theta by A/h. The h equally spaced rational points are perturbed by at most 1/R<=1/h; a circle arc of length w/k contains h w/k+O(1) points, with an absolute error independent of k, translation and initial block. (Only O(1) points lie within 1/h of either endpoint.) The remainder costs at most O(h). Therefore
    #strip at (a0,b0) mod k
       = U_p w/k² + O(U_p/(k h)+h+1).                  (1)
Rounding the x interval count costs O(1). For a NONRESONANT pair this is
    = U_p w/k² + O_K(U Y^(-kappa)),
uniformly in k and residues, since h>=Y^kappa, h<=R<=U/Y^kappa and U>=Y^epsilon. No Fourier or Kloosterman bound is needed for this part; the result uses the length in a alone and sums over all allowed shifts in the strip. It applies to an arbitrarily translated actual bin. For a resonant pair do not use the last power-saving conclusion.

## 3. Nonresonant four-condition Selberg capacity

On the strip with p,q fixed nonresonant, apply the same Selberg diagonalization as direct 14c6176, now with local rho(l)=4l-4. For squarefree k supported on primes 3<l<=z, CRT gives rho(k)=product rho(l) forbidden residue pairs where each l has at least one of the four exclusions violated. Equation (1) gives
    sum A_k = N0 g(k)+O_K(rho(k) U Y^(-kappa)),
    N0=U_p w=O_K(tau U), g(k)=rho(k)/k².
Multiplicativity and A_k A_j=A_lcm(k,j) hold. Choose z=floor(Y^(kappa/16)). All sieve primes eligible and less than p,q. Explicit Selberg weights on squarefree k<=z satisfy lambda_1=1 and |lambda_k|<=prod_(l|k)(1-g(l))^-1<=k, since (1-g(l))^-1=(1-2/l)^-2<=l for l>=5. Quadratic error amplification <=z^8 as in direct, because rho(lcm)<=lcm² and sum_(k<=z)k³=O(z⁴). Thus error O_K(U Y^(-kappa/2)). Main form 1/G(z) with G(z)>>log^4 z by the existing Euler-product/Markov proof: g(l)=4/l+O(l^-2), product over small primes ~log^4, choose smaller power cutoff so expected log squarefree divisor <=log z/2, retain at least half. This verifies the required dimension four rather than assuming independence of actual source occurrences.

For tau>=c/log^D Y with fixed c,D>0 (or any fixed positive tau<=1/4), error is absorbed. Necessary surviving strip candidates <=C_(epsilon,kappa,K) tau U/log^4Y, for large Y (threshold may depend on c,D, constant can be uniform). Weighted by <=3KY+1 and sum sides:
    F_near,nonres(p,q) << tau L/log^4Y.                (2)
Sum actual ordered nonresonant pairs from source support of size s_j: <=C tau L s_j²/log^4Y. No singular factor and no L>=Y² requirement. Count is upper only. It is valid when R exceeds p or q, too: exact rational approximation h=q is allowed and then distinct primes cannot resonate with h<Y^kappa. The fixed-shift same-label case p=q still uses XXXVI's one-progression bound << L s_j (loglog(3Y))^12/log^4Y; its required cofactor length L/p>=cY^epsilon holds here. For L>=C Y^(2+kappa) with sufficiently large fixed C the resonance inequality forces hp-Aq=0, impossible for distinct p,q with h<Y^kappa. At shorter lengths the resonant part is real and must be counted separately.

## 4. Quantitative alternative to saturation at ALL label scales

Assume M>=rho NH, aggregate source support sum s_j<=C0 (NH/L)log²Y, L>=Y^(1+epsilon). This includes top labels Y~sqrt X at L=X^.7 or L~H with suitable epsilon. As in XXXVI discard bins s_j>C1 log²Y at arbitrary small fixed loss using M_j=O_K(L+Y) and Markov. Last-pair weight o(NH); same-label near weight o(NH). Fix arbitrary tolerance xi>0, take C1 large so high-support discarded weight <=xi NH, then fixed tau<=1/4 sufficiently small so (2) summed over retained bins <=xi NH. The far-gap weight <=O_K((Delta+n)/tau). Therefore, for a saturation sequence Delta=o(NH), all but arbitrarily small fixed tolerance of M must be on RESONANT distinct consecutive source transitions with near-fourfold gap; equivalently total weight on resonant distinct consecutive source transitions (not restricted by tau or support-bin discard) is M-o(NH). Since xi arbitrary, this is an ordinary little-o conclusion for fixed kappa and epsilon. For each fixed tau>0 the gap tail is o(NH) independently. The resonant transition set itself depends on kappa and L. No claim of a single uniform kappa tending to zero.

More quantitatively if, along the same hypotheses, weight on resonant distinct source transitions is <=M-rho1 NH, fixed rho1>0, choose tolerance small relative to rho1 and fixed tau small as above. The remainder forces far weight >=c rho1 NH; hence
    G_all-4M/3 >= c' NH, M <=3G_all/4-c'' NH.
So the previous constant-gap theorem now holds at pair-CRT-short scales PROVIDED a macroscopic part of the mass is not on short rational resonances. No low-relay or target-support condition. The exception is necessary in this proof: if p/q lies very close to a small rational, the lattice strip can cluster in residue classes and (1) does not give power saving. Merely assuming distinct primes does not remove it. We have not shown a positive fraction of nonresonant transitions from near-minimal support alone.

## 5. Actual cofactor line structure of the exceptional population

For a resonant pair choose any reduced certificate h,A as above, put ell=hp-Aq (nonzero since p,q distinct and h<Y^kappa<q). Every actual strip candidate satisfies the EXACT integer identity for c=h b-A a:
    q c = ell a + h(d+e-f).
Therefore c lies in an interval of length <= |ell| U_p/q +2h tau Y/q+O(1) <<_K Y^kappa, since |ell|<=q/R, U_p=O(U), R~U/Y^kappa. Thus the whole actual local near-gap strip is contained in O(Y^kappa) parallel integer lines h b-A a=c, not a collection of unrelated residues. Their integer points have direction (h,A); parameter length <=1+U_p/h. On each line the four roughness forms become four affine forms in the single parameter. For primes not dividing p q h A, within-coordinate roots distinct; cross-coordinate collision determinants, up to sign, are
    c, q c+2fh, p c-2e A, pq c+2f h p-2e A q.
The latter three are nonzero for distinct large p,q and h,A=O(Y^kappa): if zero then respectively q|2h, p|2A, or p|2Aq, impossible. The c=0 line is a genuine three-root possibility (a,b proportional). These are algebraic identities; no singular-factor sum on these lines is asserted here. Line counting and the treatment of c=0 are next steps. No assumption that the actual starting cofactor a is prime.

At the near-top Y~sqrt X and L~H~X/(log X)^.25, |ell|=O(Y^kappa(log X)^.25), and absolute |c|<<_K X/(Y R)+h=O(Y^kappa(log X)^.25). Thus near saturation with sparse source support forces almost all such transitions to have BOTH labels and cofactors obeying the same small-coefficient rational approximation, with polynomially small relative error, for every fixed admissible kappa. At L=X^.7 the bound on |ell| is larger, O(Y² Y^kappa/L), and absolute c can be larger; the local line count remains O(Y^kappa). These are explicit necessary conditions, not an impossibility statement. In particular a pair of nearby primes can have h=A=1. No bound on their total actual weighted supply follows from this alone.

## 6. Finite diagnostics

Run node research/min_unified_cycle_rotation_strip_audit.mjs 4096 16384 65536. Extend XXXVI six actual prime-root runs and 48 controls, near cutoff floor(Y/4). Verify actual cycle and saturation ledger, actual distinct-pair strip membership, exact cofactor relation, line spread, actual roughness exclusions; enumerate integer strip points and residue counts at moduli 1,5,7,35, verify explicit generous discrepancy bound 12(U_p/(k h)+h+1), and finite resonance/nonresonance partition. Independent translated-strip controls use distinct fixed primes, varying lengths/offsets/sides, plus exact density for all nonzero slopes mod six small primes. Finite R,h0 chosen for diagnostics, not claimed to reproduce asymptotic exponent regime; no numerical certification of analytic Selberg error, full core/kernel rerun or Lean. 
```json
{
  "totals": {
    "controls": 48,
    "pairs": 29671,
    "M": 726042,
    "gapChecks": 6968,
    "nearMass": 8544,
    "farMass": 121604,
    "sameMass": 412,
    "distinctMass": 8132,
    "rotationGroups": 222,
    "rotationChecks": 288600,
    "rotationPoints": 7551,
    "rotationActual": 222,
    "resonantGroups": 14,
    "nonresonantGroups": 208,
    "resonantMass": 2156,
    "nonresonantMass": 5976,
    "cofactorRelations": 222,
    "rotationRough": 574,
    "maxRatio": 0.06501582994120306
  },
  "independent": {
    "density": 3504,
    "controls": 384,
    "checks": 499200,
    "points": 40729,
    "resonant": 126,
    "nonresonant": 258,
    "maxRatio": 0.04708215888923687
  }
}
```
Main/direct unchanged. Next: sieve the exceptional rational lines, in particular c=0 and small denominators, or connect the macro direct near-saturation premise to the original overlap ledger. No final NT overlap loss.
