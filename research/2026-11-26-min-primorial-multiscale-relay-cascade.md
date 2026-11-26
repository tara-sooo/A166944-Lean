# Mixed-scale descent pairs and a relay cascade without double charging

2026-11-26 JST. Continuation of 3a3ad8e32c591027e373f91fd6f6cf665ab885fd, research/2026-11-26-min-primorial-ordered-descent-pair-sieve.md. New paper deductions and executed finite arithmetic audit. No Lean verification, external novelty claim, or proof of twin infinitude.

## 1. A single ordered population across scales

Consider one envelope-valid uncut offset MIN segment with pre-offsets in [X,A0 X] for fixed A0>1. All events strictly increase offset by g=p-1. A descending event has w>=p; all odd prime factors of both neighbors are >=p/2 and p<=2 sqrt(A0 X+1), by the earlier descent lemma.

Mark any subset of descending events whose labels are >=8, and enumerate their labels p_1,...,p_n in chronological order (not sorted). Pair consecutive marked events, regardless of relative label size. Let E_i denote total physical gain of the strictly intervening events; thus E_i is even and nonnegative. Define

    G_M=sum_i (p_i-1),
    W=sum_(i<n) min(p_i-1,p_(i+1)-1),
    R=sum_(i<n) E_i,
    V=sum_(i<n) |p_(i+1)-p_i|.

The relay interiors are disjoint. R counts each intervening nonmarked event exactly once. For n>=1 we have the exact identity

    2W=2G_M-(p_1+p_n-2)-V.                         (1)

For n=0 all four sums are zero and no endpoint term is used. This is the sum of 2 min(a,b)=a+b-|a-b|. In particular when marked gain is macroscopic but W is small, label variation must be large. No hypothesis about comparable labels or event count is used.

For a pair with source p, target r, write offsets x=pq+e, y=rs+f, e,f in {-1,1}. Put D=p+E-1, so y=x+D. If p=r then E>=p-1 by the repeat-toll congruence from the previous note. Let m=min(p,r), M=max(p,r). With a common cutoff 0<beta<=1/2 call the pair short if E<=beta m. Short pairs necessarily have p!=r. Long pairs have weight m-1<=E/beta, so total long-pair weight <=R/beta. This adaptive cutoff is essential: it incurs no max/min scale-ratio loss and no counting a relay twice.

## 2. A CRT pair bound valid for unequal scales

Fix p,r,e,f,E for a short pair. The source x is in one class modulo 2pr. The interval parameter length is O_(A0)(N), N=max(1,X/(pr)). Since p,r<=2 sqrt(A0 X+1), N is comparable (with fixed A0 constants) to X/(pr) for sufficiently large X. For each odd prime 5<ell<m/2, all four integers x+-1,y+-1 avoid zero modulo ell. The progression step is invertible modulo ell; the four forbidden residues in x are +/-1,-D+/-1. Their distinct count is

    4-nu_ell, nu_ell=2*1_(ell|D)+1_(ell|D-2)+1_(ell|D+2).

The singular factor S(p,E)=product_(ell>5)(1-1/ell)^(-nu_ell) is exactly the same as in the previous note. No comparable-label assumption was used in these congruences. Since E<=m/2<=p/2, D(D-2)(D+2)=O(p^3). The pointwise and interval-average estimates there hold uniformly with p in place of T:

    S(p,E)<< (log log(3p))^2,
    sum_(0<=E<=B, E even) S(p,E) << B+1+(log log(3p))^4

for 0<=B<=p/2. In the average proof take primes <=log(3p) in the product expansion; the discarded larger prime factors cost an absolute bounded factor.

Set H(p,r)=min(log(2m),log(2+N)). The one-dimensional Selberg sieve on this progression gives the fixed-tuple count

    O_(A0)(N min(1,S(p,E)/H(p,r)^4)).               (2)

Indeed choose z=floor(min(m^(1/64),N^(1/12))) when this cutoff is large, and the trivial count otherwise. The local density is (4-nu_ell)/ell. The squarefree residue counts are length*g(d)+O(rho(d)), rho(d)<=d. The explicit Selberg diagonalization and weights |lambda_d|<=d in the earlier papers give error O(z^6)<=O(sqrt(N)), and the truncated Euler product gives a reciprocal main quadratic form >>H^4/S(p,E), using 1-g(ell)<=(1-1/ell)^(4-nu_ell). The error is absorbed into N/H^4 for large N; bounded cutoffs are handled by changing constants. This proof does not need a modular hyperbola in the unequal-scale case.

Let P be the set of distinct marked labels. Each fixed source offset occurs only once on the segment, so summing (2) counts actual consecutive marked pairs. Multiplying by m-1 and summing signs and E up to floor(beta m) gives

    W <= C_A0 X (beta K + E0) + R/beta,             (3)
    K = sum_(p,r in P,p!=r) (m/M)/H(p,r)^4,
    E0 = sum_(p,r in P,p!=r) (1+(log log(3p))^4)/(M H(p,r)^4).

Here p is the chronological source label, so the sum is over ordered pairs. A subset of actual transition types could replace P x P in these sums. Formula (3) holds at all scales; near the square-root scale H can be bounded and no spurious log^4 saving is asserted. Independently the bare CRT bound gives the same structure with H^4 replaced by 1 and E0=sum 1/M (without singular factors). The relay part in (3) is charged once, not once per label band.

## 3. Sparse bands: sum the scale kernel

For the remainder assume all marked p<=X^(1/2-epsilon) for fixed 0<epsilon<1/2. Use disjoint dyadic bands [T_j,2T_j), T_j powers of 2, and let J denote the number of occupied bands, T_* their minimum lower endpoint, T_max their maximum. Assume their distinct-label counts satisfy

    S_j <= C0 (log T_j)^2

with fixed C0, and T_* tends to infinity. The bands need not be adjacent. H(p,r)>>_epsilon log m, since N>=X^(2epsilon). For two bands with dyadic indices i,j, distance d=|i-j|, the factor m/M is O(2^(-d)); the ratio of their log sizes is O(1+d) (T_*>=8). Hence their contribution to K is

    O_(epsilon,C0)(2^(-d)(1+d)^2).

For each occupied i, summing this over j is bounded by the convergent geometric series, even if all dyadic indices are present. Thus K=O_(epsilon,C0)(J), not O(J^2). For E0 write 1/M=(m/M)/m. For the same two bands, log log(3p)<=log log(3m)+O(1+d). The function eta(t)=(1+(log log(3t))^4)/t is decreasing for sufficiently large t, and 1/m<=1/T_*. The analogous band-pair contribution is O(eta(T_*) 2^(-d)(1+d)^6). Therefore E0=O(J eta(T_*)). Formula (3) gives the disjoint mixed-scale bound

    W/X <= C (beta J + J eta(T_*)) + (R/X)/beta.     (4)

All constants depend only on A0,epsilon,C0, not on the band positions or their count J. Optimizing beta (clipped at 1/2), and using R/X<=O_A0(1), gives

    W/X <= C' (J eta(T_*)+sqrt(J R/X)).             (5)

For R=0, send beta to zero in (4); the residual term remains. For R>0 choose beta=min(1/2,sqrt(R/(J X))); if clipped, J and R/X are comparable up to fixed constants in the bound. This is an actual constraint on mixed-scale ordered events, not an estimate for a sum of separate possibly overlapping band relays.

## 4. Relay cascade: remove bands from smallest upward

Order occupied bands by increasing T_1<...<T_J. Let G_j be physical gain of marked descents in band j. Let R_0 be the total physical gain of ALL nonmarked events in the segment (or, more sharply, only the nonmarked gain between the first and last original mark). For each j consider the suffix population of marks from bands j,...,J, keeping their original chronological order. Apply (1)-(5) to that population, denoting its weights and disjoint relay gain by W_j,R_j. This is a separate inequality for each suffix; we never sum the relay gains across suffixes.

Every new relay in a suffix lies inside the original first-to-last span. It consists only of original nonmarked events or removed lower-band marks, so

    R_j <= R_0+sum_(i<j) G_i.                       (6)

If n_j marks have label in band j, every suffix mark has gain at least T_j-1. Thus W_j>=(n_j-1)(T_j-1) and G_j<=(2T_j-1)n_j. In particular for T_j>=3,

    G_j<=3 W_j+2T_j.                               (7)

This lower bound is valid even if high labels alternate with low ones in the suffix. Use the worst global J,T_*,T_max in (5). With f_j=G_j/X, r0=R_0/X, s_j=r0+sum_(i<=j)f_i, we get

    f_j <= C (J eta(T_*) + sqrt(J s_(j-1)) + T_max/X).           (8)

This is the scale-cascade inequality. It replaces a false sum of independent per-band relay lower bounds with a sequential budget: a higher band can use lower-band marks as relay, but those marks have already been bounded at previous stages.

For an explicit iteration write a=r0+J eta(T_*)+T_max/X. Since the physical total on the segment is O_A0(X), all s_j=O_A0(1). In the nontrivial regime a<=1, let y_j=s_j+a. From (8),

    y_j <= C1 sqrt(J y_(j-1)), y_0<=2a.

Here s_(j-1)<=O(sqrt(y_(j-1))) and a<=sqrt(y_(j-1)) justify absorbing the additive terms. Iteration for j=J gives

    sum_j G_j/X <= y_J <= C2 J (2a)^(2^(-J)).       (9)

The constants are independent of J because the sum of the geometric exponents is less than 2. If (2a)>1 the bound can simply be replaced by the trivial O_A0(1).

Two consequences:
- If the number J of occupied sparse sub-square-root bands is bounded, T_*->infinity and R_0=o(X), then all marked gain is o(X). In particular these bands cannot together produce macroscopic lag loss, since every descending loss <=p+1<=2(p-1). This does not assume a single dominant band or any bound on the total event count.
- If T_*->infinity, R_0/X=O(T_*^(-c)) for some fixed c>0, and J<=(1-delta)log_2 log T_* for fixed 0<delta<1, then a<=T_*^(-c') for some c'>0 eventually: J eta(T_*)=T_*^(-1+o(1)), and T_max/X<=X^(-1/2-epsilon)<=T_*^(-1). Hence J(2a)^(2^(-J))->0, since 2^(-J) log T_* >=(log T_*)^delta. Again the marked gain is o(X). Equivalently, a macroscopic marked population with those sparsity and polynomial relay-scarcity hypotheses needs more than (1-delta)log_2 log T_* occupied bands for every fixed delta>0.

The result still permits general paths with many occupied scales, dense bands, large nonmarked gain, or near-square-root labels. A false double would require a macroscopic lag decrease, but no theorem here proves that its ancestry is confined to a sparse sub-square-root family or that nonmarked gain is scarce. In particular a large R_0 consisting of other genuine events cannot simply be discarded. No upper bound on G(r) follows without additional control. This is a conditional exclusion of the sparse few-scale alternative, not a proof of twin infinitude.

## 5. Executed finite audit

Source research/min_primorial_multiscale_relay_audit.py at 3def80133bdcdc0b3a7ec313bd5b0ac7cc61ea06, remote blob 3c49cc7d0f2b342bc470e0b1b6ae892fa7f2bfe4 equals the locally executed blob (git hash-object). Run with SymPy and the sibling record-supply audit:

    python research/min_primorial_multiscale_relay_audit.py 100000

On all 16666 arbitrary integer resets r=7,13,...,99997, stopping before their first label >r, 317671 pre-record events. Mark descending labels >=8, testing the union of all occupied dyadic bands and each of the two alternate-band subunions separately; evaluate every occupied suffix in each population. These populations overlap, so counts are not independent samples or counts of unique events.

- 46172 suffix populations; 53825 consecutive marked pairs.
- 35270 pairs cross dyadic bands; 14118 have label ratio >=4.
- 4045 repeated-label pairs, all with E>=p-1.
- 25343 adaptive-short-pair checks (beta=1/2,1/8,1/32); no repeated labels among short pairs.
- 43623 four-neighbor roughness and residue-density checks at eligible small primes.
- 138516 long-relay budget checks over the three cutoffs, all passed.
- Every suffix passed (1), the disjoint relay sum identity, (6) with R_0 the total nonmarked gain, and (7). The mixed-scale CRT representative matched each short pair tested at beta=1/2.

These checks validate finite arithmetic/accounting, not the asymptotic sieve or sparsity hypotheses. The audit does not infer a uniform bound on band count, support, nonmarked gain, or reset displacement.

## 6. Next target

A genuine next step is to control the other alternatives in (9) by canonical ancestry: either establish a sparse-band/relay budget for the first-record path, or prove an independent constraint on dense and near-square-root descent supply. The weighted identity (1) makes rapid label variation explicit and may support a cross-scale transition sieve. The new cascade requires only disjoint physical gain and works with arbitrarily separated band locations, but is not by itself an unconditional displacement upper bound.
