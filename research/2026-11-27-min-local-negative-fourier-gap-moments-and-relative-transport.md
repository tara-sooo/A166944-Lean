# Negative MIN: unconditional Fourier gap-moment bound and relative transport entropy

2026-11-27 JST. Continuation of [f32926b](https://github.com/tara-sooo/A166944-Lean/commit/f32926ba7787001c55caf27d9c6830494002a051). User explicitly objected to stopping after a partial lemma or finite test. This continuation actually uses the prior exact pair correlation to prove an unconditional gap-moment estimate, then uses the estimate in the variable-cell signed transport inequality, then combines that with the time-weighted non-twin capacity to force a concentration lower bound under finite twins. The desired short-window variance estimate is not achieved; a separate deterministic dynamic upper bound is tested against that lower bound and fails to contradict it. No unconditional twin proof.

## 1. Fourier expansion of the exact CRT barrier correlation

Use the canonical coordinate k=b/6, period K=product_(5<=p<=z) p, local length l_p=(p-1)/2, B(k)=1 when -3k mod p is in [0,l_p-1] for every p. Density delta=prod l_p/p. Let g=B/delta, with normalized Fourier transform on Z/KZ. For a frequency with reduced denominator d|K, CRT factorizes the squared absolute Fourier coefficient into the local weights
    w_p(r) = |(1/l_p) sum_(j=0)^(l_p-1) exp(2pi i r j/p)|^2
for p|d, with r nonzero (multiplication by an invertible residue only permutes the local frequencies). Factors for p not dividing d are 1. This is the Fourier form of the preceding exact triangular correlation.

For r nonzero,
    w_p(r) = [sin(pi r l_p/p)/(l_p sin(pi r/p))]^2
             <= beta_p = 1/[(p-1)^2 sin^2(pi/(2p))].             (1)
To see the maximum, reduce to 1<=r<=p/2 using symmetry. For odd r the ratio of the two sine magnitudes is 1/[2 sin(pi r/(2p))]; for even r it is 1/[2 cos(pi r/(2p))]. The maximum is attained at r=1. In particular beta_p=4/pi^2+O(1/p).

Put D_z=prod_(5<=p<=z)(1+p beta_p). This is a real positive auxiliary product, not a spatial gap. The relative variance of the count in H consecutive canonical sites is exactly
    V_z(H)=sum_(nonzero frequencies a/K) |hat g(a)|^2 |D_H(a/K)|^2,
    D_H(t)=(1/H) sum_(j=0)^(H-1) exp(2pi i jt).
For each denominator d>1,
    sum_(a=1)^(d-1) |D_H(a/d)|^2
       = d r(1-r/d)/H^2 <= d/H,   r=H mod d.                   (2)
Indeed count the H summands in residue classes mod d and use Parseval; subtract the zero frequency. This holds for H both smaller and larger than d. Restricting to reduced numerators only decreases the sum. Combining (1),(2) and summing squarefree divisor subsets yields the unconditional bound
    V_z(H) <= (D_z-1)/H.                                        (3)
No local-uniformity or independence over short distances is assumed. The ordinary prime number theorem and sum_(p<=z)1/p=O(loglog z) give
    log D_z = log K - kappa pi(z) + O(loglog z),
    kappa = log(pi^2/4) > 0.                                   (4)
Thus (3) works for H far below the complete period by exp(c pi(z)) for c<kappa. However log D_z~z, not O(pi(z)); it does NOT prove the target V=O(1/log z) at H=delta^(-O(1)). A maximum-coefficient bound over all numerator residues loses the strong joint correlation of the local frequency indices. The gap between the scales is genuine in this upper estimate, not evidence that the desired bound is false.

## 2. Use (3) to prove unconditional size-biased gap moments

Let M be the number of canonical sites in the cell of a uniform canonical site in a full period. The previous exact void identity and Cauchy-Schwarz give
    Pr(M>2H)<=min(1,2 V_z(H)/(1+V_z(H))).
For real t>=4 choose H=floor(t/2)>=t/4. Then
    Pr(M>t)<=min(1,8 D_z/t).
For t<4 the same bound holds trivially. Set B0=8 D_z (different from the bounded window overlap constant of the earlier entropy notes). Integration of the survival function proves, unconditionally,
    E log M <= min(log K, log B0+1),                            (5)
    E M^s <= min(K^s, B0^s/(1-s)) for 0<s<1,                    (6)
    E M <= min(K, B0[1+log^+(K/B0)]).                            (7)
For (6), split the integral s int t^(s-1) Pr(M>t) dt at B0; for (7) use M<=K and integrate the 1/t bound only up to K. In particular
    H_z <= log K-kappa pi(z)+O(loglog z+1),
    log E M <= log D_z+O(log z+1).                              (8)
This is an actual asymptotic improvement of the uniform primorial baseline and supplies a first moment of the FULL size-biased cell size, not just the unweighted mean gap. It remains substantially weaker than H_z=O(pi(z)). No claim that this bound is the best available in the literature.

## 3. Apply the moment bound to actual MIN, not just the static partition

Use the synchronized windows and retirement of 5e932c4: N canonical roots A in [R,2R], T=ceil sqrt(2R+1), W=6 floor(T/6), each window observed from its latest birth n0 through n0+T. Total gain from each own birth <=3T+6. Let Y(A) be its actual retirement position. The following transport result also holds for any root-dependent observation with Y<=A and uniformly bounded gain, but the earlier time-coupling criterion is used below ONLY with synchronized windows.

Pad the canonical slab to include ALL full barrier cells intersecting [lo-3T-6,hi], where lo,hi are its canonical root endpoints. Add one stationary accounting ghost for each canonical site in this padded interval not belonging to the actual root slab. The ghosts are not active MIN states; they do not alter any trajectory. If M_j is the full canonical capacity of cell j, a_j actual initial mass, m_j^real actual terminal mass, put
    d_j=m_j^real-a_j=F(b_(j+1))-F(b_j),
    m_j=M_j+d_j=m_j^real+(M_j-a_j),
    N'=sum M_j=N+O(T+K), sum d_j=0.
Here F is the previous signed crossing flux, with actual roots only. The full period K bounds a cell's canonical capacity; padding accounts for this. Define probability distributions P_j=M_j/N', mu_j=m_j/N', and
    X=chi^2(mu||P)=(1/N') sum d_j^2/M_j.
The fine root endpoint entropy L_end is bounded by the real coarse entropy, itself at most (N'/N) L_pad, where L_pad=(1/N')sum m_j log m_j. This uses the monotonicity of f(m)=m log m on nonnegative integer masses; padding does not decrease the coarse sum.

Exact decomposition:
    L_pad = E_mu log M + KL(mu||P)
          = H0 + J + KL(mu||P),                                (9)
    H0=E_P log M, J=(1/N')sum d_j log M_j.
By Jensen applied to the likelihood ratio under mu,
    KL(mu||P) <= log(1+X).
Also |J|<=sqrt(X Var_P(log M)) by centered Cauchy-Schwarz. Alternatively, nonnegativity of KL relative to the tilted distribution P_j M_j^s / E_P M^s gives
    E_mu log M <= [KL(mu||P)+log E_P M^s]/s
for s>0. Hence
    L_end <= (N'/N) min{
       H0+J+log(1+X),
       H0+sqrt(X Var_P(log M))+log(1+X),
       (1/s)log E_P M^s+(1+1/s)log(1+X) }.                       (10)
This is a signed weighted flux inequality valid for variable cells, where the previous uniform-width Taylor cancellation could not be applied. It accounts for the preference of terminal masses toward larger or smaller cells through J; no assumption that the terminal cell sizes have the initial distribution.

For the padded interval of consecutive canonical sites, a nonnegative K-periodic function has empirical mean <=(1+K/N') times its exact complete-period mean (partition into complete periods and a remainder). Apply this to M^s. Taking s=1 in (10) and using the NEW unconditional moment estimate (7) gives
    L_end <= (N'/N) [log D_z+2 log(1+X)+O(log z+1)+log(1+K/N')].  (11)
If z=O(loglog R), then K=R^{o(1)}, N'/N=1+O(R^-1/2+K/R), and the bracket is O(log R) even using the trivial X<=O(R). Thus the multiplicative factor produces o(1) additive error. The static moment is eliminated from the dynamic problem by (11).

## 4. Force a quantitative dynamic concentration requirement under finite twins

Use the time-weighted penalty Q_R in 5e932c4 (not the cell width Q of older notes), with the SAME synchronized horizon. Under the finite-twins assumption all visited centers in sufficiently large slabs are non-twin. The existing weighted sieve capacity and entropy/time coupling imply
    L_end+Q_R >= 3 loglog R-O(1).                               (12)
Choose z=a loglog R with fixed a>0. Equations (4),(11),(12) force
    2 log(1+X)+Q_R >= (3-a-o(1)) loglog R.                      (13)
In particular if Q_R<=(1+o(1))loglog R on unbounded slabs and a<2, then finite twins force
    1+X >= (log R)^((2-a)/2-o(1)).                             (14)
Equivalently proving X<=log^(b+o(1))R and Q_R<= (1+o(1))loglog R with a+2b<2 on the same slabs would contradict finite twins. The earlier terminal/repeated small-label occupation estimate provides one way to control Q_R, but that estimate itself still needs a growing-scale bound on repeat occupation. This does not assert that Q_R<=loglog R has been proved.

One can apply (10),(11) at every synchronized observation u (with the same padded interval); under finite twins the soft support inequality forces H(A|X_u)+E c_R(X_u)>=3loglog R-O(1) for every u. Thus averaging in u also gives (13) with log(1+X) replaced by the mean of log(1+X_u), and Q_R replaced by the mean actual cost (Q_R+O(1) by the existing waiting coupling). This permits bounding transport at intermediate times, not only at the end; no implication from an asynchronous cut to a synchronous endpoint is used.

## 5. Try to close the concentration bound; explicit failure of the purely deterministic estimate

Let eta be the fraction of actual roots whose terminal cell differs from its initial cell. The actual map is monotone in time for each root, so sum d_+=sum d_-<=N eta, and d_-<=M_j. Since A-Y<=Gmax=3T+6 and each root has spacing 6, any roots arriving in cell j from outside its initial interval have A in the interval immediately to its right of length at most Gmax. Thus d_+<=ceil(Gmax/6)+1. If Mmin=min M_j, this gives the unconditional deterministic inequality
    X <= (N/N') eta [1+(ceil(Gmax/6)+1)/Mmin].                  (15)
The previous rough-difference theorem additionally gives Mmin>(z^2-1)/6 under finite twins once z exceeds all twin primes. Thus (15) improves the deterministic estimate to O(eta sqrt R/z^2) under that assumption, but at z=a loglog R it is still far larger than the required polylogarithmic scale in (14). Even the trivial eta<=1 cannot close the contradiction. This is an explicit failed attempt to finish the proof with static barrier geometry plus monotone displacement alone; replacing endpoint entropy with X has not removed the central dynamic concentration problem. A bound counting actual arithmetic trajectories, not merely their monotone displacement or total number of boundary crossings, is required. The previous direct-arithmetic branch's modular-hyperbola estimate 14c6176 counts unweighted first-pair supplies on positive MIN, not inherited mass on the negative ensemble; transferring it as a bound on X without controlling source masses would be invalid. No such transfer is used.

## 6. Audit and limitations

[Final audit 2dfdfba](https://github.com/tara-sooo/A166944-Lean/blob/2dfdfba8d576e3d8b5c97e7eb81cf89a3220ac26/research/min_local_negative_fourier_transport_audit.mjs), blob f8df9abb7a3be913fef083a8acc7183680c09bc3, exact remote readback and ECMAScript reexecution. Run node research/min_local_negative_fourier_transport_audit.mjs. Earlier commits 9993cb2 and 5c27617 contain elapsed-T variants and are superseded by the synchronized version for the time-coupling application. The tail integration uses conservative integer-window constant 8 (not the earlier experimental 4). Local Fourier maxima for primes through 53, complete small-period direct Fourier vs triangular pair sums through z17, exact finite gap moments through z23, actual synchronized MIN R480000 N80001, 1866425 root events, 57591 counted structural checks plus the separately asserted per-root synchronized time/gain checks. Same factor clock as earlier audit; no independent mathematical reviewer, Lean kernel or standalone Node process. Floating-point tests are diagnostics, not rigorous interval certification of the analytic inequalities.

At z53, K=5431526412865007455, D_z approximately 5.307372089568434e14, numerical unconditional log-gap bound (5) 36.98473 vs log K43.13875. The previous numerical short-window correlation evaluation gave a much smaller bound16.06330; this new bound is weaker numerically but proved for all cutoffs. It does not establish the desired O(pi(z)).
Actual synchronized R480000 fine L_end3.65899562; terminal fraction .68702975, Q_R=.96197215, actual penalty1.07266001.
    z       H0         X          J          actual coarse     (10), s=1    (10), signed J
    5       .936426    22.179392  .017897     3.679258         7.286758      4.122889
    7       2.119732   9.295304   .016551     3.811837         7.120468      4.495559
    11      2.821020   4.353372  -.030894     3.929089         6.408373      4.495999
    13      3.538975   1.827720  -.004986     4.173700         5.786622      4.602673
    17      4.382311   .774185    .006139     4.692873         5.746986      4.993484
    19      5.167080   .352529   -.006076     5.300254         5.995959      5.507093
Here s=1 uses the exact finite E_P M, not the looser universal Fourier upper estimate. The signed J bound is much tighter in these finite controls. No asymptotic inference from these values. The earlier time-weighted occupation, age-frontier, signed uniform flux and reverse-flow methods remain available. The missing actual weighted flux estimate and complete proof are OPEN. No Lean changes or main/sibling modifications.