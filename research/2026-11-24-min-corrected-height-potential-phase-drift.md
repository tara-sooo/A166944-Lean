# Corrected-height potential: cancellation of every LOW step and a smaller high-clock drift coefficient

2026-11-24 JST. Continues 9d153612d0c7472f5cb3c46ff457b555bcee9faa on the SAME research/min-cycle-forest-2026-11-24 branch. Elementary paper deductions; exact finite residue-rectangle calculations and larger fixed-seed CRT sampling. No Lean compilation. Full stopping deficit and twin-prime conjecture remain open.

## 1. A potential that never increases on a LOW step

Keep the canonical MIN setup and the small-terminal-physical-class first-passage construction of the preceding note: odd M in [X,2X), N=X/2, B=ceil(sqrt(7X)), original individual cutoffs, Y tending to infinity with Y<=c log log B, L=2 product_(3<=p<Y prime)p<=log^(1/4) B, full inverse projected high cap and barrier-cell admission stop. Retain only tags whose actual noninitial cell-stop terminal physical class has mass <=a. Every preceding actual physical event on these retained paths has retained mass <=a, as proved previously. Truncate at the first attained h=2t-C>=H if reached; H>=max(BL,10B). All included post-heights <=H+4B. At a high projected key (q,C) there are O(H/q) actual possible clock classes.

Use the preceding periodic LOW-only deterministic ghost. For even C and phase t mod L, D_Y(C,t) is the maximum signed height increment over all prefixes of that ghost (including empty prefix). Write D=D_Y in local formulas. It is nonnegative, <=5L, and obeys the exact recursion
    D(C,t)=max(0, 2w-(p-1)+D(C+p-1,t+w))
when the ghost has a next LOW event with label p<Y and wait w. At a horizon without any eligible LOW label it is zero. The ghost always terminates by the LOW barrier.

Define the corrected potential
    Phi_Y(t,C)=2t-C+D(C,t).
Every actual LOW event of the full MIN process agrees with the next ghost event when it is selected. Thus
    Phi_Y(t+w,C+p-1)-Phi_Y(t,C)
       =2w-(p-1)+D(C+p-1,t+w)-D(C,t) <=0.
This is a pointwise, unconditional statement, not an average or distribution hypothesis. It holds also for the last LOW event on a truncated prefix. At the canonical initial state Phi<=6+5L, and at first attained height H, Phi>=H. Hence all positive gain necessary for first passage must come from high events. This differs from summing a positive maximum for each LOW block: successive LOW increments and potential changes are canceled exactly in this telescoping inequality.

## 2. Exact local upper envelope using the last LOW clock

Consider an actual selected high q>=Y at pre-horizon C, event clock n, with prior attained time t=n-w, w>=1. Its post-horizon C'=C+q-1. If a LOW prime is eligible at C, let r_0(C) be the smallest such prime, so the full least eligible prime r(C)=r_0(C). For all eligible LOW primes p, their clock classes are 0 mod2p for p|C-1 and p+2 mod2p for p|C+1. Let g(C,n) be the distance from n to the latest of these LOW clocks at or before n. This is the minimum backward residue distance among eligible LOW primes, computed modulo 2p. Since the high event actually wins, there is no LOW clock in (t,n] (a tie would select the smaller LOW prime). Thus g>=1 and
    1<=w<=g<=2r_0(C)-1<2q.
The case g=0 is incompatible with actual selection of q. The upper bound is not asserted sufficient for full MIN selection, since intervening high clocks may also forbid an otherwise possible w.

Let ell>n be the next LOW ghost clock from (n,C), with its selected LOW label b. Define the *unclipped* ghost value
    U(C,n)=2(ell-n)-(b-1)+D(C+b-1,ell).
Here D(C,n)=max(0,U). For any 1<=w<=g the same ell,b is the next LOW clock from (n-w,C), because the interval through n has no LOW clock strictly after n-w. Consequently
    D(C,n-w)=max(0,U(C,n)+2w).
The high corrected increment then satisfies exactly
    delta Phi = D(C+q-1,n)-(q-1)
                  +2w-max(0,U(C,n)+2w)
              = D(C+q-1,n)-(q-1)+min(2w,-U(C,n)).
In particular, when U>=0, the contribution of the actual wait cancels entirely and delta Phi=D(C+q-1,n)-D(C,n)-(q-1). For general U the maximum over the allowed integer w occurs at w=g:
    E_q(C,n)=[D(C+q-1,n)-(q-1)+min(2g,-U(C,n))]_+.
This is the exact maximum of the positive corrected increment over this LOW-compatible wait interval. It is an upper bound on an actual high increment, not necessarily realizable under all high-clock constraints.

Let R_q(C,n) be the following nonnegative residual envelope, all C even and n arbitrary:
    no eligible LOW prime:
          R_q=[D(C+q-1,n)-(q-1)]_+;
    LOW eligible, g=0:
          R_q=0 (actual high impossible);
    LOW eligible, g>=1:
          R_q=[E_q(C,n)-4 r_0(C)]_+.
At a real high event,
    delta Phi <=4r(C)+R_q(C,n).
For the no-LOW case use D(C,t)=0 and w<=2r(C); no need to know r(C) from the LOW residues. For the LOW case E_q bounds delta Phi and the displayed inequality is immediate. Note that the exact envelope E is for the positive part, and we deliberately subtract an available 4r budget rather than counting the full positive increment twice.

Moreover, pointwise at ALL residues (including impossible high ties),
    0<=R_q(C,n)<=[D(C+q-1,n)-(q-1)]_+.
In the eligible case this follows from min(2g,-U)<=2g<=4r_0; in the other cases direct. Thus R_q is identically zero for q>=1+max D. All of these functions are periodic in C mod L and n mod L at fixed q; the shift q-1 is interpreted mod L only in the D lookup, not in the linear subtraction. This is essential when q>L.

## 3. Rigorous new first-passage bound

Let overline R_q be the exact arithmetic mean over all L/2 even C residues and all L clock phases n:
    overline R_q=(2/L^2) sum_(C even mod L,n mod L) R_q(C,n).
Define the finite, nonnegative coefficient
    Gamma(Y)=sum_(q>=Y prime) overline R_q/q^2.
Only q<=max D can contribute. For fixed high q and either divisibility side, pre-horizon C lies in a progression of even integers of step 2q. Since gcd(q,L)=1, a fixed even C residue mod L has O(X/(qL)) actual candidate pre-horizons in the window; additive 1 is absorbed by X/(qL)>=cB/L. At each such horizon, the possible actual event clocks n are in one residue class modulo 2q and in a window of length O(H) from the first-passage post-height bound. Each phase n mod L of compatible parity has O(H/(qL)) candidates by CRT, since H>=BL; other parity has zero. This bound is uniform in the actual pre-horizon, no independent distribution of phases is assumed. Each physical event has at most a retained tags. Sum the nonnegative R_q over all these candidates and both divisibility sides to obtain
    sum_(retained truncated events) R_q <= O(a X H Gamma(Y)).
The existing per-prime eligible-horizon cost estimate S_q^cost=O(X/log^2 q) and physical incidence bound O(aH/q) at each projected key give
    sum_(retained truncated high events) 4 r(C)
        <= O(a X H/log^2 Y).
Sum the telescoping corrected potential over all first-passage paths. Initial Phi<=6+5L, final Phi>=H. No LOW drift term is left. If Z(H) counts these original tags hitting H, then
    Z(H)(H-6-5L) <= O(a X H [1/log^2 Y + Gamma(Y)]).
Thus for H>=max(BL,10B) and sufficiently large B,
    Z(H) <= O(a X [1/log^2 Y + Gamma(Y)]).
One may equivalently retain a harmless initial-error term O(X L/H). This is an unconditional bound; it gives a vanishing relative bound if a*(1/log^2 Y+Gamma(Y)) tends to zero. The constant in the big-O is not estimated sharply here, so a small numerical coefficient at one fixed Y is not a proof of a deficit.

For comparison, define
    Gamma_tail(Y)=sum_(q>=Y prime) E[(D_Y-q+1)_+]/q^2
where the expectation is over the entire even-C/clock-phase rectangle. By the pointwise inequality and the shift permutation of the even residues,
    Gamma(Y)<=Gamma_tail(Y)<= A_+(Y) sum_(q>=Y prime)1/q^2
              = O(A_+(Y)/(Y log Y)).
Here A_+ is the preceding full-phase signed maximum mean. Thus the old sufficient condition implies the new condition Gamma(Y)->0, but the reverse implication is not established. The exact local residual also depends on D before the high event and on the LOW-compatible wait, not merely a tail of the post-event D. This is a genuinely finer coefficient, not a proved asymptotic bound on it.

If q>Q_cut>=Y, the omitted coefficient is <= A_+(Y) sum_(q>Q_cut)1/q^2=O(A_+(Y)/(Q_cut log Q_cut)). This is an analytic relation to the true mean, not a numerical upper bound on a sampled omitted tail.

## 4. Conditional consequence for the full cell-stop residual

If Gamma(Y)->0 along a diverging sequence of Y, choose Y(B) on that sequence sufficiently slowly that L<=log^(1/4) B and Y<=c log log B. Choose a tending to infinity sufficiently slowly with a<=ceil(log^(1/4)Y), a*(1/log^2 Y+Gamma(Y))=o(1). Set W=1+log log(3B), H0=X/(log^4 Y * W), Q=ceil(L log B), Dscale=floor(sqrt(a)). The first-passage theorem gives o(X) small-terminal-class tags ever attaining H0; H0>=max(BL,10B) eventually. The earlier landing-divisor deletion gives o(X) cell entry tags q>=Q. For q<Q, clock-class count at entry height<=H0 gives O(a log^2 Y [Q+H0 W])=o(X) small-terminal-class tags. This uses the global harmonic bound W rather than incorrectly assuming log log Q=O(log Y) for an arbitrarily slowly growing cutoff. Root injections into stopped cells have o(X) mass by L=o(T).

Thus under Gamma(Y)->0, all small physical cell terminal classes have o(X) mass. The remaining cell classes have size>a, with within-class terminal variance >=S_c/2-o(X) at Dscale because Dscale/a->0. The preceding capped clock-moment estimate gives within-class terminal variance >=S_p/2-o(X) at all prime stops because Dscale=o(log^2 Y). The clock-refined non-splitting forest and harmonic near deletion at d=floor(Dscale/log^(1/2+epsilon)(2Dscale)) for fixed epsilon>0 then give the necessary inequality on no-twin windows
    2 P_phys,far >= N-o(X).
This does not prove the needed upper bound on physical far coalescence. Neither Gamma(Y)->0 nor a complete twin-prime proof is obtained. It is the same conditional end reduction as the preceding note, now using the new smaller local coefficient.

## 5. Exact finite calculation of Gamma

Saved research/min_corrected_height_potential_audit.mjs and research/min_corrected_height_potential_results.json, exact remote readback at 8b8bafc311721ad6ba0a20f767ccb69bb22af620. Compute D,U,g,r_0 and min(2g,-U) on EVERY even horizon residue and EVERY clock phase for Y=5,7,11,13, backward DP using the LOW barrier. Compute R_q and E_q for every phase and every prime Y<=q<=max D+Y (residual identically zero for q>=max D+1; the extra range also checks raw E). Verify pointwise tail domination, aggregate mean inequalities, and the exact maximization over allowed waits for a deterministic subset (all compatible residues for Y<=7; deterministic mod997 subset for Y=11,13). At Y13 this checks 78131 such residue/prime cases, with every allowed w checked inside each case. D sums agree with the previous exact ghost calculation. No original full-process trajectories are resimulated in this new exact audit; it tests the local residue envelope, not actual full selection sufficiency.

Exact finite means (rounded):
    Y    A_+/(Y log Y)   Gamma_tail    Gamma
    5    0.414223       0.066939      0.026667
    7    0.567083       0.117435      0.026031
    11   0.503351       0.138096      0.040144
    13   0.539447       0.145175      0.042402
At Y13 the residue rectangle contains 2668050 states; exact Gamma decomposition: LOW eligible 0.02697207635, no LOW eligible 0.01542943672. The full positive E contribution on LOW-eligible phases plus no-LOW tail without subtraction is 0.06634154403. This is not the coefficient of the entire height bound, because 4r has a separate sieve contribution. Max D=192. For q=13, mean R=2.94208055 versus mean post-tail=10.36717453, raw E/no-LOW-tail mean4.45297427. The improved coefficient is a comparison of explicit residuals, not a claimed factor improvement of the unknown asymptotic constant.

## 6. Larger finite CRT sampling

The exact rectangle grows very fast, so separately saved research/min_corrected_height_potential_sample.mjs and research/min_corrected_height_potential_sample_results.json, exact remote readback at bd48dd2b5a54b4805baa193fd3e4f40d3c1c50ef. For each Y take 8192 pseudo-random phase samples using a fixed xorshift32 seed derived from Y, unbiased modular rejection, independent residue draws for even C mod each odd LOW p and for t mod p plus a common time parity. This is the CRT parametrization of the uniform rectangle; no actual source dynamics are assumed uniform. Simulate deterministic LOW ghost from pre and shifted post state. Sample high q in [Y,32Y] with probability proportional to q^-2 using an explicit finite prime list. Multiply residual by the finite total q^-2 weight to estimate the TRUNCATED coefficient. Check sample-by-sample tail domination and termination (20000-event guard not hit). Display descriptive standard errors under the usual independent-sampling approximation; these are not rigorous confidence bounds. In particular the sampled estimate is neither an upper bound on Gamma nor the exact finite truncated coefficient. The omitted high-prime tail has not been bounded numerically. At Y13 the exact Dmax is192<32Y, so there is no actual omitted contribution to Gamma, allowing calibration.

Selected results (8192 samples each):
    Y    sampled A_+/(Y log Y)    estimated truncated Gamma (SE)
    13   0.533635                  0.043242 (0.002221)
    17   0.456650                  0.034580 (0.001770)
    23   0.415273                  0.028831 (0.001542)
    31   0.361130                  0.027932 (0.001486)
    53   0.263620                  0.019479 (0.001130)
    101  0.192306                  0.012808 (0.000747)
    199  0.142510                  0.009045 (0.000595)
    397  0.101427                  0.006298 (0.000437)
At Y397, mean signed maximum 240.953125 (SE3.80239), average ghost events18.62024, maximum events in sampled pre/post walks188, largest sampled D3652. The sampled truncated Gamma decreases over these chosen cutoffs, as does the sampled old ratio. This is finite numerical evidence motivating an analytic estimate, not a proof of convergence, uniform integrability, or small omitted tail. The larger samples are intentionally not called exhaustive. Exact code/data retained separately from sample code/data.

## 7. Next proof target

The corrected height removes LOW steps from the positive telescoping account altogether and reduces the residual to a finite residue-rectangle coefficient with exact LOW-clock compatibility. The analytic next target is a vanishing upper bound for Gamma(Y), for example via a uniform tail estimate for the ghost D distribution, or by exploiting the cancellation with U in the local high transition. The observed decay in the sampled coefficients is not such a bound. The physical far-coalescence upper estimate is independently unresolved. No new branch, no main edit, no Lean compilation.
