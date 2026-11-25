# Long low-label run capacity and a weighted A1 tail at the mean-square scale

Continuation of [78b1212](https://github.com/tara-sooo/A166944-Lean/commit/78b1212d87663bbc8a7b137aa3e18375bc18885b) and [850c00f](https://github.com/tara-sooo/A166944-Lean/commit/850c00f2bac25d3c9eb49ef75993187ce054a995). The mean-square smoothing bound cannot simply be applied to repeated deficit crossings. Instead we use the measure of zero moving averages in the monotone horizon coordinate to control the total gain of long runs of small labels. Short runs supplying recovery of a large A1 must start with large deficit, which restricts their preceding high event. This gives a weighted A1 tail bound at scale V_R, even for the enlarged cutoff where the earlier uniform discrepancy E_R can exceed sqrt X. No twin-prime contradiction or Lean kernel verification.

## 1. Capacity of long low-label runs

Take any finite contiguous block of actual canonical MIN events, with horizon endpoints H_start,H_end, total gain G=H_end-H_start. Write J=[H_start/2,H_end/2) in integer coordinate, n=G/2. For R>=5 use the horizon CRT barrier family of density alpha_R and period P=P_R (odd prime product), with f=1_barrier/alpha_R. For an integer 1<=l<=P set f_l(j)=l^(-1) sum_{a=0..l-1} f(j+a), and sigma_l^2=mean_period (f_l-1)^2. By 78b1212,
    sigma_l^2<=4 V_R/l,
    V_R=P_R Lambda_R^2 D2_R,
    V_R/P_R=exp(-(2 log(pi/2)+o(1))*pi(R)).
In the exponent pi(R) is the prime count; the pi inside the logarithm is the circle constant.

A low run is a maximal contiguous sequence of events in the block all with labels <=R, including runs cut off by block endpoints. Its horizon interval [a,b) in the integer coordinate contains no barrier (the half-open crossing convention is essential), and distinct low runs have disjoint horizon intervals. If its length L=b-a>=2l, then every starting integer j in [a,b-l+1) satisfies f_l(j)=0, because its l positions lie within this interval. There are L-l+1>=L/2 such starts, all in J and disjoint between runs. On a zero of f_l the squared fluctuation is 1, so the number of zero positions in one period is <=P*sigma_l^2. Over J it is <=(n+P)*sigma_l^2 by periodicity and nonnegativity. Thus the total absolute horizon gain of long low runs (gain>=4l) obeys the finite bound
    G_long <=4*(n+P)*sigma_l^2
           <=16*(n+P)*V_R/l.                            (1)
No averaging of a trajectory or independence assumption is used. The first bound may use the exact periodic proportion of zeros in place of sigma_l^2. In a crossed macroscopic window with G=O(X), P=o(X), this gives G_long=O(X V_R/l). In particular at any scale l/V_R->infinity the long low runs have o(X) total gain. This differs from the previous bound on maximum possible gain in a SINGLE low run; it controls the sum even when a ray visits many different low-run gaps.

## 2. Tail recovery and a finite short-run bound

Use the established adaptive MIN model: ordinary deficit d=2t-H>=0, x=d+3, event label p, wait w, gain g=p-1, post d'=d+2w-g, adjusted D=d'-6I. The bound w<=2p implies d'-d<=5g for all p>=3. Hence along any run the increase of x from its initial value to any event plateau in that run is at most 5 times the horizon gain of that run. (This is a one-sided bound; no monotonicity of d is assumed.)

A1 has p>=47, p>=5d+15, D=2p. A0 is the same low-deficit test with D=0. B denotes all other events p>=47. Near/far are the previously fixed square-band classes. For a block with pre-horizon lower bound A>=257, set k=floor((A-1)^(1/4)), eta=2/k, c=9/5-2eta>0. Let C bound all labels. The far-only recovery theorem of 850c00f associates to every marked A1 of label p the real interval
    (p/5, 2(1-eta)*p],
of length c*p. Match each level to its first subsequent downward crossing within the block; if not crossed, it remains pending at the end. Intervals pending at a fixed time are disjoint, no downward event can supply more than its actual drop d-d', and total pending length is <=2C. All nonreset payments are far: a later near label s>=(1-eta)p has nonreset post x'>2(1-eta)p. These statements hold for any marked subset.

Fix R>=47 and T>=47, mark ALL A1 with p>R and p>=T, and write W_T for their summed prime labels (counting occurrences). We partition the supply of recovery length:
* Pending at the endpoint: <=2C.
* Decreasing resets, of label>=7, at most N+1 in the block, where N is the number of actual canonical visits in (start,end]. Total payments <=C(N+1). This counts even resets with label<=R, so they are not needed in the low-run supply.
* Decreasing nonresets with label>R: all payers are far B, since A1 increases and A0 resets. With B_R the count of all far B p>R, these payments are <=C B_R.
* Low-label nonreset payments in long runs: <=G_long by the ordinary-drop bound d-d'<=g for each event.
* Low-label nonreset payments in short runs (gain<4l): analyze below.

Any short low run supplying positive recovery length to a marked tail must have an event with pre x>T/5 (the entire demand is above T/5). If x_0 is that run's initial x, the one-sided growth bound implies
    x_0 > T/5-20l.
Except for the initial run, a maximal low run immediately follows an event p_prev>R. If this preceding event is A1, its post x_0=2p_prev+6I+3<=2p_prev+9. Consequently
    p_prev > Q=(T/5-20l-9)/2.                             (2)
Every such preceding A1 is distinct for distinct runs. When Q>1, their number is <=G/(Q-1), since each has gain p_prev-1>Q-1. Other preceding high events are either near (at most n_near, the number of all near events in the block), far A0 (at most N+1), or far B (at most B_R). The initial low run contributes at most one additional run. Every short run pays <4l in total, not per mark. Thus all short low runs that supply tail recovery pay at most
    4l*(G/(Q-1)+n_near+N+B_R+2).                        (3)
This uses no assumption about the number of visits to any deficit level and no adjacent-event assumption on the original marked A1 and a paying low run. The preceding A1 in (2) can be a different A1 event. This is why repeated upward/downward visits do not invalidate the argument.

Putting these capacities together gives the finite inequality, for Q>1 and 1<=l<=P_R,
    c W_T <= 16*(G/2+P_R)*V_R/l
              +4l*(G/(Q-1)+n_near+N+B_R+2)
              +C*(N+B_R+3).                            (4)
One may replace the first term by the exact observed total long-run gain, or by the first bound in (1). All quantities are actual block quantities except for the explicit barrier bound. The count N+1 comes from canonical normalization within seven ticks for a reset with label>=7, with one possibly pending visit at the boundary, as in 850c00f. No assertion that low runs themselves are deficit-monotone is made.

## 3. Quantitative weighted tail bound in macroscopic windows

Consider a crossed horizon window [X,lambda X] on an infinite canonical ray, lambda>1 fixed. The established geometry gives G=(lambda-1)X+O(sqrt X), C=floor sqrt(lambda X+1), n_near=O(sqrt X), c=9/5-o(1). Take any cutoff from 78b1212:
    R = largest odd prime with P_R exp(-gamma*pi(R))<=sqrt X,
    0<=gamma<2 log(pi/2) fixed.
Then R=Theta(log X), P_R=o(X), V_R log^a X=o(sqrt X) for every fixed a>0. Also P_R>=sqrt X/O(log X) by the next-prime bound, and V_R/P_R decays faster than any fixed negative power of R. In particular for T<=C and l=ceil(sqrt(V_R*T)), we have l<=P_R eventually, because V_R C/P_R^2=o(1). When T>=K V_R for a sufficiently large absolute fixed K, e.g. K=10^6, l<=T/200 for all sufficiently large windows, and Q>1 with Q-1>=T/50 (use T>=large, l<=T/200, Q>=T/20-9/2). Also l<=C for such T<=C. If T>C the tail is empty.

Substitution into (4), absorbing constants depending on lambda and the fixed near definition, gives
    W_T <= O_lambda( X sqrt(V_R/T) + sqrt X*(N+B_R+1) ),
    K V_R<=T<=C.                                      (5)
Indeed the long-run term is O(X V_R/l), the term l G/(Q-1) is O(X l/T), and l*n_near=O(l sqrt X)=O(X sqrt(V_R/T)) since T<=C=O(sqrt X). Remaining short-run exceptions are absorbed by C(N+B_R+1). All estimates are deterministic and uniform in the ray/window. Formula (5) is an upper bound on the sum of labels of all marked A1 p>=T, not merely the number of such occurrences, and permits arbitrary repeated use of individual labels.

Under the same sparsity assumptions as the earlier work,
    N=o(sqrt X), B_R=o(sqrt X),
for EVERY omega(X)->infinity we obtain
    sum_{A1,p>R,p>=omega V_R} p = o(X).                 (6)
If omega V_R exceeds C there are no such marks. For a fixed sufficiently large K, the weight at p>=K V_R is <=O(X/sqrt K)+o(X), with the implied constant independent of K. This supplies uniform tail control on the horizon-gain scale, not a relative o(W) statement for sublinear total mark weight W. The same upper bounds hold for the corresponding gain sums, since gain=p-1.

In 78b1212, m_f=Omega(X/V_R) was proved for far A1 under the sparse hypotheses, with the mean label O(V_R) and an o(m_f) count tail above omega V_R. The new (6) controls the WEIGHT of that tail on scale X, which cannot be inferred from the mean bound alone. It improves the earlier weighted-tail threshold of order E_R (850c00f), because V_R/E_R decays exponentially in pi(R), and (6) applies at enlarged cutoffs even where E_R/sqrt X->infinity. For example omega=log X is admissible, and V_R log X=o(E_R) when R~log X. All near A1 then have o(X) weight in the sparse branch, since near labels are >=(1-o(1))*sqrt X and V_R/sqrt X->0.

## 4. Good-mark weight recovery at enlarged cutoffs

At the enlarged R choose S as in 78b1212, largest odd prime with P_S<=R, so E_S=o(R). Earlier completed-slab allocation with geometric ratio 1+1/log X discards O(sqrt X log^2 X) marks under the sparse hypotheses: decreasing resets are <=N+1, all high ordinary-decreasing nonresets are B and their number is O(sqrt X) including the near population. The number of geometric levels is O(log^2 X) and each nonreset intersects O(log X) slabs. The earlier count of bad marks is unchanged; it never required E_R=o(sqrt X).

Split these bad marks at T=V_R log X. The weight below T is O(V_R sqrt X log^3 X)=o(X), by the improved cutoff assumptions. The remaining tail has weight o(X) by (6). Hence
    W_good = W-o(X)                                     (7)
for the good marks of the completed-slab theorem, with W the sum of labels of all A1 p>R. This was previously established using uniform E_R and could fail as an estimate at the enlarged cutoff; now it follows without such a bound. Moreover the good count is m-o(m) because m>=m_f=Omega(X/V_R) dominates sqrt X times every fixed log power.

The dense S-deficit-cut matching inside good slabs, with actual lower-band decrease total F and count j (nonreset S<s<=R), therefore gives simultaneously
    F >= theta_S*((9/5-o(1))*W-o(X)),
    F+2E_S*j >= (9/5-o(1))*W-o(X).
These are the previous full-weight type estimates, now also with the good-slab relative estimate available on a set of weight W-o(X) at every enlarged cutoff. For sublinear W the relative good-weight estimate remains separate: (7) does not assert W_good=(1-o(1))*W. Neither sparsity hypothesis is forced by finite twins. The new tail bound and the upper bound on long low-run supply do not yet bound the total small-prime recovery supply sufficiently to contradict the count lower bound.

## 5. Reproducible diagnostics

[Audit b583eaf](https://github.com/tara-sooo/A166944-Lean/blob/b583eaf343ae18e4e01a46fe19957f4e7aa712a2/research/min_direct_low_run_tail_audit.mjs), blob 7e4e9f433c4fe1ca729bd72b08ebf9fa80fb26aa. Exact remote readback. Run node research/min_direct_low_run_tail_audit.mjs 60000 180. Actual ECMAScript function executed in the tool runtime, not a separate Node process.

Complete horizon barrier periods R7/11/13/17, seven l values per period. Exact cut and zero-position counts, floating mean-square values and comparisons with analytic bound 4V_R/l. 1,680 synthetic periodic barrier-gap interval tests. 29,998 odd canonical roots through 60,000, 549,085 events, 5,254 A1, all terminated within 180 events. With diagnostic R7/11/13, l1/2/4, T151/251/401/601 subject to Q>1, full and suffix blocks plus nine witness controls: 978,921 block incidences, 3,782,139 low-run barrier/capacity checks, 240,264 long-run zero-start checks including synthetic controls, 2,674,359 ordinary interval allocation checks, 843 marked-block conservation and finite weighted-tail bounds, 63 nonreset near-exclusion payment checks. These overlapping diagnostic samples are not observations of a macroscopic infinite-ray window. At small diagnostic R<47 the code counts other high far events where needed for the geometry; the theorem uses R>=47. All assertions passed on the final run.

The ordinary finite scan did not exercise short runs making positive tail payments. A new actual 1,634-digit canonical CRT root with first two event labels 1279 and 7 was constructed and tested by 1,916 literal BigInt GCD ticks (including quiet ticks and both selected ticks), with the adaptive eligibility bound checked. First A1 p1279, even side, then odd label7 at wait1, ordinary deficit drops4. The CRT chooses p=3mod4,1mod3,5mod7, avoids all smaller competing first-event factors, and makes the odd second clock select7. This gives a short low run of gain6 for smoothing lengths2,4 and a long run for length1. Using the exact horizon residues in a conservative translated lower-horizon control, nine finite tail tests passed, six short-paid-run and preceding-A1 checks and three long-run checks. An initial witness diagnostic chose too small a conservative lower horizon, excluding its tiny four-unit drop from the far-only recovery interval; the assertion failed. The final source raises that conservative bound while keeping it below the actual huge horizon, verifies residues and literal ticks, and reruns all checks. Integer scaled interval lengths and exact cut counts stay within safe integer ranges; the analytic V_R and variance tests use floating-point tolerances. No actual infinite trajectory, external novelty claim or Lean kernel verification. Main and sibling branches unchanged.

Next: use long-run capacity with recovery at smaller mark scales or derive stronger constraints on short runs following A1. The present argument deals with repeated deficit visits through disjoint horizon runs, not through an unjustified independent sampling of deficit phases. No finite-twin contradiction.
