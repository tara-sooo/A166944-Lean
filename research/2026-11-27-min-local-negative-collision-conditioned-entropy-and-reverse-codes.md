# Negative MIN: collision-conditioned entropy and reverse spatial/clock codes

2026-11-27 JST. Continuation of 54b0687c82906efc4ef3a4c90a3d5d4fb0a6c2ff.
This note develops the entropy route on ACTUAL near-square-root selected
cohorts. It splits the exact entropy flow into base, distinct label,
and same-label displacement mixing, and restricts the upper bounds to
traffic actually involved in each type of collision. It also constructs
two independent reverse codes: prime-factor rank plus low-run gaps,
and clock-block ancestry with truncated subtree weights. The latter
has an exact telescoping redundancy formula. Finite tests expose
the costs of each relaxation. No asymptotic entropy coefficient or
selected-population lower bound is proved. Paper-level deductions,
no Lean verification or literature priority assertion.

## 1. Common selected section

Use the negative MIN and frontier conventions of d9f6049 and 54b0687.
Take fixed B>0, K=floor(sqrt(R)/log^B R), T=4K, a gain cap
J<=g T with fixed g<2/9, and the selected canonical roots
S={A in [R,2R]:6|A,G_T(A)<=J}. Denote its size N_s and fraction s_R.
For sufficiently large R their retirement positions a_T have
both neighbors K-rough, by the mod-30 potential
W<=9G/4+8, giving final idle length T-W>2K.
For H=floor(3+T-J/2), all selected paths reach first postheight H
at their final stationary position. Indeed their last completed
event is at elapsed time <=9J/4+8, and its height and all earlier
heights are <=3+9J/4+8<H for large R (g<2/9 suffices).
Their retirement height is >=H. First PREheight H+1 is the same
position, at the next tick before its action. The selected
population is fixed across every earlier cut.

For its final endpoint multiplicity m(a), define
L=(1/N_s)sum m log m. Recall the sufficient criterion
L-log s_R <=(3-delta)loglog R on unbounded R for fixed delta>0,
using the previous upper sieve for non-twin rough centers.
The work below does not establish this criterion.

## 2. Exact three-part entropy ledger

At a fixed record preheight b, let u(y) be initial first-cut mass,
v(x) the entire visiting mass at a moving source, and I(y) the
sum of v over incoming return edges. Use the decreasing return
forest of f8b2421, including multiple visits to b, so v(y)=u(y)+I(y).
For f(t)=t log t, f(0)=0, and
Phi(a,b)=f(a+b)-f(a)-f(b), the entropy creation at y is

    Phi(u(y),I(y)) + f(I(y))-sum_(x->y) f(v(x)).

Group incoming edges by l=(p,sigma), their triggering prime and sign.
Write I_l(y)=sum_(x->y,label l) v(x). The second term splits EXACTLY
into f(I)-sum_l f(I_l) and sum_l [f(I_l)-sum_(x of l)f(v(x))].
The first is label entropy, the second within-label entropy.
At given b,l the possible sources are one class modulo 4p,
so for given y the integer k=floor((x-y)/(4p)) distinguishes
all sources of that label. Thus the within-label part is the
conditional Shannon entropy of k, multiplied by its mass.

Summing over all vertices and b cancels every internal f(v);
initial canonical masses are one. The sum of these three nonnegative
terms equals N_s L, including all below-record merging hidden inside
the return edges. The cancellation does not need distinct labels,
a mass cap, independent coordinates, or absence of earlier merging.

## 3. Collision-conditioned upper bound

At each b define
 A_b = sum_(y:u(y)>0) I(y),  B_b = sum_(y:I(y)>0) u(y).
Only these masses take part in base/arrival mixing.
Let C_b be the total incoming mass at y with at least two
different incoming labels, and C_(b,l) the label-l marginal on
those vertices. Let D_(b,l) be the total label-l mass at those
(y,l) with at least two distinct incoming sources of that label,
and Q_(b,l)=sum on these groups v(x) floor((x-y)/(4p)).
Zero-mass terms below are zero. Put
g(t)=(1+t)log(1+t)-t log t, g(0)=0.

By log-sum (or concavity and homogeneity of Phi), the base
part is <=Phi(A_b,B_b). By conditioning reducing entropy,
the label part is <=f(C_b)-sum_l f(C_(b,l)).
By the geometric-distribution maximum-entropy inequality,
the displacement part is <=sum_l D_(b,l) g(Q_(b,l)/D_(b,l)).
Consequently

    L <= (1/N_s)sum_b [
           Phi(A_b,B_b)
          +f(C_b)-sum_l f(C_(b,l))
          +sum_l D_(b,l)g(Q_(b,l)/D_(b,l)) ].       (1)

Crucially no charge for an incoming cohort whose target has
no base mass in the first term; no charge for a uniquely labeled
arrival in the second; and no charge for an injective label
in the third. The earlier all-traffic estimate charged many
such moves. Further aggregation by concavity yields
sum_b Phi(A_b,B_b)/N_s <=Phi(A,B), with A=sum A_b/N_s,
B=sum B_b/N_s. Let E_br be the last two terms of (1), normalized.
A concrete sufficient asymptotic condition is

    s_R >= c log^(-gamma) R,
    A <= (alpha+o(1))loglog R,
    B <= (beta+o(1))loglog R,
    E_br <= (eta+o(1))loglog R,
    gamma+Phi(alpha,beta)+eta < 3.                 (2)

Here alpha,beta,gamma,eta are nonnegative constants. For instance
alpha=beta=2 gives Phi=4 log 2=2.77259, leaving room for small
branch loss if s_R is bounded below. No such asymptotic incidence
estimate is proved. These normalized quantities count root
incidences, not distinct physical keys; the prime-coordinate
dilution from the fresh insertion does not imply (2).

One unconditional component bound: fix c0>0 and retain the
incoming edges with p>=c0 J, J tending to infinity. Within
this high subpopulation at a given b, there are at most two
labels/signs for large J, because p^2>2b+1 (all b<=H=O(J)
when J=gT with g fixed positive); for each label there are
at most 1+floor(J/(4p)) incoming source shells at a target.
Every selected root traverses at most J/(c0 J-1) such edges,
since their completed gains are disjoint. Thus the entropy
from MIXING WITHIN the high incoming subpopulation is O_c0(1)
per selected root, across all record levels. This does not
include binary mixing with lower-label incoming branches or
with the base cohort, and does not apply to all incoming
edges. It bounds a component without an inherited mass cap.

## 4. Late entropy, a direct displacement code

For first preheight b let X_b be its position and Y=a_T.
On the fixed selected cohort, Y is a deterministic function
of X_b (the subsequent first cuts are deterministic up to
the common H+1 cut). Hence L_final-L_b=H(X_b|Y).
Put D=(X_b-Y)/2>=0, alpha=Pr(D>0), and d=E[D].
Given Y, D determines X_b. Encoding whether D is zero, then
the nonnegative integer D-1 conditional on D>0, gives

    L_final-L_b <= h_2(alpha)+alpha g(d/alpha-1). (3)

When alpha=0 the right hand side is zero. This is an exact
information bound on entropy after b, rather than a bound
on all past gain. A coarser sufficient estimate uses
alpha<=Pr(G_T >=18b/35-10) by the earlier event barrier
(676c259), and the cap D<=floor(J/2). Audit A checks
the coarser version with an integer-safe threshold and
log(floor(J/2)+1), not the sharper mean-d version (3).
The gain-tail bound by itself is not a new tail estimate.

## 5. Reverse spatial code using factor ranks

For a selected root path ending at a, fix cutoff Y0>=3
(unrelated to the frontier K). Read completed jumps backwards.
Separate k jumps p_i>Y0 by k+1 low runs, with half-distance
gaps l_0,...,l_k>=0, including empty runs. Let L0=sum l_i.
Starting from a, first add 2l_0 to obtain the arrival of
the last high jump. For a jump with target x, its odd
prime p divides x (minus) or x-2 (plus). These two
conditions are disjoint for any odd p. Thus its high
prime can be identified by its rank in the candidate
factor list of x and x-2, not by its numeric value.
Then add p-1, add the next low gap, and repeat.
The resulting final reconstructed position is exactly A.
No clock information is needed to establish injectivity
of this ROOT code: some other decoded words need not
describe a legal trajectory.

Because the total gain is <=J, the candidate list can
omit p>J+1 and use the sharper remaining-budget cutoff:
if used high gain is U and r later high choices remain,
p<=J-2L0-U-r(p_min-1)+1, where p_min is the least prime >Y0.
Also all positions are O(R), so at most
d_Y0=2 floor(log(2R)/log Y0) eligible factors at any
reverse step (can use a slightly enlarged physical upper
bound if needed). Assume d_Y0>=1 when a high jump occurs.

Let Z=(l_0,...,l_k) be the reverse gap vector. The conditional
entropy of the actual selected root satisfies

    L <= H(Z|a mod M)+E_S sum_i log d_i,           (4)

for any fixed positive integer M, where d_i is the size of
the actual candidate factor list in the reverse decoding.
This follows by the chain rule or by coding Z with its
conditional marginal distribution and choosing factor ranks
uniformly. More explicitly the probability assigned to a
root conditional on endpoint is

    w(A,a)=pi(Z|a mod M) product_i 1/d_i.

For ANY probability mass functions pi on gap vectors,
not necessarily the empirical marginals, the sum of these
weights over distinct roots in a fixed endpoint fiber is <=1:
each vector defines a branching decoder with probability
mass at most one, and each branch reconstructs a unique root.
Consequently

    D_selected >= sum_(A in S) w(A,a_T)
               >= N_s exp(E_S log w(A,a_T)).     (5)

The second inequality is Jensen. The first is a Kraft-type
support certificate that can exploit a well-coded subpopulation
without controlling the mean length of the rest.

A coarser formula uses H(k,L0) and
log binom(L0+k,k) for compositions into k+1 gaps. A further
first-moment bound (not separately audited) follows from
geometric maximum entropy and conditioning:
if kbar=E k, lbar=E L0, then

    L <= g(kbar)+(1+kbar)g(lbar/(1+kbar))
                          +kbar log d_Y0.         (6)

For the gap vector conditional on k use subadditivity across
components and concavity of g, then weighted Jensen with
weights k+1. Formula (6) identifies a possible path count
and low-gain target, not a claim that such counts have the
needed growth. The bound may be poor if many high events
occur or if low gaps carry substantial entropy.
Audit B confirms that the factor rank part alone is small
at high cutoff but the low-gap cost dominates. For every
tested slab the best of the compared codes in this family
was the trivial all-low vector (only total gain recorded).
Thus no numerical improvement over the actual endpoint
entropy has been achieved with this spatial-only code.

## 6. Clock-block reverse code and exact retirement filtering

Use the exact reverse block ancestry of 9314cd5
(research/2026-11-27-min-local-negative-clock-block-ancestry-and-terminal-tail-sieve.md).
At state (x,u), the stationary backwards interval is [d(x,u),u],
d=max(0,max_clock[u-((u-x/2-c) mod 2p)]).
A candidate arrival h in this interval from b=x+p-1 has
clock n=h-x/2, preheight t=h+(p-1)/2 and previous state
(b,t-1). Check the exact prime winner at b,n; require t<=H,
b<=Amax=min(2R,a0+J). The old gain/height pruning
h<=11+7(Amax-x)/4 and 18t<=35(Amax-x+10) applies.
At (x,u), a birth is possible when x is canonical and
3 is in its idle interval.

For the fixed-time selected set there is an additional
retirement constraint not present in the earlier first-height
tree: at endpoint a0,H let b_next be the next preheight
with a firing at unchanged a0. Then a root A in the tree
has retirement height 3+T-(A-a0)/2. It must be strictly
less than b_next. Equivalently the birth position must obey

    A >= max(lo,a0+2(3+T-b_next)+2).              (7)

Here lo is the lower canonical slab boundary; all positions
are even. The previous upper bound and the first-height
clock constraints still apply. With (7) the tree births
are exactly the selected fixed-time fiber, because H is
reached by T whenever G<=J and the stationary segment
extends through retirement. An initial scratch audit
omitted (7); at a0=377718 the reverse tree had five births
but the selected fixed-time fiber had one. This mismatch
was corrected before committing the final audit. No claim
that first-height and fixed-time fibers coincide without
the retirement constraint.

At each reverse node v with birth flag B(v) in {0,1}
and children w, define bounded-lookahead counts

    M_0(v)=1,
    M_(d+1)(v)=B(v)+sum_w M_d(w).

These count births seen before the truncation depth plus
unresolved frontier blocks. They may decrease with d
because dead branches disappear; no monotonicity assumed.
Use birth option weight 1 and child option weight M_d(w),
normalize by M_(d+1)(v). For a genuine selected root along
nodes v0,...,vr ending at its birth, every selected option
has positive weight. Its conditional code probability is

    w_d = [prod_(i=0..r-1) M_d(v_(i+1))/M_(d+1)(v_i)]
                    / M_(d+1)(v_r).

Sum of w_d over all births in an endpoint fiber is <=1;
some probability may be lost on dead branches. The negative
log code length has the exact telescoping formula

    ell_d=log M_(d+1)(v0)
        +sum_(i=1..r) log(M_(d+1)(v_i)/M_d(v_i)).   (8)

Hence the selected entropy is <=E_S ell_d and the support
is >=sum exp(-ell_d). This is a second, local arithmetic
certificate with no empirical gap distribution needed.
For d larger than every residual subtree depth, counts
are exact fiber counts, the ratio terms vanish and the
code is uniform on the actual fiber. For finite d the
redundancy may be expressed precisely: if Z_a=sum w_d
over the fiber and U_a is uniform on that fiber, then

    E_(U_a) ell_d-log m(a)
           =D_KL(U_a || w_d/Z_a)-log Z_a >=0.       (9)

So two distinct errors matter: imbalance of code
probabilities and lost mass on dead branches.
One can also directly use (8) as a proof target:
if a bounded or slowly growing d yields
E log M_(d+1)(v0)+E sum log ratios -log s_R
 <=(3-delta)loglog R, the frontier contradiction follows.
Neither term is bounded asymptotically here.
The inverse enumeration itself is exact; solving it on
all endpoints and all depths would merely calculate m(a),
not provide an asymptotic theorem.

## 7. Reproducible numerical results

All three final scripts were executed, fetched at exact
remote commits and re-executed in the ECMAScript research
runtime. Reproduce with node. No separate Node or Lean
invocation. No new external literature claims in this note.

A. research/min_local_negative_selected_entropy_forest_audit.mjs
   commit 0ab3d500a5aa897538062a2235c697f119a2f336
   blob 90ff775ca65390be6c3729eb0ba285c9ac31b831

Actual slabs R=12000,48000,192000,480000,1000000,2000000,
B=1/2, T=4K, J=floor(T/5). Fixed selected root set,
first-cut interval storage, exact return forest and
three-part entropy. Check all branch shell distinctions,
both full and collision-conditioned bounds, global entropy
and coarse late entropy bounds.

    roots                            622004
    completed events               14181783
    selected roots                   207261
    distinct return edges            302429
    traffic checks                   560485
    entropy-level checks               3812
    shell checks                     302429
    coarse tail controls                 44

At R=2000000, 115899 selected of 333333:
L=2.62109874, base term=2.59166734,
label term=.02943140, same-label shell term=0.
Normalized all return traffic=3.44915, normalized
base-collision incoming A=1.90549, base mass B=2.68027,
different-label collision traffic=.045255.
All-traffic bounds for base/label/shell:
3.97193939,2.87337582,.40559627.
Collision-conditioned bounds:
3.04900775,.03175298,0 (sum 3.08076074).
This is a substantial finite tightening of (1),
but the corresponding effective support lower bound
is only about 5322, below the finite bad-count 11616.
The sum is not an asymptotic upper bound with a
verified coefficient. In this control ~98.88% of
actual entropy is base/arrival mixing. Entropy accumulated
through b=63 is 2.16804, through b=127 is 2.46301,
through b=255 is 2.59084. Most loss is earlier than
the terminal height. All tests passed.

B. research/min_local_negative_reverse_gap_entropy_audit.mjs
   commit 33fedd889ecba7637ac5ab9d0ca0e127c50ad771
   blob a0a31868006750464036c5c74ac49de736125b80

Four actual slabs R=48000,192000,480000,2000000,
same selected-root rule. Compare cutoff grid (including
3,5,7,11,19,31, sqrt J, J/4, J/2 and J+1), full gap
vector distributions, composition codes and gap vector
distributions conditional on a mod 210. All code
probabilities use remaining gain budget in the factor list.
Each root decoded exactly and the per-endpoint
Kraft inequalities checked.

    roots                            453336
    completed events               10466579
    selected roots                   151595
    reverse root decodes            1513870
    reverse factor pin checks       2252926
    Kraft checks                     191001
    entropy comparisons                  39

At R=2000000, cutoff 31: mean high jumps .6605,
mean low gain 47.395, factor rank entropy bound .2773,
conditional gap-vector code mean length 5.5825.
Cutoff 148: mean high jumps .05751, factor rank cost
.00732, total code mean length 3.9005.
The best compared code uses cutoff 297 (all-low);
conditional mean length 3.6460, weight sum 4527.60.
The actual entropy 2.6211 and its effective support
8428.51 are better. The empirical coding exercise
does not show that (4) improves the actual entropy,
nor that the empirical gap distribution is predicted
by a proved law. All checks passed.

C. research/min_local_negative_reverse_clock_entropy_audit.mjs
   commit 718135c4a400741228dec4abe9dc1bdcbd163e30
   blob b784a5ce15cc16124661ba5bbea3871976a1db21

Four actual slabs R=12000,48000,192000,480000,
same fixed-time selection. Exact clock-block candidates
with retirement constraint, depth d=0,...,4 codes,
check every true reverse branch and birth, Kraft
inequalities, independent full inverse counts on
70 deterministically selected endpoints.

    roots                            122004
    completed events                2202302
    selected roots                    36182
    endpoint trees                     6242
    generated clock blocks          2474258
    candidate edges                 2685185
    true reverse branches            177485
    birth checks                      36182
    Kraft checks                       6242
    exact inverse fiber comparisons      70

At R=480000, actual L=2.21754, 24664 selected,
3786 distinct endpoints. Average code length at
lookahead d=0,1,2,3,4:
10.66948,7.43475,5.81404,5.00354,4.45754.
Weighted support lower bounds:
61.55,80.87,215.07,393.12,666.17.
At d=4 mean first term of (8)=4.45318,
mean ratio sum=.00436. The coarse root term
dominates at this depth. This finite comparison
does not imply the ratio sum stays small as R
grows or that bounded-depth codes are competitive
asymptotically. All final checks passed; the
initial missing retirement filter is described above.

## 8. Status and next targets

The three-way decomposition identifies the main term
and removes charges from noncolliding traffic. Formula
(2) is an explicit alternative to a third-moment or
maximum-mass recurrence; it is not proved at growing R.
The reverse codes provide independent checks on where
information loss can arise. The spatial code loses too
much in low-gap descriptions in the tested range, and
the bounded-lookahead clock code counts many spurious
frontier branches. To improve the latter, one would
need arithmetic pruning or a weighted harmonic
reference on the reverse blocks that controls (8)-(9),
not simply increasing a finite search depth.
The most direct outstanding estimates are the two
base-collision incidence masses and the selected
root fraction at actual near-sqrt scale. No new
asymptotic result for them, no full entropy bound
with coefficient below three, no proof of twin
infinitude or Lean verification. No canonical
Lean target, sibling branch or Context changes.
