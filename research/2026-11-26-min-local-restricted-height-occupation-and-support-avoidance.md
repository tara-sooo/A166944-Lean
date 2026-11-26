# Height occupation energy and joint support avoidance

2026-11-26 JST. Continuation of 7021cc120bf07b05137b106a04188d63cc2f8b48.
Seek a weaker dense-band activation criterion than linear total gain and
sublinear total event count. Use high-deficit occupation rather than
unweighted event counts. Separately strengthen the periodic deletion
lower bounds to joint avoidance and Laplace domination. Paper deductions
and executed finite diagnostics, not Lean kernel verification or a
twin-infinitude proof.

## 1. Why a small-run cap does not resolve the event count

Let G_y,N_y denote total displacement and event count of the canonical
restricted trajectory with all odd primes below y. Fix a small alphabet
of primes <=z and let L_z be its arbitrary-phase consecutive gain cap.
Write H_z for the number of events with p>z. Then

    H_z <= G_y/(z-1),
    N_y <= H_z+(L_z/2)(H_z+1).

The latter follows by partition into at most H_z+1 low runs.
The resulting upper bound on N_y/G_y is not known to tend to zero
as z grows: the cap L_z grows much faster than z in the available
wall estimates. In particular this argument does NOT derive
E N_y=o(y) from E G_y=O(y). The preceding periodic displacement
lower bounds already rule out a uniform low-run cap o(z/log z).
Do not infer an asymptotic event count from the finite caps.

## 2. High-height occupation and exact overlap identity

As in 7021cc1, h=v-u/2 starts at 3, rises by w_i during
the wait of each event, then falls by g_i/2=(p_i-1)/2.
Let k_i=h_i+w_i, h_(i+1)=k_i-g_i/2. Define the integer
down interval I_i={h_(i+1)+1,...,k_i}, and

    D_y(h)=sum_i 1_(h in I_i),
    h0=ceil((y-1)/2),
    L_y=sum_(h>=h0) D_y(h)^2.

Here y may be taken an integer >=7. D_y is a local time in
HEIGHT, not in offset, firing time, or origin count.
There is no restriction on the number of events.
In particular

    sum_h D_y(h)=G_y/2,
    L_y=sum_i |I_i intersect [h0,infty)|
        +2 sum_(i<j) |I_i intersect I_j intersect [h0,infty)|.    (1)

The latter is exact by expanding the square. It makes high
occupation energy a weighted count of repeated visits to
the same levels. Intervals from arbitrarily many low-height
events contribute nothing to L_y.

Write Hmax=max(3,max_i k_i) for maximal half-deficit.
For the new prime band B_y=primes in [y,2y] define
a_y(h) and Phi_y as in 7021cc1:

    a_y(h)=sum_(p in B_y) [1_(p|2h+1)+1_(p|2h-5)]/p,
    Phi_y(t)=sum_(1<=h<=t) a_y(h).

For h>=1 the defects are odd and nonzero; if h<h0
both have absolute value <y. Therefore a_y(h)=0 there.
The old coarea identity and conditional CRT union bound give

    P_any <= 2 sum_(p in B_y)1/p + Phi_y(h_end)-Phi_y(3)
                           + sum_(h>=h0) a_y(h) D_y(h).           (2)

P_any means conditional probability over the CRT lifts of
ONE old canonical seed residue, not empirical local activation.
No independence between events is used.

## 3. An energy estimate needing only a height cap

Suppose Hmax<=Cy for fixed C>=1. No bound on G_y or N_y
is needed in this section. For sufficiently large y, each
nonzero defect at h<=Cy has magnitude O_C(y)<y^2,
and consequently at most one prime divisor in [y,2y].
Thus max_h a_y(h)<=2/y on this range. For each prime p in
the band, each of the two congruences has O_C(1) solutions
in [1,Cy]. By the dyadic reciprocal prime sum,

    sum_(h<=Cy) a_y(h) <<_C 1/log y,
    sum_(h<=Cy) a_y(h)^2 <<_C 1/(y log y).

Combining (2) and Cauchy-Schwarz gives

    P_any <<_C 1/log y + sqrt(L_y/(y log y)).                     (3)

This removes the previous N_y=o(y) hypothesis in favor of
a local-time condition. It does not imply that this new
condition holds on all actual trajectories. A path with
many low-height events or with many down intervals occupying
different levels may have a small L_y despite large N_y.
Conversely repeated long overlaps may make L_y large even
when N_y is sublinear. This is an alternative criterion,
not a logical weakening of every aspect of the old one.

One can also use a truncated local-time tail, for integer K>=1:

    P_any <<_C (K+1)/log y
          + (2/y) sum_(h>=h0) (D_y(h)-K)_+.                      (4)

Indeed a D <= K part contributes at most K sum a_y and
the excess costs at most 2/y per unit. This may apply even
if the second moment is large because of a small number of
highly occupied levels. For G_y<=Cy, for instance,
max D_y(h)=o(log y) on the high region suffices by (1),(3).
If G_y=0 the formulas include the terminal opportunity.

## 4. A localized small-label condition

Now assume G_y<=Cy. Use the translated interval prime
upper bound from 7021cc1 on the downward intervals for
labels p>z. The total charge of those intervals is
O_C(1/log(2+z)) because their total length is <=Cy/2.
For p<=z retain only their high-height part, of total
length

    S_z=sum_(i:p_i<=z) |I_i intersect [h0,infty)|.

Using a_y<=2/y for the remaining charge yields

    P_any <<_C 1/log y + 1/log(2+z) + S_z/y.                    (5)

This removes every small-label event which stays below
h0. For fixed z an event counted by S_z must have
h_i>=h0-2z since its firing height k_i=h_i+w_i>=h0
and w_i<=2p_i<=2z. Thus only small-label activity
already in a high-deficit region needs to be controlled.
No restriction on the number of low-deficit excursions
or on the total gain in low-height small events is
imposed by (5), beyond the assumed total gain cap.

For the full old period, tightness of G_y/y together with
S_z/y->0 in probability for every fixed z>=3 suffices for
P(new label selected)=o(1). First restrict G_y<=Cy,
then use fixed large z and the stated convergence.
The conclusion follows by bounding all exceptional
probabilities by 1. This is less restrictive than
requiring N_y/y->0 under the same tightness, because
S_z<=(z-1)N_y/2. It is not proved here that S_z has
the required convergence.

## 5. A general one-step criterion for quadratic displacement

Take A_y=all odd primes <y, and add all primes in [y,2y].
The CRT coupling of full periods remains exact.

Suppose along a sequence y->infinity the old-period
distribution satisfies

    G_y/y^2 ->0 in probability,
    Hmax/y is tight,
    L_y/(y log y) ->0 in probability.                          (6)

The first assumption is weaker than the earlier linear
gain tightness. The second is a separate height constraint:
it does not follow from the first. The third concerns
only the high region. By (3), after restricting Hmax<=Cy,
the conditional activation probability tends to zero in
probability, hence in mean since it is bounded by 1.
Taking C large gives P(new band activated)=o(1).

On unchanged trajectories G_enlarged=G_y. Therefore

    E[min(G_enlarged,y^2)] <= E[min(G_y,y^2)]
                             + y^2 P(activation)
                            =o(y^2).                           (7)

The third condition in (6) can instead be replaced by
the high-occupation tail condition: for every epsilon>0,

    lim_(K->infty) limsup_(y->infty)
       Pr(sum_(h>=h0)(D_y(h)-K)_+ > epsilon*y)=0,

using (4) and height tightness. Alternatively under
G_y/y tight, (5) supplies (7) through S_z.

These are conditional one-step implications, not a
recursion establishing any of their hypotheses.
In particular (7) controls only a truncated mean and
does not imply linear displacement or height tightness
at the next scale. None of these period estimates
automatically transfers to the physical interval R~y^2.

## 6. Unconditional joint avoidance of used prime labels

This is a separate consequence of the deletion method
in 56614c0. Work over the entire canonical period for
A_y, and let I_p be the indicator that p is selected
at least once, for 5<=p<y. For ANY subset B of these
primes, delete B. The remaining period is coprime to
every p in B and divisible by 6. Fix one residue of
this smaller period, and lift it to the full period.
If the enlarged trajectory uses NONE of B, it
coincides step by step with the deleted trajectory.
Its terminal must have both neighbors nondivisible by
every p in B. Each p forbids exactly two lift residues;
CRT gives the exact necessary avoidance bound

    Pr(I_p=0 for all p in B) <= product_(p in B)(1-2/p).        (8)

Intermediate preemption can shrink this set further.
No independence of the actual indicators I_p follows.
This argument works for omitted labels smaller than
other retained labels: if they never win a clock,
the trajectories coincide.

For arbitrary nonnegative real weights c_p and t>=0,
expand the product of the nonnegative expressions

    exp(-t c_p I_p)=exp(-t c_p)
                 +(1-exp(-t c_p)) 1_(I_p=0).

Every term is bounded by (8). Thus

    E exp(-t sum_p c_p I_p)
       <= product_p [1-(2/p)(1-exp(-t c_p))].                   (9)

This is lower-tail Laplace domination by independent
Bernoulli variables of parameters 2/p, NOT an upper-tail
domination or an independence statement.

For c_p=1, set K_y=sum_p I_p and
mu=2 sum_(5<=p<y)1/p=2 loglog y+O(1).
For fixed 0<delta<1, Markov applied to exp(-t K_y)
with t=-log(1-delta) gives

    Pr(K_y <= (1-delta)mu)
      <= exp(-mu[delta+(1-delta)log(1-delta)]).                  (10)

Here N_y>=K_y. Hence on density-one roots of the full
period at least (2-o(1)) loglog y distinct labels are
used, in the sense that for every fixed delta>0 the
corresponding lower threshold holds with probability
tending to 1. This complements the earlier mean lower
bound. It is far below the desired sublinear upper
bound on N_y, and does not establish such an upper bound.

For c_p=p-1, G_y>=sum c_p I_p, so (9) also bounds
E exp(-t G_y) from above. Directly in (8), omit
all primes greater than y^alpha+1, fixed 0<alpha<1.
If G_y<=y^alpha none can occur. Mertens' product gives

    limsup Pr(G_y<=y^alpha) <= alpha^2.                         (11)

The product ratio is asymptotic to
(log(y^alpha+1)/log y)^2 since the corrections to
Mertens factors form a convergent product.
This strengthens the mean displacement lower bound
to a distributional constraint. In particular G_y
cannot be polylogarithmic on a positive fraction of
the full-period roots (apply (11) for arbitrarily small
fixed alpha). It is compatible with G_y=O(y) in mean
or in probability. No local interval equidistribution
or twin-prime lower bound is obtained.

## 7. Executed finite diagnostic

Source research/min_local_restricted_height_occupation_audit.mjs
commit a450153a693a7e970d38d595dda0fe0174ff12c2,
blob 68f7c9d71cb457a06aa82c73b9e80796bf601f90.
Reproduction: node research/min_local_restricted_height_occupation_audit.mjs.
Actual ECMAScript tool runtime execution, exact remote readback,
and re-execution with identical output. No Node or Lean process.

Five complete old periods with y=7,11,13,17,19; three local
samples of 2,000 roots each with y=127,503,997. Same sample
domain as 7021cc1, censoring if G>64y (none censored).
For the tested odd y, floor((y-1)/2)=ceil((y-1)/2).
Use exact integer occupation arrays and independent pairwise
interval-overlap sums, checking (1). Evaluate the coarea
charge, exact conditional residue-set probabilities, the
Cauchy-Schwarz bound with exact sum a_y^2, and (4) with
K=1,2,4,8,16 and exact maximum a_y.
Check localized small-label charge for p<=11. No numerical
asymptotic constant inferred.

    kind      y    mean N  mean high down events  mean L_y  L_y mean/(y log y)
    period    7      .800          .800            1.600          .11746
    period   11     1.529         1.400            3.171          .12024
    period   13     2.373         1.931            5.775          .17320
    period   17     2.897         2.083            7.698          .15983
    period   19     3.633         2.563           10.771          .19252
    local   127     9.686         2.469           42.647          .06932
    local   503    26.087         5.292          234.907          .07508
    local   997    30.718         2.430          144.585          .02100

Mean S_11 in the three local samples:
3.137, 6.0885, 2.792, respectively. Number of roots
without any high down interval:1326,1310,1441;
largest observed high-height local time:9,10,10.
These are finite observations, not proofs of tightness
or occupation bounds. Local conditional lift
probabilities remain distinct from actual local frequencies.

187030 root/cutoff incidences, 782136 old events,
5363128 quiet ticks, 187030 occupation length checks,
187030 pair-overlap checks, 187030 energy checks,
935150 truncated local-time bounds, 187030 localized
small-label charge checks. No failed assertions.
For the five full old periods, enumerate EVERY subset
of p>=5 and compare the empirical avoidance counts
to the exact product in (8): 62 subset checks.
Also check (9) for c_p=1 and p-1 at t=1/8,1/2,1,2:
40 checks. Probability arithmetic is floating point
with tolerances; occupation and overlap counts integer.
The lower-tail asymptotics are paper deductions.

## 8. Remaining work

The event-count hypothesis has not been established.
The height occupation method instead allows a
different target, namely control of repeated
high-deficit downward crossings, or small-label
gain at those heights. It has the advantage of
ignoring the potentially extensive low-height
portion of the path. The exact support deletion
bound also rules out overly small typical gains in
the full period. Neither argument bounds the full
old displacement, nor transfers full-period
probabilities to a short interval with T comparable
to sqrt R. No twin-infinitude proof or change to
canonical Lean targets or sibling branches.
