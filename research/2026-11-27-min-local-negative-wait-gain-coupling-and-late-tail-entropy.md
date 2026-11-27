# Negative MIN: time-weighted gain coupling, repeat occupation, and late-tail entropy

2026-11-27 JST. Continuation of 1d0e2c5147fd4cc32908062da6f32a573798d10a.
The user set the final objective to an unconditional proof of twin infinitude,
independent verification and Lean formalization, with continued research
rather than stopping after an isolated lemma. This installment pursues the
actual all-root soft frontier in three connected steps: an exponential
coupling of roughness deficit to the outgoing event label, a replacement of
the event-count hypothesis by repeat-gain occupation and terminal waiting,
and a multiscale entropy decomposition with reverse codes. A further
occupation-packing certificate permits nonuniform fiber representatives.
The new inequalities below are paper-level deductions; the required
asymptotic bounds, twin proof and Lean verification are still missing.

## 1. Setup and a correction to the abbreviated sufficient condition

Use the soft frontier of 1d0e2c5. Canonical roots A in [R,2R], 6|A.
S=sqrt(2R+1), T=ceil S, W=6 floor(T/6). A window of roots with
left endpoint l has latest birth n0=3-l/2 and common end n0+T.
Each path starts at its own birth 3-A/2, with h=3.
G<=3T+6 by nonnegative height. All positions lie in the expanded
slab used for the weighted non-twin upper sieve.

Let q(a) be the smaller least prime factor of a-1,a+1, and put

    L=log S,
    d(a)=log(S/min(q(a),S)),
    C_R(d)=2 log(L/(L-d)) + F(d),
    F(d)=log(1+d)+2 log(1+log(1+d)),
    w(a)=exp(-C_R(d(a))).

The previously derived non-twin weighted capacity is O(R/log^3 R).
Let Y(A) be the final synchronized position, X_u(A) the position
at common offset u in its own window, 0<=u<T, and
L_end=H(A|Y). The earlier synchronization proof gives
H(A|X_u)<=L_end+log B0 with B0=ceil((3T+6)/W)+2=O(1).
Hence an upper bound on the mean (A,u) roughness penalty,
together with L_end, yields a sufficient all-root soft criterion.

The abbreviated condition stated after 1d0e2c5,
liminf [L_end+log(1+M_R)]/loglog R<3, needs a restriction on
M_R=E log(1+N_event) if it is to follow just from that note's
bound. The omitted chord term k_R(1+log 2+M_R) may contribute
at leading order when M_R is comparable to log R. For example
M_R=o(log R) suffices to make that term subleading; otherwise
use the full inequality (10) in 1d0e2c5, with its chord term.
The two-condition version with log(1+M_R)=o(loglog R) is valid.
The present approach will avoid that count hypothesis entirely.

## 2. Time-weighted label/roughness coupling

Partition the T observed post-tick states into stationary segments
of lengths ell_i>0. For a segment whose outgoing jump is completed
by the common retirement, give it the outgoing odd prime p_i.
For the terminal segment (no outgoing completed jump), assign the
proxy p_i=S, not an actual prime. The terminal segment may have
zero observed length and is then omitted. Observe that for a
nonterminal segment q(a_i)<=p_i, while in every segment
ell_i<=2q(a_i) by the periodic clock of the least eligible label.
Let r_i=log(S/min(p_i,S)); terminal r_i=0. Thus d_i>=r_i.

For a fixed root and t>=0, the event d_i-r_i>t implies
q(a_i)<min(p_i,S) exp(-t). Summing ell_i<=2q over these segments,
and using 2p_i<=3(p_i-1) for odd primes >=3, gives

    Pr_U(d-r>t | A)
       <= min(1, [(3G+2S)/T] exp(-t)).              (1)

There is only one terminal interval, accounting for 2S in
the numerator. Here G is gain over the entire synchronized
path, including events before the observation window, so it
dominates the gain on completed observed segments. The
uniform cap G<=3T+6 makes the bracket O(1). Integrating (1),

    E_U(d-r | A) <= 1+log max(1,(3G+2S)/T)=O(1).

The derivative of C_R on [0,L-log 3] is
2/(L-d)+F'(d)<=2/log 3+3, uniformly in R. Therefore

    0 <= E_(A,U) C_R(d)-E_(A,U) C_R(r) <= O(1).    (2)

Both statements are unconditional on actual integer slabs.
In particular a rare large discrepancy q<<p does not spoil
the time-weighted penalty at logarithmic order.

Define the outgoing-label penalty Q_R=E_(A,U) C_R(r).
A sufficient condition for twin infinitude is now

    liminf_(R->infinity) [L_end+Q_R]/loglog R < 3.   (3)

Proof: (2) gives a common offset with mean actual penalty
<=Q_R+O(1); add the synchronization entropy O(1) and use the
soft frontier. No mean event-count bound or gain-saving
condition is required in (3). No asymptotic bound for Q_R or
L_end has yet been obtained.

Another deterministic improvement: write pi_i=ell_i/T.
Then d_i<=log(2S/T)+log(1/pi_i), so

    E_U d | A <= log(2S/T)+H(pi_i)
                           <= log 2+log(1+N_event).

The time-partition entropy H(pi_i), rather than log number
of events, suffices in the concavity bound of 1d0e2c5.
This may be considerably smaller when there are many short
events but a few very long waits. It does not give an
unconditional bounded time-partition entropy.

## 3. A repeat-occupation coefficient with no event-count hypothesis

Fix 0<epsilon<1/4 and Y0=R^epsilon.
Define theta_R as the mean fraction of observed time in the
terminal stationary segment. Put beta_R=1-theta_R.
Let sigma_R be the fraction of observed time in nonterminal
segments with outgoing label p<Y0, and sigma_rep,R the same
fraction restricted to labels previously used on that root.
These are fractions under uniform (A,U), not event counts.
For p>=Y0 the proxy penalty is at most
(1+o(1))loglog R, since log p_* is comparable to log R and
F(log S)=loglog R+O(logloglog R).
For 3<=p<Y0 the proxy penalty is at most
(3+o(1))loglog R. Terminal proxy cost is zero. The error
terms are uniform in each class with fixed epsilon. Hence

    Q_R/loglog R <= beta_R+2 sigma_R+o(1).         (4)

On any path the total first-use gain for p<Y0 is bounded
by sum_(p<Y0)(p-1)<=Y0^2=o(T), even without a prime estimate.
Each such outgoing wait has length <=2p<=3(p-1).
Consequently first-use occupation below Y0 is o(1),
uniformly over all roots:

    sigma_R = sigma_rep,R+o(1).

If zeta_R=E[G_repeat,p<Y0]/T (including all completed
events before retirement, even before the observation window),
then sigma_rep,R<=3 zeta_R. Thus either of the following
strict liminf inequalities is sufficient:

    L_end/loglog R + 1-theta_R + 2 sigma_rep,R < 3,
    L_end/loglog R + 1-theta_R + 6 zeta_R < 3.      (5)

Here '<3' means liminf strictly below 3.
For instance, if L_end<=(2+o(1))loglog R, a fixed positive
margin theta_R-2 sigma_rep,R (or theta_R-6 zeta_R)
on unbounded slabs suffices. Unlike the earlier M_R
condition this does not require any upper bound on the
number of small jumps; only the time or gain they consume.
It also need not show that repeated small-label gain is o(T).
The new targets are the endpoint entropy and a weighted
difference of terminal time and small-repeat time.

A more general split uses Y1=S exp(-(log R)^alpha) with
0<alpha<1. For labels >=Y1 the proxy penalty is at most
(alpha+o(1))loglog R, since log p_*/log S tends to one.
For labels in [R^epsilon,Y1) use coefficient 1,
and below R^epsilon coefficient 3. If tau_R is the
time fraction of nonterminal labels >=Y1, this gives

    Q_R/loglog R <= beta_R+2 sigma_rep,R
                              -(1-alpha)tau_R+o(1).

This gives an additional saving from completed long waits,
not only the terminal wait. It does not assert lower
bounds for tau_R or theta_R. These reductions use actual
time-weighted outgoing labels, not an independent CRT law.

## 4. Asynchronous early-prefix and late-tail entropy

For any deterministic intermediate position X(A),
even with an A-dependent absolute clock, the chain rule gives

    H(A|Y) <= H(A|X)+H(X|Y).                        (6)

No synchronization is needed for this inequality, nor is it
required that Y be a deterministic function of X alone.
For the early elapsed cutoff u=floor((log R)^a), fixed a>0,
take X as the position after u ticks from each root's own birth.
The gain cap 2u+6 gives at most 1+floor((2u+6)/6) canonical
roots per X. For sufficiently large R this cutoff precedes
retirement, and

    H(A|X) <= a loglog R+O(1).                      (7)

This splits off an initial low-scale portion with an
unconditional entropy bound, without charging log(T/u)
for its different clock windows. It remains to bound the
entropy H(X|Y) of the later displacement, not merely its size.

For a common synchronized offset u instead, let J be window
index. Then Y is a deterministic function of (X,J), and

    H(A|Y,J)-H(A|X,J)=H(X|Y,J).

At most B0 possible windows per final position give an
additional O(1) to the full entropy. This identity applies
to tail intervals of any length and to dyadic stages.

Choose a label cutoff y>=3 on the tail. Read the jumps in
reverse, grouping all labels <=y into half-gain gaps
l_0,...,l_k around k high labels p>y. The factor-rank code of
095053c now reconstructs X, not A: starting at Y add 2l_0,
select p among the odd factors of the target x or x-2,
add p-1, then add 2l_1 and repeat. Every actual high p
occurs on the candidate list, including the gain cap.
For a given Y and complete codeword the decoded X is
unique, even if the early absolute clock was asynchronous.
Conditional entropy H(X|Y) is bounded by the mean code
length, using any probability distribution pi for the
gap vector, possibly depending on Y mod a fixed integer.
It is permissible that more than one word decodes to the
same X; the total word Kraft mass is at most one.

For synchronized tails there is a further clock filter.
Given the window, the tail interval (n_start,n_end] is
known. Maintain an upper bound U on the absolute time
of the next reverse event, initially n_end. When a
positive low gap is decoded, subtract at least one from
U (there was at least one low event). For target x, a
candidate p dividing x has minus clock c=0 mod 2p;
p dividing x-2 has plus clock c=p+2 mod 2p. The classes
are disjoint for odd p. Keep only candidates whose
latest clock n_p=U-((U-c) mod 2p) satisfies

    n_p>n_start,  n_p+x/2>=0.

After selecting p, set U=n_p-1. By induction the actual
clock of every reversed high event is no greater than
its maintained upper bound, so the actual label is
never excluded. No need to encode the actual clock.
This reduces candidate rank cost with a decoder
that still has total probability at most one.
A winner-priority test could prune further; the audit
only uses this clock filter, not the exact prior winner.

Using kbar and lbar as means of k and sum l_i,
the general geometric gap bound of 095053c becomes

    H(X|Y) <= g(kbar)+(1+kbar)g(lbar/(1+kbar))
                          +kbar log d_y,

where g(s)=(1+s)log(1+s)-s log s and
d_y=max(1,2 floor(log(2R)/log y)).
For example y=cT, kbar=O_c(1) deterministically.
If lbar<=log^(b+o(1)) R then this bound is
<=b(1+kbar)loglog R+o(loglog R).
Combine with (7) and (4) to obtain a fully explicit
conditional early/late criterion without separately
bounding the number of small events. The observed
tail low gains are not small enough to establish this
asymptotically. No new entropy upper coefficient is
claimed. The synchronized clock-filter code is
numerically much weaker than actual conditional
entropy, and the unpruned all-low displacement code
was best in every compared finite cut.

## 5. Occupation-packing support, beyond the uniform entropy average

For each window j and final position y let m_j(y)
be its final root multiplicity. Given any nonnegative
weights k_A with sum_(A in final fiber (j,y)) k_A<=1,
and an observed position a at common offset u,
the sum of k_A for roots in j at a is <=1.
They all have the same final y within j by determinism.
Write ell_A(a) for number of observed ticks at a and

    b_j(a)=sum_(A in j) k_A ell_A(a)/T,
    b(a)=sum_j b_j(a).

Thus 0<=b_j(a)<=1, and only at most B0 windows can
reach a, by the gain cap. For the union of visited
positions, whether or not they occur at a common
time, one obtains

    sum_(visited a) w(a)
      >= sum_a w(a) min(1,b(a))
      >= (1/B0) sum_A k_A (sum_u w(X_u(A))/T).     (8)

The clipped version can be much stronger than losing
the full B0 factor. The standard uniform choice is
k_A=1/m_j(Y(A)). Alternatively choose the single
representative maximizing its mean occupation weight
in each final fiber, with weight 1 and all other
roots weight 0; this satisfies the same inequality.
The representative choice maximizes the *unclipped*
right-hand sum for fixed fibers, not necessarily the
clipped sum. Any computable reverse code with
per-fiber total weight <=1 can replace the exact
multiplicity. If the right side or clipped certificate
is >>R/log^3 R (ratio tending to infinity) on unbounded
slabs, the non-twin capacity gives twin infinitude.
This can exploit well-spread subcohorts without first
proving uniform-average entropy of all roots.

There is a separate terminal-only certificate without
a window ambiguity factor. Let theta_A be terminal
time fraction of root A and m(Y) the final multiplicity
across the whole slab. Since theta_A<=1,

    sum_(occupied final y) w(y)
       >= sum_A theta_A w(Y(A))/m(Y(A))
       >= sum_A theta_A w_q(max(3,T theta_A/2))/m(Y(A)). (9)

Here w_q(q) denotes the increasing weight as a function
of q, capped at S as in section 1. The last inequality
uses the least-factor clock bound in the terminal
segment. It holds even when theta_A=0. This last
certificate uses only terminal durations and final
fiber weights, not the least prime factors at the
endpoints. The bound is not asymptotically established;
in the largest finite control it does not exceed the
finite non-twin capacity, unlike the certificate
using actual terminal roughness.

## 6. Executed audits and readback

All three scripts were executed in the ECMAScript
research runtime, committed to the research branch,
fetched from their exact remote commits and re-executed
with matching output. The first combined replay timed
out; each individual replay succeeded. Reproduce
with node; no separate Node/Lean invocation.

A. research/min_local_negative_wait_gain_coupling_audit.mjs
commit 24f1b47dae8d51611f65420b67c225060896aa06
blob e99b9084d06975baf62c6bdef60b2bf26fe428fc

Actual slabs R=12000,48000,192000,480000,1000000,2000000,
all canonical roots, synchronized T=ceil S.
Check per-root coupling tails at eight t values, mean
deficit, Lipschitz penalty, duration entropy and
small-gain occupation thresholds.
    roots                         622004
    completed events            17010526
    occupied segments            9730511
    tail checks                  4976032
    per-root penalty checks       622004
    small-gain threshold checks  4352027

    R         terminal fraction   mean H(wait)  mean d-r  actual penalty  proxy penalty
      12000         .570528          1.05693       .089811     1.65006       1.47331
      48000         .610472           .96706       .063265     1.39060       1.27020
     192000         .646773           .91264       .066661     1.24696       1.11867
     480000         .687030           .81529       .057356     1.07266        .96197
    1000000         .716218           .74136       .049077      .94649        .85241
    2000000         .729042           .69278       .048069      .86725        .77412

At R=2000000 mean log(1+N_event)=2.97834,
mean deficit=.571034, proxy deficit=.522965.
Mean L_end+Q_R=4.763138 and actual mean score
L_end+E C_R(d)=4.856270. The empirical tail
Pr(d-r>1)=.011599, >2=.001845, >4=.00008387.
These are observed finite values; the proved
uniform error bound is much larger.
All checks passed.

B. research/min_local_negative_late_tail_factor_entropy_audit.mjs
commit 22e25d4fdf2458ea7d113489d3c8392cd9c3ba1b
blob 629c72ce793c9c0f88198e86da848adacc84ab8c

Same six actual slabs. Common-offset cuts and
asynchronous early elapsed cuts floor(log^a R),
a=1,1.5,2 (use fewer common cuts at two largest
R). For each compare spatial gap-factor codes,
clock-pruned codes where synchronized, empirical
gap-vector distributions conditional on y mod210,
and exact conditional entropy. Deduplicate
actual words for per-endpoint Kraft checks.
    roots                      622004
    completed events         17010526
    tail controls             2854028
    reverse decodes           4000000
    factor rank checks       19762952
    clock pin checks           552392
    Kraft checks               783195
    entropy checks                216

At R=2000000, common offset 1000:
within-window early L=3.511587, final=3.577359,
actual additional entropy=.065772, even though
mean tail events=5.069 and tail gain=355.295.
For cutoff y=250 the rank cost reduces from
.142507 to .094940 by clock pruning, total code
1.927955 to 1.880389; all-low displacement
code 1.733380 is still better. These are
empirical code lengths, not proved distribution
estimates. At early elapsed cuts 14,55,210:
    early L       .624306    1.420789    2.330786
    H(X|Y)       3.369562    2.579104    1.672953
    chain sum    3.993868    3.999892    4.003739
Actual L_end=3.989016. All-low code at t=210
has mean length 4.539623, not competitive with
actual tail entropy. No entropy asymptotic
contraction inferred from these finite tests.

C. research/min_local_negative_occupation_packing_repeat_gain_audit.mjs
commit 6c00c81e0f6bf3ee48b57faf7349d56d158fc0bd
blob e0a9c3ff0374f8092d2203fa64f3f879dfc8e7f7

Same slabs, actual per-fiber uniform weights
and representative maximizing occupation
weight, clipped all-window certificate,
terminal-only certificates, and small first
and repeat gains for epsilon=1/8,1/6,1/5,.24.
    roots                      622004
    completed events         17010526
    observed segments         9730511
    capacity checks            875029
    first-gain checks          2488016

At R=2000000, 333333 roots:
theta=.729042, beta=.270958.
For epsilon=1/8, rounded cutoff Y0=7,
small time=.014757, normalized first gain=.002725,
repeat gain=.018471. Thus beta+2 sigma=.300472
and beta+6(first+repeat)=.398132. These are
finite diagnostics of (5), not an asymptotic
bound (the finite penalty contains substantial
lower-order terms). At epsilon=.2, Y0=19,
small time=.030224, repeat gain=.039283.
    full visited weighted support      14352.988296
    uniform clipped window certificate 12611.990568
    representative clipped certificate12701.419453
    terminal actual weight certificate11406.842655
    terminal duration-only certificate 2315.192799
    finite non-twin capacity            3501.210442
The finite integers already contain twins.
The first three certificates exceed their
finite bad capacity; the final duration-only
one does not. No claim of asymptotic excess.
All assertions passed.

## 7. Remaining central estimates

The new target (5) removes both selection and an
event-count upper bound from the soft frontier;
only the full entropy coefficient and the
terminal/repeated-small-label time balance
are needed. The late-tail chain demonstrates
that an initial polylog elapsed cutoff has a
deterministic entropy budget, but the available
factor-rank codes do not yet control the late
tail. The occupation-packing inequality allows
replacing uniform entropy by a weighted
inverse-fiber estimate if that proves easier.
Actual asymptotic upper bounds, in particular
on low-prime repeats and late-tail ambiguity,
remain open. The user's final target is not
achieved: no unconditional proof of twin
infinitude or Lean formalization. No changes
to canonical Lean targets, sibling branches,
or Context files.
