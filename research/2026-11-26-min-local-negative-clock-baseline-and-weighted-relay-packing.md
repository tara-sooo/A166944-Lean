# Negative MIN: clock-gap CRT and individual-baseline relay packing

2026-11-26 JST. Continuation of cc6280720ea3c7bc39fdc9bc14d4caeb35aae11c.
Refine the stopped-prefix multiband certificate by imposing both
spatial and clock-gap congruences, and by retaining individual
known contributions rather than subtracting their aggregate from
a zero-baseline packing bound. Exact finite inequalities and audits.
No asymptotic twin-infinitude result or Lean verification.

## 1. Clock-gap capacity

Use the stopped forward prefix and band relays of cc62807, with
actual completed events in decreasing remaining distance a.
An ordered distinct-label key is g=(level,p,r,e,f), p!=r.
The first event has firing time n, the second n+tau, with
tau>0. Source sides e,f belong to {-1,+1}. Define

    c(p,-1)=0, c(p,+1)=p+2.

Then

    n=c(p,e) mod 2p,
    n+tau=c(r,f) mod 2r.

For a fixed tau the congruences fix one class modulo 2pr
when consistent. The consistency condition is the parity
tau=equality_of_sides?0:1 mod2. More explicitly, same
sides give positive even gaps, opposite sides odd gaps.
Thus if the span of first firing times in key g is d_time,
at most

    c_time=floor(d_time/(2pr))+1

occurrences can have any fixed gap tau. This is independent
of the spatial capacity c_space from cc62807. It also holds
for any fixed tau modulo 2r, although the weaker fixed-value
bound suffices here. First firing times are strictly increasing.

For a same-label relay, p=r, the gap is congruent to
c(p,f)-c(p,e) mod 2p, and is positive. In addition
its spatial gain is at least p-1 as before.

Write E_I=H_I+g_I for the full relay gain, its known
gain from labels >=t, and its unknown lower-label gain.
Likewise write V_I=K_I+u_I for the full relay wait,
its known wait from labels >=t, and its lower-label wait.
If w_r is the actual wait of the second endpoint,
the clock gap is exactly

    tau_I=w_r+K_I+u_I = b_I+u_I.

Here b_I is a known baseline when the marked waits and
band word are supplied. The identity follows because
the first firing has already completed, and the interval
to the second firing includes the second wait. It does
not include the first wait. In every relay u_I<=3g_I,
and g_I is a nonnegative even integer. Neither b_I nor
H_I is assumed constant across occurrences of a key.

## 2. Packing with individual baselines

Let n observations x_i have x_i>=b_i, with x_i drawn
from the lattice of integers x>=m, x=par mod 2, and
at most c observations at any one value. For the spatial
gain use m=0,par=0. For a positive clock gap use
m=1,par=1 for odd gaps or m=2,par=0 for even gaps.

Round each b_i upwards to the first lattice value at
least b_i and m, then sort these rounded baselines
beta_1<=...<=beta_n. Define

    t_i = beta_i,                         i<=c,
    t_i = max(beta_i,t_(i-c)+2),           i>c.

The sequence is nondecreasing, obeys the lattice and
capacity, and is componentwise no larger than the
sorted values of any feasible observation list.
Indeed the ith sorted observation must be at least
beta_i (otherwise its n-i+1 larger-baseline observations
cannot all fit), and must be at least two more than
the (i-c)th observation. Induction proves minimality.
Matching the sorted t_i to sorted baselines gives a
feasible relaxed assignment, so the exact minimum of
the total excess is

    P(b,c,par,m)=sum_i t_i-sum_i b_i.                 (1)

It is nonnegative. This is an arithmetic relaxation,
not an assertion of realizability by a MIN trajectory.
The earlier packing with all baselines zero followed
by subtraction of their sum and positive part is
always a lower bound for (1), and may be strictly weaker.

For any subset S of occurrences of a distinct key,
use the group's valid capacities (or smaller capacities
recomputed on S). Then

    sum_(I in S) g_I >= P_space(S)
      := P((H_I),c_space,0,0),

    sum_(I in S) u_I >= P_time(S)
      := P((b_I),c_time,par,m).

Since u_I<=3g_I and sum g_I is even, the combined
lower bound for this subset is

    B(S)=max(P_space(S), 2 ceil(P_time(S)/6))
       <= sum_(I in S) g_I.                         (2)

The max, rather than the sum, is essential: both
certificates may charge the same low event.
For same-label relays use the maximum of
(p-1-H_I)_+ and 2 ceil(u_min/6), where u_min is the
distance from b_I to the smallest positive clock gap
>=b_I in the required residue mod 2p.

A single distinct-label occurrence can already have
a positive time bound: if b_I has the wrong parity,
at least one additional low tick is required and hence
at least two units of low gain. This elementary parity
constraint is not a new asymptotic CRT saving. The
new CRT part is the cap on repeated equal gaps,
which may force extra ticks beyond parity rounding.

## 3. Weighted integration and multiband budget

For any feasible weights lambda_I>=0 as in cc62807
(sum of enclosing weights <=1 at each low event),
let 0<v_1<...<v_s be the distinct positive weights
within a key and v_0=0. Define S_j={I:lambda_I>=v_j}.
Layer decomposition is the exact identity

    sum_I lambda_I g_I
      =sum_j (v_j-v_(j-1)) sum_(I in S_j) g_I.

It follows from (2) that each group contributes
the nonnegative lower certificate

    C_g=sum_j (v_j-v_(j-1)) B(S_j).

Sum C_g over distinct keys and add the same-label
individual rounded maximum multiplied by lambda_I.
The total C_clock-space satisfies

    C_clock-space <= G_<t.

This combines arbitrary unequal weights, individual
baselines, both CRT capacities, integrality and parity.
It dominates applying the two baseline-aware subset
bounds separately then taking their maximum per group.
It also dominates the zero-baseline packing certificate
of cc62807: at each weight threshold the baseline-aware
minimum is at least the positive part of the zero-
baseline minimum minus the subset baseline sum, and
summing positive parts is at least the positive part
of the summed differences. With unit weights this
is exactly the comparison of unweighted certificates.

The previous pointwise capacity condition guarantees
no low event is double charged, even across bands.
For the stopped non-twin prefix, after dropping the
half-crossing event if present, the necessary budget
remains

    G_hi + C_clock-space < A/2,
    W' >= A/4-O(sqrt A).

The clock certificate uses the actual marked waits,
known marked gains and source/time spans. It supplies
a computable lower bound on low gain given these data,
not a bound on how many groups or waits can occur.
No conclusion that these two inequalities conflict
has been obtained. In particular singleton keys
often produce only the parity-level bound of two,
and for long paths with abundant distinct keys the
certificate can remain small relative to A.

## 4. Executed audit

Source research/min_local_negative_clock_baseline_packing_audit.mjs,
commit 16dea271547cef2711e2cc28c5b9ac9906d3f67d,
blob 776cc95f599c04f8016844e9d6bf5cbd9f69a9fd.
Executed in the ECMAScript research runtime, fetched
at the exact commit and re-executed with identical
output. Reproduce with
node research/min_local_negative_clock_baseline_packing_audit.mjs
No separate Node or Lean invocation.

800 initial-distance/phase controls: four slabs
R=10000,40000,120000,250000, 50 roots per phase
per slab, canonical negative phase and noncanonical
phases 0,17,floor(A/5). Stop canonical prefixes
before tick zero, split at twin sources, retain
contiguous non-twin event blocks. Five base thresholds
5,7,11,17,23 per block. These are local finite controls,
not a distribution of hypothetical long non-twin
canonical prefixes.

    event evaluations                  17250
    contiguous blocks                    756
    block/threshold controls            3780
    relay incidences                    9629
    distinct-key groups                 8577
    repeated-key groups                  291
    clock congruence checks             9629
    spatial congruence checks           8956
    capacity checks                    17154
    weighted group checks               8577
    rounded subset checks               6383
    global certificate checks           3780

All assertions passed. Clock lower bound positive
in 3652 group incidences, spatial baseline-aware
lower bound positive in 24. The clock bound is
strictly stronger than its zero-baseline/subtraction
counterpart in 3518 cases, including 95 repeated
groups. The spatial baseline-aware bound did not
strictly improve its old counterpart in these controls.
The clock bound divided by three exceeds the spatial
bound in 3639 group incidences. Importantly, only ONE
group has a clock bound strictly beyond its own
sum of parity-rounding costs (also a repeated group).
Thus most numerical gain is the elementary parity
constraint, not a substantial new packing effect.
The largest unweighted lower-wait bound is 4 ticks.
Integer rounding and layerwise maximum increase
the previous fractional combined certificate in
1569 block/threshold controls; largest final
certificate is 54 units of gain. No macroscopic
budget contradiction observed.

Additionally 120 synthetic small packing instances
with c=1..3,n=1..5, both parities and four baseline
patterns were exhaustively checked against a search
over admissible lattice slots up to 20. The search
contains the greedy optimum in these small instances.
80 instances strictly improve on zero-baseline
packing followed by aggregate subtraction. All
minima agree. These are arithmetic relaxations,
not asserted to be actual clock trajectories.

## 5. Remaining problem

This improves the finite multiband budget and shows
the precise role of time-gap CRT. The observed
improvement is mostly parity-level; to obtain a
large-A contradiction one still needs an independent
mechanism forcing many repeated keys with binding
capacity, or a stronger way to couple time-gap
residues to the known label gains and clock waits.
The main stopped-prefix target remains an unbounded
sequence with liminf W(A)/A<1/4. No twin-infinitude
proof or Lean verification. No changes to canonical
Lean targets or sibling branches.
