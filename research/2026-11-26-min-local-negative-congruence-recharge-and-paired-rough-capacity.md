# Negative MIN: congruence recharge profiles and paired rough capacity

2026-11-26 JST. Continuation of 3d99a80c0c1090676830c102b09f85f11d00c62e.
Refine the finite-alphabet absorption potential by label residue,
and derive a four-linear-form upper sieve for time carried by
jumps with rough endpoints on both sides. The latter yields a
conditional fourth-power logarithmic support obstruction on
actual local inverse paths. Paper deductions and executed finite
diagnostics; no Lean verification or twin-infinitude proof.

## 1. Congruence-specific recharge profiles

Use R_z(a,k), H_z, Q=2 prod_(3<=l<=z, l prime) l from 3d99a80.
For any unit residue r modulo Q, define the following finite
upper profile on even a mod Q and clock phases k mod Q:

    D_z(r)=max(0, max [R_z(a-r+1,k)-R_z(a,k)]),

where the inner maximum is restricted to phases at which
no small clock fires from a at tick -k. Every actual selected
p>z has this property, by least-prime priority. Its spatial
gain p-1 has the same effect modulo Q as r-1 for r=p mod Q.
Therefore its exact signed recharge delta from the previous
note satisfies delta<=D_z(r). A refinement restricts the
maximization to either parity of k and either rough or
nonrough sources a. All four resulting upper profiles may
be used simultaneously. There is no requirement that every
relaxed pair (a,k) can be realized by an actual large clock;
including unrealizable pairs only enlarges the maximum.

The exact active-time telescope gives

    T_z <= H_z-R_z(b,1) + sum_(large jumps) D_z(p mod Q).

One may replace each profile by the minimum of the applicable
parity and source-specific profiles. D_z(1)=0. Direct finite
enumeration gives H_3=7 and D_3(5)=6; for z=5:

    r     1   7  11  13  17  19  23  29
    D     0  16  18  15  18  17  18  12

For z=7 the nonneutral D values range from 41 to 55, with
H_7=56. In particular these are exact maxima in the relaxed
finite phase space, not maxima along every full trajectory.
A large jump with both endpoints z-rough has delta=0 even
if it is not neutral modulo Q.

## 2. Exact rough-pair local factors

Write q(a) for the least odd prime factor of either a-1
or a+1, for positive even a. Ignore the integer 1 in taking
prime factors. An actual forward jump of odd prime p from
a to b=a-p+1 has a=e mod p, e in {-1,+1}. In the reverse
graph a is its newly created predecessor.

Fix p>z>=3 and impose that both a and b are z-rough,
that is q(a)>z and q(b)>z, with b>=2.
For each odd prime l<=z the forbidden residue classes of
a are exactly

    -1, 1, p-2, p (mod l).

Let nu_l(p) be their number of distinct classes. Since p
is a unit mod l,

    nu_l(p)=2 if p=1 mod l,
             3 if p=3 or -1 mod l, except previous case,
             4 otherwise.

The formula includes l=3: p=2 mod3 makes nu=3,
so both endpoints cannot be rough unless p=1 mod3.
Since p is odd, every such jump satisfies p=1 mod6.
In particular both-rough time for any z>=3 can only
be carried by labels neutral for the z=3 spatial cycle.

Fix the source side e and parametrize a=pm+e,
with m odd to make a even. Over a complete small-prime
period Q in m, the number of admissible odd residues is
exactly prod_(l<=z, odd prime)(l-nu_l(p)), since p is
coprime to Q. The exact conditional fraction given
source roughness is

    prod_l (l-nu_l(p))/(l-2).

No probabilistic independence between successive actual
jumps is asserted. This is a full-period arithmetic count
for a single fixed label and side, not a short-slab
trajectory distribution. The local upper sieve below
does not use a full period as a sampling interval.

## 3. Four-form paired rough capacity in a physical slab

Fix epsilon>0, let R tend to infinity, and take
z>=R^epsilon. If z is too large to permit any eligible
source in the slab the bound below is trivial.
Consider even sources a in [R,2R), b=a-p+1>=2, and
both q(a)>z and q(b)>z. Assume the sources under
consideration are non-twin centers (a-1,a+1 not both
prime); one can restrict to just these sources even
if twins exist elsewhere in the slab. Consequently
q(a)<=sqrt(2R+1). Set

    C_pair(R,z;p) =
      sum_(eligible such a) 2 min(p,q(a)).

Every actual event wait at a is <=2q(a) and <=2p,
so this is a per-label capacity for the total elapsed
time of actual paired-rough events on a strictly
decreasing forward path (or increasing reverse path).
Only sources are counted once; this is not a bound
on the aggregate over many canonical origins.

We obtain, uniformly over all odd primes p,

    C_pair(R,z;p) <<_epsilon
            R (loglog R)^4/(log R)^4.               (1)

Proof. For p<=z no such source exists. For p>R^(3/4),
the number of eligible even sources is O(R/p+1)
from the two congruences. Their weight is O(sqrt R),
so C_pair=O(R^(3/4)+sqrt R), which is absorbed in (1).

For z<p<=R^(3/4), use a=pm+e, e=+/-1, and m odd.
The paired rough conditions imply the following four
positive linear forms have no odd prime factor <=z:

    m,
    pm+2e,
    p(m-1)+e,
    p(m-1)+e+2.

The first is the cofactor of the p-divisible neighbor,
the second the other source neighbor, and the last
two are the arrival neighbors. A value 1 is allowed
and has no prime factors. The converse holds because
p>z. The m interval has length R/p>=R^(1/4).
For p>=5 these four forms have nonzero pairwise
determinants. The bad-prime product can be taken as

    B=2p * (2e) * (-p+e) * (-p+e+2)
                 * (p+e) * (p+e-2) * 2

in absolute value, which is nonzero and polynomially
bounded in R. Include 3 and 5 in the bad product as
well. For every prime l not dividing B, the forms
have four distinct forbidden residues mod l.
Restricting m to odd integers amounts to a linear
change of variable m=2t+1 and preserves this assertion
at odd l. Choose a fixed sufficiently small delta>0
depending on epsilon, with R^delta<=z and below p.
The dimension-four Selberg upper sieve on the t
interval, at a sufficiently small fixed power level
of its length, gives

    # paired-rough sources for one side
        <<_epsilon (R/p) prod_(5<l<=R^delta,l not|B)
                                        (1-4/l).

For clarity, the input is a multiplicative count
4^omega(d) of bad residues for squarefree d supported
on the good sieving primes, with uniform remainder
O(4^omega(d)) for an interval. The elementary
upper-sieve level can be chosen a sufficiently small
power of R/p so the usual remainder sum is absorbed.
This uses the standard dimension-four upper-bound
sieve, not a lower-bound sieve or a prime-tuple
asymptotic. The product over all l>5 up to R^delta
is O_epsilon((log R)^(-4)) by Mertens. Deleting primes
dividing B costs at most O((loglog R)^4): for primes
<=log R use Mertens again, and larger divisors have
reciprocal sum O(1/loglog R) by log |B|=O(log R).
Thus the count is O_epsilon((R/p)(loglog R)^4/log^4 R).
Multiply by 2p and sum over the two sides to obtain (1).

This is a paper-level application of the standard
upper sieve; the asymptotic constants and rate were
not tested numerically or Lean-checked.

## 4. Consequence for surviving local reverse paths

Take an exact inverse branch whose full physical
distance range lies in [R,2R), and on which no
source is a twin center. Let K be its number of
ticks, and let T_pair be the number of ticks in
event waits with both endpoints z-rough. Specifically,
attribute each completed event's preceding wait to its
source a and selected p; omit the final stationary
tail, and count the first wait from the given initial
phase if the branch begins between events. This is
the forward decomposition of the reverse path, so
each such wait is <=2 min(p,q(a)).
Let L_pair be the number of distinct labels on
those paired events. Summing (1), with no assumption
of independence or typical trajectories, gives

    T_pair <<_epsilon R L_pair
                      (loglog R)^4/(log R)^4.       (2)

If T_pair>=eta R for fixed eta>0, then necessarily

    L_pair >>_(epsilon,eta)
                      (log R/loglog R)^4.           (3)

This is a fourth-power logarithmic diversity
requirement for the time carried by rough-to-rough
events, improving the second-power single-source
capacity at the price of the paired roughness
hypothesis. It is not a support bound for all
events. All these labels also satisfy p=1 mod6.

Under finite twins, every sufficiently large slab
automatically has non-twin sources. If the branch
begins and ends in that slab, the final idle tail
at its target is <=2sqrt(2R+1)-1. Partition its
remaining time into paired-rough waits and other
waits T_other. Then

    K <= T_other + O(sqrt R)
                  + O_epsilon(R L_pair
                               (loglog R/log R)^4).

A long surviving path with few paired labels must
therefore obtain its time from events having at
least one endpoint with a small factor. This
identifies a precise alternative to the paired
sieve obstruction. Neither the fixed-z absorption
profile nor (1) controls that remaining time for
a polynomial cutoff z. In particular H_z may grow
very rapidly with z; replacing a fixed z by R^epsilon
in the earlier finite-potential bounds without a
new estimate would be invalid.

For the canonical-line problem, an arbitrary branch
need not lie within a single dyadic slab. One may
apply (2) to local source subintervals, but neither
the proportion of time in paired events nor the
number of distinct paired labels on such intervals
has been established. Equation (3) is conditional,
not a proof that non-twin inverse fibers die.

## 5. Executed diagnostic and persistence

Source research/min_local_negative_paired_rough_capacity_audit.mjs,
commit 55f537d50875f32a9f4fb22f7e8f3b3b63182486,
blob 6e32a8189cff267308bafe0e6632b239ae66ce71.
Executed as ECMAScript in the research runtime, fetched
at exact commit and re-executed with identical output.
Reproduce using
node research/min_local_negative_paired_rough_capacity_audit.mjs
No separate Node or Lean process invoked.

Compute full relaxed recharge profiles for z=3,5,7,
covering respectively 2,8,48 unit residues. 887840
valid phase/residue evaluations, with exact paired-rough
CRT count for each class. Check the profile bounds on
1011 canonical negative forward prefixes (A=12,210,...,
<=200000), truncated at tick -1. 22361 completed or
truncated event waits, 30570 actual high-event profile
checks across the three cutoffs, 3033 exact telescopes.
1197 actual paired-rough events for z=7; all satisfy
p=1 mod6. Their waits total 52361, compared to
50484649 ticks at rough sources, mostly stationary
terminal waits in this sample. These totals do NOT
support the assumption T_pair>=eta R for hypothetical
non-twin branches; no such inference is made.

For z=3,5,7,11,13, enumerate the odd progression residues
for 19 primes p=17..97 in the explicit list in the
script, both signs e. 190 complete period comparisons,
619134 progression-state checks. All exact local factors
and rough-pair CRT formulas passed.

Five finite source slabs (including possible twin
sources, not filtered by the asymptotic non-twin
condition) enumerate every eligible p and source
with both endpoints positive, and compare the four-form
test with direct roughness.

    R        z    eligible with rough source and b>=2    paired
    10000    5                 3039                        830
    10000   17                 1008                        108
   100000    7                22601                       4515
   100000   31                 7318                        563
   200000   53                11111                        661

45077 four-form comparisons, 6677 paired candidate
incidences (all p=1 mod6). The script also records
finite capacities and maximum capacity per label.
These are arithmetic input checks, not a proof
or numerical test of the asymptotic upper sieve.
The empty highByClass and unused slabCapacityChecks
fields in the script are not additional validations.

## 6. Remaining gap

The absorption recharge is now computable per residue,
and both-rough transitions have a stronger local
support obstruction than single-source rough events.
The missing bound concerns mixed rough/nonrough
transitions, or alternatively an unconditional
restriction on the distinct labels carrying paired
rough time. No uniform extinction theorem, no
unbounded zero-phase last-label theorem, no proof
of twin infinitude or Lean verification. No changes
to canonical Lean targets or sibling branches.
