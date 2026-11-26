# Joint adaptive query budgets and localization of small relay charges

2026-11-26 JST. Continuation of 2d4882e49a4b850ea973464a5c63ae25a42786b7.
Strengthen the first-moment CRT query law to joint upper tails for
distinct label discoveries, without assuming independent band
trajectories. Localize the remaining fixed-small-alphabet charge
by the label preceding a maximal small relay. Paper deductions
and executed finite audit. No Lean verification or twin-infinitude proof.

## 1. Posterior law on the exact query transcript

Use the canonical restricted map and deferred query algorithm
of 562b8890 and 2d4882e4. The finite admitted alphabet A
contains 3. Sample uniformly the full seed period
P=4 product_(p in A) p, among canonical roots X=0 mod6.
Condition on X mod12, and optionally on all residues outside
the tracked primes. The remaining prime residues are independent
and uniform by CRT. This is a finite full-period probability
space, NOT the empirical distribution in a short physical slab.

The next query is determined by the actual relative transcript.
At source u=X+G and a tick of parity e (e=+1 even, -1 odd),
a candidate prime dividing the relevant defect queries
X=e-G mod p. Check clocks in actual time and least-prime order;
a positive query selects that clock. An already known residue
or a previously rejected residue does not need a new query.
A virtual terminal scan does not advance the state.

Conditional on the entire previously revealed transcript,
each still unknown prime p has a uniform residue over the
complement of its f_p distinct rejected residues. Indeed each
fixed transcript imposes just the indicated residue exclusions
or equalities separately at each prime, since the deterministic
algorithm makes the same subsequent query on every lift with
that transcript. Thus the next previously untested residue
at p succeeds with predictable probability

    q=1/(p-f_p).                                     (1)

The transcript must not include information from a full
factorization oracle. Factorization may independently check
the next event in a numerical audit, but the query process
itself reveals only the stated tests. In particular the
stopping rules below use only revealed information.

## 2. Joint budgets for distinct discoveries

Let B_1,...,B_m be disjoint sets of admitted primes >=5
(the letter B denotes the set here; beta denotes a budget).
Choose targets k_i>=1 and budgets 0<beta_i<1.
While band i has fewer than k_i discovered labels, charge
1/p for each NEW query at an unknown prime p in that band,
including a successful query. Let C_i be this running sum.
After k_i discoveries freeze the counter for that band.
Continue the actual dynamics, including uncharged queries
to that band if necessary. Also allow any ordinary bounded
transcript stopping rule, e.g. a displacement cutoff.

Introduce an auxiliary global stop BEFORE any charged
query would make C_i>beta_i. An original path on which
every band meets its target within its own budget survives
this additional stop until all targets are attained.
Conversely, success of this stopped process certifies
exactly that original event. No assumptions on the order
of band activations or on intermediate events are made.

For a charged query of weight a=1/p in band i, write
C=C_i, beta=beta_i. Then f_p/p<=C, and by (1),

    q <= a/(1-C),   C+a<=beta<1.                     (2)

Only this band's potential changes on a charged query.
All other potential factors remain fixed, even though
the query may change the subsequent physical trajectory.

### 2a. One discovery: exact linear budget factor

For a band with k_i=1 use the nonnegative potential

    V(C,not hit)=(beta-C)/(1-C),
    V(hit)=1.

Put t=a/(1-C), V'=(beta-C-a)/(1-C-a). At a charged
query the conditional expectation is (1-q)V'+q.
Since V' in [0,1] and q<=t, it is at most

    (1-t)V'+t = (beta-C)/(1-C)=V.

After success freeze V=1. Thus the product of these
potentials across bands is a nonnegative supermartingale,
not a product of independent random variables.
It starts at product beta_i and equals 1 on joint success.

### 2b. Multiple distinct discoveries: logarithmic budget factor

For k_i>=2 use r=k_i-K_i remaining discoveries and

    b=log((1-C)/(1-beta)),
    V_r(b)=b^r/r!,  V_0=1.

Freeze when r=0. At a permitted new query, the decrease
in b is

    d=log((1-C)/(1-C-a)) >= a/(1-C) >= q.

Here b>=d>=0. For r>=1,

    E V_after
      =(1-q)(b-d)^r/r! + q(b-d)^(r-1)/(r-1)!
      <= [(b-d)^r+r d (b-d)^(r-1)]/r!
      <= b^r/r!.

The last step is the binomial theorem (also valid at
r=1, with the zeroth power interpreted as 1).
Use the exact first-hit potential for k_i=1 and this
logarithmic potential for the other bands. Their product
is again a nonnegative supermartingale because only
one factor changes at a time.

The process stops in finitely many queries: the ordinary
physical cutoff gives finitely many events, each with
a finite clock scan; even without it a restricted path
terminates at a primorial wall. Equivalently one can apply
the finite-step supermartingale inequality and take the
nonnegative limit. The joint success event has product
potential 1, so

    Pr(all k_i targets reached within their budgets)
      <= product_(i:k_i=1) beta_i
         * product_(i:k_i>=2)
                [-log(1-beta_i)]^k_i/k_i!.           (3)

Use min(1,RHS) if the expression exceeds 1.
For small budgets the logarithmic factor is asymptotic
to beta_i, and the dependence on the target count is
factorial. The proof also gives the weaker potential
with b=(beta-C)/(1-beta), since its decrement is >=q.
The finite audit checks both versions.

This is a joint tail for DISTINCT labels, not all event
incidences of a previously discovered label. There is
no claim of stochastic independence of actual hits.
The argument conditions on the revealed transcript,
including previously selected labels in other bands.

## 3. Convert failed-query charges into joint tails

Let F_i be the sum of 1/p over distinct failed queries
in band i prior to its k_i-th discovery or the original
stop, counting each prime only before its first success.
If the band's minimum prime is >=y_i, then at the
k_i-th discovery the full charge C_i is <=F_i+k_i/y_i.
Consequently (3) applies to the event

    K_i>=k_i and F_i<=c_i for every i,

by taking beta_i=c_i+k_i/y_i<1.
Here K_i may count all discoveries on the original
trajectory; the charge F_i freezes at the target.
In particular the probability of all bands having at
least one discovery under failed budgets c_i is at most
product_i(c_i+1/y_i). A union bound adds the probability
of any budget violation when an unconditional joint
hit bound is desired. No independence between violation
events is needed.

The quiet-coarea bound of 2d4882e4 supplies a
pointwise upper estimate on F_i. For band primes in
[y_i,2y_i] and 2Hmax+5<y_i^2 it is

    F_i <= 2 sum_(p in band i) 1/p
       + Phi_i(h_end)-Phi_i(3)
       + sum_h a_i(h) D^o(h).                         (4)

One may use the whole stopped path on the RHS, since
the sum of nonnegative quiet upward costs and the
terminal allowance dominate any prefix cost. If the
height condition does not hold, use the untrimmed
coarea bound or add the actual failed firing cost.
Thus (3) applies even to widely separated bands provided
the appropriate cost bound for EACH band is used.
One must not apply the O(y_i) height-corridor estimate
uniformly to much smaller bands on a much longer path.

For a band in [y,2y] on a path of total gain G, previous
same-label spacing is at least 2(p-1). Therefore the
gain from any one p is <=G/2+(p-1)<=G/2+2y.
In particular if G_B>G/2+2y, at least two distinct
band labels have been selected. From (3) with k=2,
for c+2/y<1,

    Pr(G_B>G/2+2y, F_B<=c)
        <= [-log(1-c-2/y)]^2/2.                      (5)

The F_B counter can stop at the second distinct hit;
the upper bound remains valid if one instead imposes
the full original failed-query cost <=c.
This is a quadratic small-cost bound on heavy band
gain, rather than just the preceding linear first
moment bound. It does not bound heavy gain when the
cost itself is large. For G only O(y), the criterion
G_B>G/2+2y can be vacuous at very short horizons.
For a larger fixed multiple D=Cy, it is meaningful.

## 4. Localize the fixed-small-label residual charge

Fix z0>=5 and consider a stopped path with G=O(y).
Take maximal runs of labels <=z0; an arbitrary-phase
run has physical gain <=L_z0, a finite primorial wall
bound (or a sharper exact restricted cap).
The residual interval length per run is at most
half its physical gain, so its contribution to
S^o_z0 (defined in 2d4882e4) is <=L_z0/2, with
or without the height restriction.

Split these runs by the preceding label, including
one possible initial run. For any t>z0, the total
high-height residual charge of runs immediately
following a label >=t, plus the initial run, is

    <= (L_z0/2)(1+G/(t-1)).                           (6)

This bound is deterministic, since each preceding
label >=t consumes at least t-1 gain and precedes
at most one maximal run. The initial run is in fact
below the high-height cutoff for all sufficiently
large y with z0 fixed: its total gain <=L_z0 and
all waits <=3 times that gain, so Hmax<=3+3L_z0.

For fixed z0 and t=t(y)->infinity the RHS is o(y).
Thus the missing condition E S^o_z0=o(y), on the
linear displacement stop, reduces to controlling
small runs immediately following labels in the
intermediate range z0<p<t(y). This bound is valid
pointwise, hence also in a local slab without CRT
averaging. It does NOT bound the sum over these
intermediate predecessors. Attempting to absorb
all of them into the low alphabet would replace
L_z0 by L_t and does not give o(y) with the available
caps. In particular (6) does not establish the
desired asymptotic small-label occupation bound.

## 5. Executed finite diagnostic

Source research/min_local_restricted_joint_query_budget_audit.mjs
final commit e6b580ae18e5970339e3190f3fb5aa4f92f008cb,
blob 4cafea736deb07f60aa2c01eff16fb637f104cda.
Run: node research/min_local_restricted_joint_query_budget_audit.mjs.
Actually executed as ECMAScript in the research runtime,
fetched at exact commit and re-executed identically.
No separate Node process or Lean invocation.

Five full-period controls with max label z and physical
cutoff D. Disjoint tracked bands are finite prime subsets;
the budgets and target counts are specified in the script.
For each seed compute the ordinary full stopped path,
and separately run the transcript budget-stopped path.
The latter stops before exceeding a band's charge budget.
At each actual source compute the next event independently
from neighbor congruences, then scan defect candidates up
to the firing tick in least-prime order. Thus event oracle
is only used as an independent numerical route to the true
clock order, not as conditioning information in (1).
Check the conditional probability bound and both potential
inequalities at each active new query. Average terminal
potentials over the entire period, check joint success
frequency against the product bound, and compare exactly
with eligible original paths.

    z    D   roots   joint success   sharp upper probability
    7   20       70          2             .0315000
    11  24      770          3             .0247896
    13  28    10010          2             .0053990
    17  36   170170       1137             .0135000
    17  36   170170         85             .0073472

351190 root/control incidences, 351553 completed
events on budget-stopped paths, 2069800 unknown
query attempts (includes budget-trigger attempts),
1607756 active permitted new queries, 387417 cached
or known query checks. Both potential inequalities
checked at all 1607756 active queries; all five exact
period success counts and mean final potential bounds
passed. In the five controls there were 17784 original
paths with all discovery targets reached, of which
1229 met all budgets, exactly matching auxiliary
successes. 342356 budget stops. In the first control,
two single-prime targets, final mean sharp potential
equals .0315 within floating arithmetic tolerance.
The test verifies finite supermartingale inequalities
using exact prime arithmetic and floating potentials.
The posterior argument, asymptotic deductions and
relay localization are mathematical derivations, not
independently enumerated posterior transcript groups
or kernel-checked statements.

## 6. Remaining work

The joint-budget result strengthens the adaptive CRT
method beyond single-band expectation estimates. It can
be combined with any proven high-height charge bound
and provides simultaneous discovery tails without
multiplying unverified independence probabilities.
However the unresolved intermediate-label relay charge
in section 4 prevents using it as an unconditional
small-occupation theorem. Full-period conditioning also
does not hold for empirical intervals of length O(y^2).
No short restricted-termination theorem, favorable
unbounded reset family, or twin-infinitude proof.
No changes to canonical Lean targets or sibling branches.
