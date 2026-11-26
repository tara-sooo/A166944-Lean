# Negative MIN: small-prime absorption potential and neutral large labels

2026-11-26 JST. Continuation of b3b6bccf76f91ca4b9ccaffe53c2127955a35782.
Use the finite-alphabet forward absorption time as a potential on
the exact unrestricted inverse graph. This yields an exact
active-time identity and a finite deadline for the first
residue-disrupting large label. It does not establish general
inverse extinction.

## 1. Finite-alphabet absorption time

Fix z>=3 and let A_z be all odd primes <=z, Q=2 prod_(p in A_z)p.
A positive even remaining distance a is z-rough if neither
a-1 nor a+1 has a prime divisor in A_z. Extend this definition
to all even residue classes modulo Q. In the restricted forward
tick maps (remaining distance decreases), a z-rough state is
stationary forever.

Let R_z(a,k) be the number of future ticks until reaching a
z-rough state in the restricted system, starting at remaining
distance a immediately AFTER tick -k. Define R_z=0 at rough
states. Here the restricted maps are extended to all integer
clock times, including zero and positive times, by the original
clock congruences. At tick n even use n=0 mod 2p and a=-1 mod p;
at tick n odd use n=p+2 mod 2p and a=1 mod p.

Both coordinates are periodic modulo Q for this absorption
time: translating the distance or clock by Q leaves the
restricted relative trajectory unchanged. The physical
primorial wall prevents the restricted trajectory from
crossing the preceding multiple of Q. Since a nonrough
state has a finite next wait, it reaches a rough state in
finitely many events, with total gain <Q and elapsed time
<=3 times that gain. Thus

    0 <= R_z <= H_z := max_(a even mod Q,k mod Q) R_z(a,k) < 3Q.

This definition of H_z is local to this note; it is not
the terminal phase H(A) of the negative trajectory.
It is an exact finite number independent of the number
or size of unrestricted labels.

Let F_k^z denote the restricted forward map at tick -k.
For all even a and all integer k, exact one-step recursion:

    R_z(a,k+1)-R_z(F_k^z(a),k)=1_(a not z-rough).     (1)

For a nonrough state the first future tick is consumed
whether or not it fires; if it becomes rough on that tick,
the second term is zero. At a rough state both terms are zero.

The DP for H_z enumerates even residues a=0,2,...,Q-2
in increasing order. Every restricted jump has a lower
arrival residue (no crossing of 0). For each phase k
compute the actual restricted next wait w, winner p,
and use R_z(a,k)=w+R_z(a-p+1,k-w). No numerical
truncation of the absorption time is involved.

## 2. Exact telescoping identity on unrestricted paths

Consider any exact inverse branch through K ticks, with
remaining distance a_{k+1} after tick -k-1 and a_k after
tick -k. Its forward map satisfies F_k(a_{k+1})=a_k.
Let p_k be its selected odd prime or zero for identity.
If p_k<=z (including identity), its forward step agrees
with the restricted map. If p_k>z, the restricted map
would be identity at the actual source a_{k+1}: any
eligible small clock would win before the large prime
by least-label priority at the same tick.

Define for a large jump

    delta_k=R_z(a_k,k)-R_z(a_{k+1},k),

and delta_k=0 for all other ticks. Substituting into (1)
gives the exact identity on every actual inverse edge,

    1_(a_{k+1} not z-rough)
       = R_z(a_{k+1},k+1)-R_z(a_k,k)+delta_k.

Write b=a_1, A=a_(K+1), and T_z for the number of ticks
in the prefix whose forward source is NOT z-rough.
Summation gives

    T_z=R_z(A,K+1)-R_z(b,1)+sum_(k:p_k>z) delta_k.    (2)

This is a count of elapsed active ticks, not event count
or physical gain. It covers idle ticks as well. The
same identity can be aggregated over whole forward
event waits (including truncated final idle waits)
because the physical source is constant during a wait.

For any large selected p with p=1 mod Q, the spatial
displacement p-1 vanishes modulo Q. Hence delta_k=0,
and the unrestricted step is exactly an identity step
on the restricted spatial residue. Call such a large
label neutral; call a large label not 1 mod Q
disruptive. Not every disruptive label has positive
delta: the potential difference is signed and depends
on the actual phase and distance residue.

In particular

    T_z <= H_z-R_z(b,1)
                    + sum_(large jumps) max(delta_k,0)
        <= H_z-R_z(b,1)+H_z N_disrupt.               (3)

No bound on the product of the neutral primes is
needed. Thus large neutral jumps can contribute
large physical gain but cannot recharge this
small-prime active-time budget. Only disruptive
jumps can do so.

## 3. Deadline for the first disruptive reverse jump

Suppose the target b is not z-rough. Consider an inverse
prefix containing no disruptive jump. Project its
coordinates modulo Q. Its forward motion is exactly
the restricted motion: a small jump is unchanged, an
identity is unchanged, and a neutral large jump
projects to identity at a tick where no small clock
fires. A rough state is absorbing in the projected
motion. Since the final target is nonrough, every
state along the prefix is nonrough. Hence T_z=K.

By (2), the exact deterministic bound is

    K <= H_z-R_z(b,1).                               (4)

This proves extinction of any branch with selected
alphabet contained in A_z union {p prime: p=1 mod Q}
at a nonrough target after this finite depth.
Unlike the finite-support theorem in 165150b,
the allowed neutral part of the alphabet can
contain arbitrarily many arbitrarily large primes.
The proof uses only the small-prime product Q.

For the unrestricted system, any branch surviving
beyond depth H_z-R_z(b,1) must have its FIRST
disruptive jump at some k satisfying

    k <= H_z-R_z(b,1)+1,
    z < p <= k+2 <= H_z-R_z(b,1)+3,
    p != 1 mod Q.                                   (5)

The label bound follows directly from negative tick
candidate divisibility. There is also an arbitrary
starting-node version: for a nonrough b at node
(b,j), replace R_z(b,1) by R_z(b,j) and k by
j plus the number of ticks processed so far.
In that version the absolute label cap is shifted
by j-1, so (5) is strongest at the original target.

These bounds do not imply that no disruptive jump
exists. They isolate a finite set of small/intermediate
labels that must restore a nonrough target at the
beginning of a long inverse path. If the first
disruptive jump occurs, the same argument can be
reapplied at later nonrough nodes, but rough nodes
may persist much longer. The number and signed
potential changes of such jumps are not controlled
by (4).

## 4. Separate the remaining rough-time budget

For the reverse jump sequence of b3b6bcc, let b_0=b
and b_i be the successive reverse jump arrival
distances, q(b) the least odd prime factor of a
neighbor. Partition the K ticks by their forward
source distance. The number at each b_i is at most
2q(b_i), by the stationary deadline bound; for b_i
with i>=1 include the tick of the reverse jump
that created b_i, then the subsequent identities.
The last interval has the same bound. Therefore the
number of ticks at z-rough sources is bounded by

    K-T_z <= 2 sum_(0<=i<=m:q(b_i)>z) q(b_i).        (6)

Combine (3) and (6):

    K <= H_z-R_z(b,1)+H_z N_disrupt
            +2 sum_(0<=i<=m:q(b_i)>z) q(b_i).       (7)

The second term counts only genuinely disruptive
large labels. In the final sum, for i>=1,
q(b_i)<=p_i; hence those contributions come
only from jumps with p_i>z. Small labels have
been eliminated from the direct time budget,
replaced by the finite potential and the cost
of recharging it. More sharply one may retain
the actual positive deltas in (3). This is a
necessary inequality, not an upper bound on
either remaining term. It does not contradict
the required canonical time K=A/2-4.
For fixed z, if K tends to infinity and the
disruptive jump count is o(K), then T_z=o(K).
Thus any such long path must spend nearly all
its time at sources rough for the fixed small
alphabet. This is a conditional conclusion,
not a claim about all long inverse branches.

## 5. Finite diagnostic and persistence

Source research/min_local_negative_absorption_potential_audit.mjs,
commit 48707499e4767a34d9a63c6460b6edfdd5a889f6,
blob 803b81e078932f99519b786029d1925880f4f76c.
Executed as ECMAScript in research runtime, fetched at the
exact commit and re-executed with identical output.
Reproduce:
node research/min_local_negative_absorption_potential_audit.mjs
No separate Node or Lean process invoked.
An initial prototype failed an inverse identity assertion.
It was replaced by a simpler independent exact one-tick
and event-wait audit; the committed version passed.
The initial failure was not an established counterexample
to the identity, and its precise implementation cause
was not isolated.

Four complete restricted phase spaces:
    z    Q       phase states   rough residues   H_z    mean R_z
    3    6                 18             1      7      2.666667
    5    30               450             3     19      6.128889
    7    210            22050            15     56     10.690113
   11    2310         2668050           135    133     15.043958

Every one-step identity (1) in all 2690568 states passed.
These exact maxima are for the unrestricted phase space
of the SMALL alphabet, not full negative MIN. They are
not the same statistic as the maximum nonrough target
extinction depths 7,19,49,79 in 165150b. In particular
for z=5,7,11 the first disruptive-jump cap (5) is much
smaller than Q. For z=3 there can be no canonical
non-twin target with q=3 beyond the already known
single-tick erasure, but general edge identities still
apply.

For each z independently use every non-twin prime
target P in [1009,30000] and sparse additional P up to
300000 satisfying P=1 mod 101 (2840 targets per z).
Compute actual inverse fibers up to min(8192,(P-1)/2-4).
All 2840 targets extinct in each control as previously.
Check (2) one edge at a time, neutral-label cancellation,
and (4) on prefixes from nonrough targets before any
disruptive jump. All checks passed.
    z     inverse edges    large edges   neutral    positive delta
    3       573272             44493     15851         12607
    5       573272             24062       706          9510
    7       573272             14098        14          5915
   11       573272             10240         0          4388

Counts of edges are graph incidences, not independent
paths. 9766 no-disruption surviving-edge checks across
the four controls passed. Positive-delta edges and
rough-to-nonrough transitions are not equivalent;
17619 rough-to-nonrough large edges were counted.
The empty profile field in the script is unused;
no complete residue-drop profile was computed.

Independently simulate the 1516 canonical roots
X=12,210,...<=300000, stopping their prefix at -1.
Aggregate (2) over actual event waits and a truncated
last wait, checking the telescope for every root and z.
    z    sum of active ticks    total elapsed ticks
    3            38507               113691662
    5            70917               113691662
    7            96707               113691662
   11           116700               113691662

Totals 6064 root/control incidences and 139900
event-wait checks, 2293088 inverse-edge checks,
16571 neutral high-edge checks, 9766 checks of (4),
2690568 complete restricted one-step checks.
All assertions passed. The sparse canonical samples
are dominated by long idle waits near terminal twin
centers; the ratios do not supply an estimate for
hypothetical non-twin long inverse branches. No
asymptotic distribution is inferred.

## 6. Remaining gap

The finite-support extinction result now extends to
an infinite neutral-label alphabet. For a nonrough
terminal target, the first restoring disruptive jump
has an exact phase-dependent finite time cap.
The remaining challenge is to control subsequent
disruptions and time at rough states in (7). The
inequality neither forces unrestricted extinction
nor proves unbounded zero-phase terminal labels.
No twin-infinitude proof or Lean verification;
no changes to canonical Lean targets or sibling
branches.
