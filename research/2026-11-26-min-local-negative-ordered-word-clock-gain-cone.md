# Negative MIN: ordered high-word rounding and coupled clock-gain cone

2026-11-26 JST. Continuation of fcce5edb6b863a24a130e9d21c775ae777e61238.
Replace repeated-key packing by cumulative congruences along the
entire ordered high word. This gives a lower-gain certificate even
with no repeated keys. Couple cumulative space and time using two
monotone slack variables and the nonnegative-height invariant.
Paper deductions and executed finite audit; no asymptotic result
or Lean verification.

## 1. Ordered word and exact scalar relaxation

Consider a finite completed-event block of negative MIN starting
at even distance A>0 and integer clock v0, with initial height
h0=A/2+v0>=0. Choose integer threshold T>=5. Mark p>=T.
Record only the ordered marked labels p_i, their source signs
e_i in {-1,+1}, and actual marked waits w_i. The source convention
is a=e_i mod p_i and firing time 0 mod 2p_i when e_i=-1,
p_i+2 mod 2p_i when e_i=+1. Set

    H_i=sum_(j<=i)(p_j-1)/2,
    V_i=sum_(j<=i)w_j.

Let s_i be half the cumulative unmarked gain through just before
mark i and u_i the cumulative unmarked wait through that point.
They are unchanged by the marked event itself. The source and
firing clock at mark i are

    a_i=A-2H_(i-1)-2s_i,
    n_i=v0+V_i+u_i.

Thus s_i is in the residue

    alpha_i=(A-2H_(i-1)-e_i)*inverse(2,p_i) mod p_i,

and u_i is in the residue

    beta_i=c(p_i,e_i)-v0-V_i mod 2p_i,

where c(p,-1)=0, c(p,+1)=p+2. Both cumulative variables
are nonnegative integers and nondecreasing, starting at zero.
This is the entire ordered word, not a collection of unordered
pair keys. Neither actual source positions nor relay gains,
nor any low labels, need be supplied.

Write up(x,r,m)=x+((r-x) mod m), for integer x and positive m.
The greedy recurrences

    S_0=U_0=0,
    S_i=up(S_(i-1),alpha_i,p_i),
    U_i=up(U_(i-1),beta_i,2p_i)

give componentwise minimum sequences in the separate scalar
monotone congruence relaxations. By induction up is monotone
in x, so S_i<=s_i and U_i<=u_i for every actual trajectory.
Every scalar greedy sequence itself satisfies the corresponding
relaxed conditions; it need not be a realizable clock path.

Exact short-relay reconstruction: if for every i up to a given
mark the actual s_i-s_(i-1)<p_i, then S_i=s_i throughout
that prefix. Indeed the actual value is the unique congruent
integer in [s_(i-1),s_(i-1)+p_i). Similarly if every
u_i-u_(i-1)<2p_i then U_i=u_i. The initial unmarked run
before the first high mark is included. These assumptions are
not established for arbitrary long prefixes.

Without reconstruction assumptions the lower bound still applies.
It can be positive even for a completely distinct high word,
unlike a pure repeated-key packing argument. The actual marked
waits are needed only for the time and joint versions.

## 2. Coupled clock-gain cone

Every unmarked event satisfies w<=3(p-1) and w>=1.
Put M=floor((T-2)/2)>=1 and D=6M-1>0.
The half gain of such an event is at most M. Therefore for
successive cumulative points (s_i,u_i),

    delta_s>=0, delta_u>=0,
    delta_u<=6 delta_s, delta_s<=M delta_u.

In particular two further cumulative quantities are nonnegative
and nondecreasing:

    l_i=6s_i-u_i,
    r_i=M u_i-s_i.

They satisfy exact congruences

    l_i=6alpha_i-beta_i mod 2p_i,
    r_i=M beta_i-alpha_i mod p_i.

The first uses the even coefficient 6 and s_i mod p_i;
the second uses only the modulus p_i. All four cumulative
variables start at zero. The linear identities

    s_i=(M l_i+r_i)/D,
    u_i=(l_i+6r_i)/D

and the nonnegative height AFTER the i-th marked event imply

    u_i >= s_i+C_i,
    C_i=H_i-V_i-h0.

These hold even for noncanonical initial phases with h0>=0.

Maintain lower bounds (S,U,L,R) for (s,u,l,r), initialized at
(0,0,0,0). At each mark start with the preceding bounds and
repeatedly apply the simultaneous monotone update

    S' = up(max(S,ceil((U+L)/6),ceil((M L+R)/D)),
            alpha_i,p_i),
    U' = up(max(U,ceil((S+R)/M),ceil((L+6R)/D),S+C_i),
            beta_i,2p_i),
    L' = up(L,6alpha_i-beta_i,2p_i),
    R' = up(R,M beta_i-alpha_i,p_i).

Every inequality in this update is a necessary lower bound
using the exact identities and height constraint. Each rounded
value stays <= the corresponding actual variable, because that
variable has the required residue. Since all four bounds are
nondecreasing integers bounded by the actual trajectory, the
iteration terminates at a fixed point for every actual word.
On a hypothetical word with a finite gain/time budget one can
instead stop and reject immediately when a bound exceeds that
budget; no general termination assertion for infeasible,
unbounded inputs is necessary. This algorithm is a lower-bound
propagation, not a claim that its fixed point satisfies all
linear equalities or is the exact joint optimum.

The joint S,U dominate the independent greedy values by
induction, because each update includes the previous S,U and
rounds them into the same required residue. The slack bounds
carry information from earlier marks even if all later labels
are new. The extra height constraint also enforces a necessary
amount of waiting before any large cumulative gain.

## 3. Application to the stopped-prefix objective

Use the canonical stopped prefix of cc62807, trimming its
half-crossing event if present. Under finite twins and large A,
the trimmed block has total gain <A/2 and total wait
>=A/4-O(sqrt A). For a complete observed marked word of
length m, the new certificate is

    2H_m+2S_joint(m) <= total gain < A/2,
    V_m+U_joint(m) <= total completed wait.

The first is a necessary joint-gain budget; the second is
only a LOWER bound on the wait. Both exclude the unmarked tail
after the last mark, so neither should be read as equality
with all unmarked gain or time. With no marked events the
certificate is zero. For a hypothetical word whose gain lower
bound reaches A/2, no trimmed canonical prefix can realize
it. Similarly, on the negative prefix all marked firing
times must be <=-1, so V_i+U_joint(i)<=-1-v0 gives an
additional rejection test. The bounds do not prove that
all long words are rejected, nor an upper bound on the
actual wait. In particular there is no demonstrated lower
bound forcing the joint certificate to violate the budget
under the assumed macroscopic wait. This is a potentially
useful restriction on ordered words before counting or
constructing actual trajectories. No independence of successive
residues, and no assumed bound on the distinct high support.

## 4. Executed finite audit

Source research/min_local_negative_ordered_word_cone_audit.mjs,
commit 6b0a9642841532abbaec50a9c84ecedbbf372a1b,
blob 26232cc3bd61617557e2007a034dd501ed79920c.
Executed as ECMAScript in the research runtime, fetched
at exact commit and re-executed with identical output.
Reproduce:
node research/min_local_negative_ordered_word_cone_audit.mjs
No separate Node or Lean invocation.

Canonical controls: all A=12,18,...,60000 (9999 roots).
Stop before firing after -1, or omit the half-crossing
event. Three thresholds per root: 11, max(5,ceil(sqrt(A)/4)),
max(5,ceil(sqrt(A))). 165952 event evaluations include
any omitted crossing event. 29997 root/threshold controls.

Noncanonical controls: four slabs R=10000,40000,100000,
180000; 50 roots per each initial phase 0,17,floor(A/5)
per slab. Split at twin sources, retain contiguous
non-twin blocks. Four thresholds per block: 11,23,
max(5,ceil(sqrt(R)/4)),ceil(sqrt(R)).
600 roots, 10467 event evaluations, 561 nonempty blocks.
These controls use positive clock phases and do not
represent hypothetical long canonical negative prefixes.

    total block/threshold controls       32241
    controls with marks                   17892
    marked incidences                     78209
    first occurrences of a label          62235
    space/time/slack checks              78209 each
    fixed-point update iterations        146137
    max iterations at a mark                  4
    exact independent spatial bounds     76000
    exact independent time bounds        74545
    both joint bounds exact              74902
    joint gain improves independent      1021
    joint time improves independent       593
    short-gain reconstruction checks    71977
    short-time reconstruction checks    64671

All assertions passed. The maximum gain-certificate improvement
over the scalar spatial bound is 1324 units. This finite maximum
is not a uniform theoretical bound. For example A=762,T=11 at
a marked p=19, scalar spatial gain lower bound 12, joint lower
bound 50, actual cumulative low gain 50.

Summing over the last mark of each canonical threshold control
(zeros if none), actual lower gain 1405416, independent spatial
lower bound 1295338, coupled lower bound 1339860. This is a
ratio of sums across overlapping threshold controls and excludes
the final unmarked tail, not a statement of typical asymptotic
accuracy. It shows a stronger finite certificate but no
macroscopic contradiction. All canonical controls together
are finite and most eventually encounter nearby twin centers.
The script tests lower bounds against actual words, not
arbitrary-word enumeration or impossibility of every long word.

## 5. Remaining target

Cumulative congruences remove the need for repeated pair keys
in this lower-gain certificate. To reach twin infinitude one
must still show an unbounded sequence of canonical seeds with
liminf W(A)/A<1/4, or derive a contradiction to finite twins
using ordered-word constraints, time and gain budgets. A
possible next problem is to count feasible words with both
budgets, rather than refine a posteriori certificates alone.
No asymptotic estimate of that kind, twin-infinitude proof,
or Lean verification. No changes to canonical Lean targets
or sibling branches.
