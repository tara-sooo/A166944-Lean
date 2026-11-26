# Negative-time prime innovation and finite-support extinction

2026-11-26 JST. Continuation of 91e7cfeb525ef747b685e9c7412d1b789f549d9f.
Analyze inverse suffix restoration by distinguishing the first appearance
of a prime from recycled clocks. Exact CRT lift formulas for inverse
width and image density, and a deterministic necessary support-product
bound for long surviving nonrough targets. Executed finite diagnostic.
No general extinction theorem, Lean verification, or twin-infinitude proof.

## 1. A single-clock inverse operation

Use the tick maps F_k of 91e7cfe, for n=-k, k>=1.
For a tick with a single candidate prime p, set e=+1 for
odd k and e=-1 for even k. F_k moves a=e mod p to
a-p+1 (arrival residue e+1); it fixes all other even
integers. For any finite nonempty inverse set S, let
W=|S| and N_j=|{a in S:a=j mod p}|.

The full inverse set has cardinality exactly

    W' = W - N_e + N_(e+1).                         (1)

Each state with residue e has no predecessor; each
state with residue e+1 has two, itself and itself+p-1;
each other state has exactly one. Distinct targets
have disjoint preimages because F_k is a function.
Thus W'=0 iff N_e=W. In particular extinction with
W>=2 requires all the even states to be congruent
modulo p, hence their span to be at least 2p.
This applies to repeated single-prime ticks as well.

For a tick with multiple candidates C_k, a necessary
condition for extinction is that EVERY state in S
be congruent to e modulo at least one p in C_k.
Otherwise a state not moved by the forward tick is
its own predecessor. The condition is not sufficient:
arrivals from other states can restore a predecessor.
We continue to use exact least-prime tests for them.

## 2. First appearance of a new prime: exact lift law

The first appearance of any odd prime p in the
backward scan k=1,2,... is at k=p-2, an odd tick
with the SINGLE candidate p. All earlier candidate
primes are less than p. Conversely every odd prime
less than p has already appeared. Therefore the
previous suffix is periodic with

    Q=2 product_(3<=r<p, r prime) r.

For a fixed even target b mod Q, let S be its
exact inverse fiber through the previous suffix
k=p-3 (empty allowed). Write the distinct offsets
of its elements relative to b as D={d:a=b+d in S}.
All offsets are even and nonnegative. Translating
the target by any multiple of Q translates its
whole inverse fiber, by periodicity. This statement
is about the arithmetic maps on even integers; for
positive targets all inverse offsets are positive
states as well.

Let N_j count offsets d=j mod p. The p CRT lifts
b+Qt, 0<=t<p, run once through each possible target
residue mod p. Since p is new, (1) gives their
new widths in some order as

    W_j = W - N_j + N_(j+1),  j mod p.             (2)

In particular, over these p lifts,

    E W_new = W,
    Var(W_new) = (1/p) sum_j (N_(j+1)-N_j)^2,
    Pr(W_new=0 | W>0) =
        1/p if all offsets share one residue mod p,
        0 otherwise.                              (3)

For an empty prior fiber every lift remains empty.
The variance is <=2W^2/p, or <=2W/p if the offsets
are pairwise distinct mod p. In the latter case use
sum N_j^2=W. The exact formulas need no independence
between different states' residues: they all undergo
the SAME shift mod p. In particular treating the
states as independent CRT draws would give an
incorrect extinction probability.

Define rho(K) to be the density of nonempty inverse
fibers at depth K over the even residues of the
suffix period, and let mu(p) be the density at
depth p-3 of nonempty fibers whose offsets all lie
in ONE residue mod p. Then exactly

    rho(p-2) = rho(p-3) - mu(p)/p.                  (4)

In particular rho(p-2)>= (1-1/p)rho(p-3).
A prime innovation never removes more than 1/p of
the preceding image density; a wide fiber with two
different residues cannot be erased by this tick.

Similarly the mean squared width increases at this
innovation by the mean over old target classes of
the variance expression in (3), whereas the mean
width itself is unchanged. The average width over
the full residue period equals one for any suffix,
because the forward composition is a function on
that finite cycle. The mean squared width identity
does not assert monotonicity for recycled clocks.
At a recycled tick the period is unchanged, and
the image of the longer suffix is a subset of the
previous image. Its density can decrease without
the factor bound (4). Controlling these losses
is a separate issue.

If conditioning on the target b+1 not divisible by
the newly introduced prime p, one lift is excluded.
For a nonempty mono-residue fiber D=c mod p the
erasing lift has b+Qt=1-c mod p. It is excluded by
that primality condition exactly when c=2 mod p.
Otherwise its conditional extinction probability is
1/(p-1). Multiresidue fibers have zero extinction
probability in either case. This is a local
congruence calculation, not an assertion about
the distribution of actual primes in short intervals.

## 3. Application to the first factor of P-2

Let P>=11 be prime, P-2 composite, q its least factor,
and b=P-1. Through depth q-3, the stationary state
b itself always survives: all candidate primes <q
divide neither b+1=P nor b-1=P-2. At the innovation
k=q-2, b=1 mod q, so this stationary inverse branch
is erased. All other inverse states are >=b.
It follows from (1) that

    S_(q-2)(b) nonempty
      iff S_(q-3)(b) contains a state not
           congruent to b modulo q.               (5)

For example, any restored offset d with 0<d<2q
already certifies survival beyond this first erasure.
This does not guarantee long survival: at later
ticks the restored states can themselves be erased.
It does not prove that every non-twin q>=11 is
eventually erased. For q=11 the earlier finite
period control shows that all 15 admissible target
classes survive at depth 9.

## 4. Finite support cannot maintain a nonrough target

A separate deterministic constraint on longer inverse
survival does not require CRT averaging.

Suppose an actual surviving inverse path through K
ticks, from a at time -K-1 to b at time -1, has
selected labels in a finite alphabet A of odd primes.
Assume an odd prime q divides b-1 or b+1. Adjoin q
to A if necessary, and put

    Q_A = 2 product_(p in A union {q}) p.

The path is still an exact path of the restriction
to A union {q}: every selected event remains
available, and removing unused labels cannot create
an earlier winner. The tick maps in this restriction
are periodic in the clock with common period Q_A.
For the physical coordinate, no decreasing step
a->a-p+1 can cross a multiple J of Q_A from above
to below: if the even positive distance a-J were
less than p-1, a=+/-1 mod p could not hold. At the
wall no label in the alphabet is eligible.
Since b has an eligible q, b is not a wall. Hence
the whole prefix must start below the next multiple
J>b of Q_A, and its total gain G=a-b satisfies

    G<J-b<=Q_A.

Every wait to a selected prime p is <=2p<=3(p-1).
This includes the first event wait from the arbitrary
starting tick, since a fixed eligible clock repeats
every 2p. The final idle stretch at b must be
strictly less than 2q: otherwise the eligible
q-clock would have fired. Thus

    K <= 3G+2q-1 < 3Q_A+2q.                       (6)

This also covers a completely stationary finite
prefix (G=0); its final idle stretch is the
whole K. Therefore all inverse fibers of a
finite-alphabet restriction at a nonrough target
are empty for K>=3Q_A+2q. A target rough for the
whole alphabet always has its stationary inverse
path. The infinite-depth survival set for this
FIXED restriction is consequently exactly its
rough offsets.

For the original unbounded alphabet, every surviving
path at a target with factor q must satisfy

    product_(distinct selected primes union {q}) p
         > (K-2q)/6                               (7)

when K>2q. This is a necessary support-product
growth condition; it is NOT sufficient for survival.
For example, if every selected label were <=z and
q<=z, then K<6 prod_(3<=p<=z)p+2q.
Thus for fixed q, no indefinitely surviving branch
can use only a fixed finite set of labels. Using
the prime number theorem, a surviving branch for
K tending to infinity with fixed q must use a
label at least (1-o(1))log K. The product argument
also holds without this asymptotic estimate.
The bound grows exponentially with the allowed
label cutoff, so it does not show extinction of
the full negative-time maps, whose available
labels grow with K.

This connects inverse restoration to the earlier
support-product wall idea, but with the actual
clock-time horizon rather than a forward displacement
cutoff. It does not establish that all non-twin
targets are erased by their canonical birth-time
bound K=(P-1)/2-4.

## 5. Executed diagnostic

Source research/min_local_negative_prime_innovation_audit.mjs,
final commit 9f45b5a4329a6f5e04ab8057a7b1dcae9a87dc6d,
blob 48fd28f573225e2543f5b87bb440aac6105b959a.
Executed as ECMAScript, fetched at exact commit,
re-executed with identical output. Reproduce using
node research/min_local_negative_prime_innovation_audit.mjs.
No separate Node or Lean process.

Repeat the non-twin prime targets P in [1009,300000]
from 91e7cfe, now using a single cap
min(8192,(P-1)/2-4), and classify the extinction tick.
All 22870 targets extinct as before, longest 4315.
694630 inverse ticks (fewer than previous audit
because twin targets, period controls and redundant
extensions are excluded from this count).

    first q-clock erases entire fiber        17256
    survives first q-clock                    5614

    extinction at any prime innovation      17301
    extinction at recycled clocks            5569

    singleton just before extinction        21701
    multiple states just before extinction   1169

Joint breakdown:
    innovation / single / width 1            17301
    recycled / single / width 1                1528
    recycled / multi  / width 1                2872
    recycled / single / width >1                123
    recycled / multi  / width >1               1046

All 1169 multi-state extinctions occurred at
recycled ticks in this finite sample, not a
general theorem. Of 5614 targets surviving their
first q-erasure, 45 later died at another innovation
and 5569 at recycled clocks. This identifies the
dominant restoration obstacle in these controls.
The longest case P=241333 died at k=4315, with
candidates {3,1439} and prior fiber {245242,245248}.

All 167081 innovation and 221932 recycled-single
width/extinction checks of (1) passed; all 3918
multi-prime extinction cover checks passed.
For each new p=3,5,7,11,13,17, enumerate the exact
previous full-period fibers, translate through
all p lifts and verify (2)-(4) including variance.

    p       Q      nonempty       mono-residue   lost lifts
    3       2             1                  1            1
    5       6             2                  1            1
    7      30             9                  5            5
   11     210            30                  0            0
   13    2310           330                 25           25
   17   30030          3286                140          140

E.g. p=11 causes no additional image loss at first
appearance in this complete period. The finite CRT
translation, mean, variance and extinction identities
all passed, not estimates of asymptotic loss.
The script also counts excluded primality lifts
for the conditional observation in section 2.

Restricted alphabet controls: for each even residue
in a complete physical period Q_A test every nonrough
target until extinction, check wall and time-gain
inequality (6) on every surviving ancestor.

    A max      Q_A  nonrough targets   max extinction
      3          6          2                  7
      5         30         12                 19
      7        210         90                 49
     11       2310       1020                 79

Total 1124 nonrough targets, 8023 restricted reverse
ticks, 18240 wall and time-gain checks each, all passed.
The upper bound 3Q_A+2q is very loose here; the observed
small maximum is not a proved general replacement.

## 6. Remaining gap

At new-prime steps extinction has an exact one-residue
criterion and density-loss law. The data show that
after restoration at the first q-clock, recycled
clocks are usually responsible for eventual erasure.
A general estimate on recycled-clock loss and the
growth of the support along surviving branches is
still needed. Finite-support extinction does not
justify unrestricted extinction with a growing
support. The other open problem, unbounded zero-phase
last labels on canonical seeds, remains separate.
No twin-infinitude proof, no Lean verification, no
canonical Lean target or sibling branch changed.
