# Negative-time inverse suffix erasure and terminal-label exclusion

2026-11-26 JST. Continuation of 376c97e80d9cc67ef105269037f27a964a0820a6.
Investigate the negative MIN via exact inverse tick maps, instead of
estimating the entire forward displacement. Establish unconditional
small-prime erasure and a finite certificate excluding every tested
non-twin prime from zero-phase termination of canonical seeds.
No asymptotic extinction theorem, Lean verification, or twin-infinitude proof.

## 1. Tick maps and exact inverse

Use remaining distance a=-u, even and positive. For each k>=1 the
tick n=-k has candidate odd prime set

    C_k = {p odd prime: p|k}           if k even,
    C_k = {p odd prime: p|(k+2)}      if k odd.

Set e_k=-1 for even k and +1 for odd k. At this tick the least
candidate with a=e_k mod p is selected, if any. Thus F_k(a)=a-p+1
if there is such a p, and F_k(a)=a otherwise. These maps are defined
on all even integers as arithmetic maps; any inverse trajectory
ending at a positive a consists only of positive states.

For an even target b, the inverse image is exactly

    {b : F_k(b)=b}
      union {b+p-1 : p in C_k, F_k(b+p-1)=b}.

The second test includes least-label priority. Simply accepting
every congruent predecessor would produce spurious inverse states.
For a target b at time -1 AFTER that tick, put S_0(b)={b} and

    S_k(b)= union_(c in S_(k-1)(b)) F_k^(-1)({c}).

Then S_k is the exact set of states at time -k-1 AFTER that tick
which can reach b at time -1. Empty sets remain empty under every
further inverse step.

If P>=5 is the last prime of a canonical trajectory ending at
phase H=0, necessarily b=P-1 at time -1. The state before tick
0 has this distance and the minus clock at 0 uses P. Since
A>=P-1, the canonical birth time -A/2+3 is <= -(P-1)/2+3.
Consequently extinction S_K(P-1)=empty at any

    1<=K<=(P-1)/2-4

rules out this P for ALL canonical seeds, not merely sampled seeds.
The stronger condition follows from the exact canonical-line test:
a seed A with 6|A, A>=12 and K=A/2-4>=1 ends via P at H=0
iff A belongs to S_K(P-1). The same test works for K=0 with
birth time -1, when relevant. The forward dynamics from a canonical
seed has nonnegative height and cannot hit 0 before time 0:
a last minus label p=a+1 requires time a multiple of 2p,
whereas at a negative firing the nonnegative source height gives
n>=-a/2+1>-2p. If P is prime, the remaining target P-1 at
time -1 necessarily jumps to 0 at time 0. The exact line test
therefore introduces no fictitious earlier stopping.

## 2. Uniform width bound

Every inverse step either preserves the distance or increases it
by p-1. Write

    U(K)=sum_(1<=k<=K) max({p-1:p in C_k} union {0}).

Then S_K(b) is contained in [b,b+U(K)] intersect the even integers,
so |S_K(b)|<=1+U(K)/2. The crude bound is O(K^2), independently
of b and of the magnitude of the original seed. More sharply,
each prime p<=K+2 can occur at most O(K/p+1) times in the candidate
sets. Bounding the maximum by the sum over candidates gives
U(K) <= O(sum_(p<=K+2) (K+p)) = O(K^2/log(2+K)),
using the standard elementary upper bound for pi(K+2).
No inverse-tree exponential bound is needed: equal states merge.
This bound is on widths, not on extinction time or mass.

## 3. Erasure by a prime and the cases q=3,5,7

Suppose P>=11 is prime and P-2 composite, with least prime factor q.
At tick n=2-q the odd candidate set is exactly {q}. The map
moves every a=1 mod q to a=2 mod q, leaving other residues
unchanged. Its image contains no a=1 mod q. Since b=P-1=1 mod q,
the desired final state is erased at this tick. It can survive
the entire suffix only by arriving again after that erasure.
The later even ticks have labels dividing k, the later odd ticks
have labels dividing k+2, and every arrival must obey the exact
inverse condition of section 1.

For q=3 the erasure is at n=-1 itself, with no later tick.
Hence S_1(b)=empty.

For q>=5, primality of P and least-factor condition imply b=0
mod 3. The last tick -1 is a plus-3 map: a moved by 3 arrives
at residue 2 mod 3. It cannot arrive at b=0 mod 3. Thus the
only predecessor at tick -1 is b. Tick -2 is the identity.
For q=5 tick -3 is the erasure of b, proving S_3(b)=empty.

For q=7, after undoing -1 and -2, tick -3 is plus-5.
As P>7 is prime, b is not -1 mod 5. If b=1 mod 5 it has
no predecessor at -3; if b=0 or 3 mod 5 only b is possible;
if b=2 mod 5 the candidates are b and b+4. Tick -4 is
identity. At -5 (plus-7), b=1 mod 7 is erased, and
b+4=5 mod 7 can have only its identity predecessor.
If b+4 was present, its residue mod 3 is 1.
Tick -6 (minus-3) cannot move anything into residue 1:
only residue 2 is moved, to 0. It therefore leaves only
b+4 in the inverse set. Tick -7 (plus-3, since -9 has
only the odd prime 3) erases residue 1. Thus S_7(b)=empty.
This proof does not use a bound on P beyond P>7.

Corollary: for canonical A>=24, a zero-phase final P>=11
with composite P-2 must have least prime factor q>=11.
For q<=7 the required suffix starts after the seed birth.
For large P the birth-time condition holds automatically.
The q=7 exception after only five inverse ticks is real:
the residue b=162 mod 210 survives that shorter suffix.
The extra two ticks are essential in this argument.

General finite suffix tests are periodic. Put
Q_K=2 prod_(p in union C_1..C_K)p. Each F_k commutes with
translation by Q_K; membership in the image of the suffix
is therefore periodic mod Q_K. One can determine the
surviving residue classes of b with a specified q using
either exact forward images over a full period or the
inverse recursion. No assertion that the erasure for
q=3,5,7 extends by the same argument to larger primes:
for q=11, K=9 all 15 candidate residue classes survive,
and for q=13, K=11 131 of 135 survive.

## 4. Finite exhaustive target exclusion

Source research/min_local_negative_suffix_erasure_audit.mjs,
final commit a8a854ebda745e97369e1950c7a207bf3e38a373,
blob ee8cbb16e3feb1593ae1250de98c1b7252c6e397.
Execute: node research/min_local_negative_suffix_erasure_audit.mjs.
Actually executed in ECMAScript research runtime, fetched at the
exact commit and re-executed identically. No separate Node or Lean.

For EVERY prime P in [1009,300000], classify P-2 by an exact
smallest-prime-factor sieve. For composite P-2 run the exact
inverse suffix to K=min(768,(P-1)/2-4), stopping early on
extinction. For every survivor extend to min(8192,(P-1)/2-4).
This deliberately tests all prime targets, not just labels
observed in forward canonical simulations.

    prime targets                         25829
    P-2 prime                               2959
    P-2 composite                          22870
    composite targets extinct by first cap 22770
    survivors extended                       100
    extended survivors extinct               100
    final non-twin survivors                   0

The longest extinction was at P=241333, q=373, K=4315,
with maximum inverse width 406. All extinction depths used
are less than or equal to the canonical birth-time bound.
Thus, as a finite computational corollary of section 1,
no canonical seed of ANY size can terminate at phase zero
with last prime P in [1009,300000] having composite P-2.
The qualification on H=0 is essential.

For twin targets verify the stationary state b=P-1 at each
tick up to the first cap: neither neighbor has an odd prime
factor in that time range. This does not claim all inverse
states of twin targets are stationary. Check six small
periodic forward-image controls against inverse sets.
Additionally compare independent forward simulations from
a sparse set of canonical seeds up to 300000: 31440
events, 1515 actual phase-zero suffix checks, one nonzero
phase case. All assertions passed.

Total inverse ticks and width checks 1933995; accepted
inverse-edge checks 79819528; forward witnesses for nonempty
sets 1762; stationary twin tick checks 2270271.
These counts include repeated controls and longer reruns.
Exact integer arithmetic; no extrapolation from the data.

## 5. Remaining analytic target

The finite inverse extinction property is stronger than
the forward observation in 376c97e, because the tested
non-twin terminal labels are excluded for ALL canonical
origin sizes whenever H=0, not just for the tested origins.
But the finite range of excluded P does not prove a general
extinction theorem. A concrete new conjecture is that for
all sufficiently large non-twin primes P the exact suffix
S_K(P-1) becomes empty for some K<=(P-1)/2-4.

Even proving that conjecture would not suffice by itself:
one also needs unbounded zero-phase final labels from
canonical roots (or another way of obtaining large prime
survivors). The existing forward last-jump criterion remains
a separate sufficient condition. The next analytic problem
is to understand whether inverse branching can indefinitely
restore states after their plus-prime erasure, and how to
bound that restoration without assuming the desired
twin-prime distribution. No asymptotic extinction or
zero-phase synchronization is established here.
No canonical Lean targets or sibling branches changed.
