# Sieve on relay displacements and rough endpoint entropy

2026-11-26 JST. Continuation of e7520f52cfcac0419533b1d8ef2a1a7818a72ba0.
The aggregate-budget theorem counted all nonnegative gain vectors.
Here rough high sources reduce the number of possible relay gains
at every rough endpoint. This is a uniform upper count of actual
anchor wait; no lower-label word enumeration, phase restriction,
mass bound, or probabilistic clock independence. No twin proof.

## 1. Statement

Same common-boundary system: M=R/12+O(1) seeds X in [R,3R/2],
6|X, initial (X,X/2+3), stop at first arrival offset >=2R.
Only non-twin events; w<=2min(p,q(u)), total gain <3R.
For sufficiently large dyadic T set

    l=log T, m=log log T,
    A=T/l^2, U=T l^2, W0=T/l^2,
    h=ceil(16 l/log(2m)).

Choose theta in {0,1/8} and define

    B=floor(l m^(1/2-2theta)), z=floor(B^(1/20)),
    Q=2 product_(3<=ell<=z, ell prime) ell.
    Q U^h <= sqrt R.                                    (1)

The last inequality is a product-room assumption. It holds
uniformly, for example, at growing T<=exp((log R)^(1/3)).
By Chebyshev log Q=O(B^(1/20))=o(l), so Q=T^o(1).
Require T large enough that hB+3<A and z<W0/2.

An anchor has p in [T,2T), w>=W0. From it retain successive
high events (labels >=A), stopping at the first repeated high
label or hth distinct high label. Require that stopping event
to exist and all retained labels to be <=U. Let n be the number
of distinct high labels: n=h in the distinct case, otherwise
n+1 occurrences. Between successive high sources x_i and x_(i+1)
the gain E_i=x_(i+1)-x_i-p_i+1 is the sum of ALL intervening
lower gains. Require

    G=sum E_i <= n B;
    # retained high events after anchor with w<W0
         <= floor(theta n).

No restriction on individual E_i, low labels, their support,
multiplicities, phases, or number of low events.

Then the actual anchor wait of these prefixes on any one path is

    W_rough(T) << R/l^3.                                (2)

Thus summed over eligible dyadic T>=T0(R)->infinity and all M
origins, this part of actual wait is O(R^2/(log T0)^2)=o(R^2).
In particular B is of order log T sqrt(log log T) when all high
waits are long, or log T (log log T)^(1/4) when up to n/8 of
the successor waits are short. Both exceed the previous
two-rough-source B2=log T/(log log T)^4, but the new hypothesis
on later long waits is stronger. Neither result implies the
other's complete population is covered.

## 2. Uniform short-interval sieve on a relay gain

For every integer offset a and every interval of integers E
of length <=B, the number with
    gcd((a+E-1)(a+E+1), Q/2)=1
is O(B/(log B)^2)=O(B/m^2).
Indeed enlarge to a comparable length B interval. For odd
primes <=z there are two distinct forbidden roots. The explicit
two-form Selberg construction in the inherited
2026-11-26-min-primorial-record-displacement-and-supply.md,
section 3, with index cutoff z gives main O(B/log^2 z) and
error O(z^6)=O(B^(3/10)), absorbed uniformly. Here log B~m
and log z~m/20. No condition on a modulo Q is needed.
Summing the length-B blocks with exponential weights gives
    sum_(E>=0, condition) exp(-E/B) << B/m^2,           (3)
where the weight in block k is at most exp(-k). Without
the condition the corresponding sum is O(B).

Every high event with w>=W0 has both neighbors free of all
odd primes <W0/2, so every preceding gain into such a source
satisfies (3) with a=previous source + previous p -1.
Fix x0=rho mod Q and all high prime residues mod Q; then,
recursively, a mod Q is known from the earlier gain choices.
Thus (3) is a uniform bound on the weighted sum of possible
next gains for EACH fixed earlier gain history. It is not a
statement of independence. If the total G<=nB, then
exp(-G/B)>=exp(-n); hence unweighted admissible vector counts
are at most e^n times the iterated weighted sums.

For an all-distinct word of length h, there are h-1 gains
and at most floor(theta h) nonrough destinations. For a
repeated prefix with n distinct primes, there are n gains.
Fix all high prime residues EXCEPT the last distinct prime
q=p_(n-1). The first n-1 gains still have known preceding
residues, since q is not used until the final step. Discard
the final destination's roughness in this gain count, and
allow its final gain arbitrarily (weighted sum O(B)).
Among the first n-1 gains at most floor(theta n) have
nonrough destinations. Enumerate short positions (<=2^(n+1)).
For either distinct or repeated case the number of gain
vectors with G<=nB, for these fixed residues, is therefore
    << m^2 D^n,   D=C B/m^(2-2theta),                   (4)
including orientation choices and any fixed absolute
exponential factors in C. For the repeated case this is
C^n B^n / m^(2(n-1-floor(theta n))); the distinct case
has one fewer gain, so the same upper bound applies.
We can ignore parity in the upper count, while retaining
evenness of actual gains when proving return identities.
For our B, D=O(l/m^(3/2)) in both cases. This is the
improvement over the unfiltered stars-and-bars count.

## 3. Source progression counts

For fixed gains, full high prime values, orientations e_i
and initial residue rho mod Q, offsets x_i=x0+G_i are
determined up to x0. Each distinct high prime imposes
x0=e_i-G_i mod p_i. All high primes exceed z, so consistent
tuples give a single residue mod QP, P=product of distinct
high labels. By (1), QP<=sqrt R. Inconsistent tuples are
discarded.

The anchor's two rough neighboring forms, on this progression,
have distinct roots modulo odd sieve primes not dividing Q.
All p|P exceed the sieve cutoff floor(T^(1/40)). As in the
previous paper, the explicit Selberg construction gives
    # source offsets << R m^2/(QP l^2).                 (5)
Omitting primes dividing Q costs O(m^2) since Q<=T^C.
For completeness the uniform omitted-prime estimate is
prod_(ell|N)(1-1/ell)^(-1)<<log log T for 0<|N|<=T^C:
split the prime factors at log T, use Mertens below and
bound the sum of reciprocals of larger factors by O(1).
The truncated Euler product lower bound follows from the
mean-log-index Markov argument in the inherited sieve.
The error O(T^(3/20)) is absorbed by R/(QP)>=sqrt R.

Every repeated prefix has n>=2: consecutive repeated high
labels would require p_i to divide the nonzero odd integer
1+e_(i+1)-e_i-E_i of absolute value <=hB+3<A.
There are therefore at least three rough high sources in
any accepted repeated prefix: n+1-floor(theta n)>=3.
Choose the first three rough sources. Their six neighboring
shifts are distinct integers, since high source gaps >=A-1>2.
Their pairwise differences are O(h(U+B)), so their
nonzero difference product Delta has |Delta|<=T^C for a
fixed C. Omit primes dividing Q Delta and primes <=7,
retaining exactly six forbidden roots at each remaining
prime <=floor(T^(1/40)). Selberg with g(ell)=6/ell and
weights bounded by d (ell>=11) gives
    # source offsets << R m^6/(QP l^6).                 (6)
The same O(T^(3/20)) error is absorbed. The omitted-prime
Euler product costs O(m^6). This is only a fixed six-form
sieve, even though the number of high events grows.
These counts are of source offsets, not clock phases
or cohort masses; a single path visits each offset once.

## 4. All distinct and first-repeat enumeration

Let S_H=sum_(A<=p<=U)1/p<<m/l by Chebyshev in dyadic bins.
For all h distinct labels, sum (5) over rho (<=Q choices),
then the prime tuples and (4). Their residues may be taken
from the full prime tuple, so no residue enumeration of
individual primes is necessary. Weight by w<=4T:
    W_distinct << R T m^4/l^2 * (D S_H)^h.
Since D S_H=O(m^-1/2), h=ceil(16l/log(2m)), this
power is T^(-8+o(1)), and the contribution is O(R/T^2).

For a first repeat p_n=p_i, i<=n-2, write p=p_i,
q=p_(n-1). From the endpoint congruence,
    q=a p+c,
    c=n-i+e_n-e_i-sum_(j=i)^(n-1) E_j
                         -sum_(j=i+1)^(n-2) p_j,
where 1<=a<=C h U/A, c!=0 and |c|=O(h(U+B)).
The first two facts follow from positivity of the interior
high sum minus n-i+e_n-e_i and distinct primality of p,q,
as in the aggregate-budget note. Choose i, fix orientations,
rho, p mod Q, the other n-2 prime values, and gain vector.
The vector count (4) is valid without knowing the full p
value or q residue: the last gain is unfiltered. Thus c is
fixed, independent of a,p,q as actual values.

The harmonic coefficient sieve of the first-repeat-prefix
note, restricted now to p in one specified residue mod Q,
gives
    sum_(a,p,q) 1/(pq) << m^4/(Q A l^2),                 (7)
and denominator T instead of A if p is the anchor. To
verify it, subdivide p~s,q~t dyadically. For fixed a,c the
intersection interval for p has length <=min(s,t/a).
Parametrize p by its residue mod Q. Enlarge to length
comparable to min(s,t/a)/Q when needed; this length is
T^(1-o(1)) because a<=C h l^4 and Q=T^o(1).
Sieve p and ap+c on this progression, omitting primes
dividing Qac and 2, retaining two distinct roots.
The omitted-product loss is O(m^2), since |Qac|<=T^C.
The count is O(min(s,t/a)m^2/(Q l^2)), with error
O(T^(3/20)) absorbed. Weighted count <=m^2/(Q a s l^2).
Summing 1/a=O(m), O(m) q-bins, and sum 1/s=O(1/A)
(or O(1/T) for the anchor) proves (7).
The additional constraint on q mod Q is NOT imposed:
it is unnecessary for the filtered first n-1 gains.
Counting the final gain without the small-prime filter
is what permits this nested sum with fixed c.

Now sum (6) over each prime pair counted in (7), with
remaining reciprocal primes contributing S_H^(n-2).
The two factors Q in the denominators cancel the <=Q
choices each of rho and p mod Q. Combining (4), (6), (7),
the repeat-position choice (overcount by n^2), and anchor
weight <=4T, gives at fixed n:
    repeated anchor (n>=2):
       << R m^12/l^8 * n^2 D^n S_H^(n-2);
    repeated nonanchor (n>=3):
       << R (T/A) m^12/l^8 * n^2 D^n S_H^(n-2).
We may freely count compatible tuples with other primes
outside their actual orientation constraints; this only
enlarges the counts. All actual prefixes are included.
Summing the two geometric tails (D S_H=o(1)) gives
    W_repeat << R m^12/l^8 *
                          (D^2+(T/A)D^3 S_H)
             << R (m^9/l^6 + m^(17/2)/l^4)
             << R/l^3.
Together with the distinct case this proves (2). Sum over
dyadic bands using sum_(T>=T0) 1/log^3 T=O(1/log^2 T0)
and over M origins. The charges are per origin, so apply
even to already concentrated carriers of arbitrary mass.

## 5. Finite audit and limitation

Source research/min_simple_rough_relay_audit.py, commit
938b63d5525263780d9c245f6616bf064b668b2f, blob
5400fc61a4dc0f46ca90f83597c001a774650a89; exact remote
readback matches the executed local source. Uses stdlib
and existing research/min_simple_relay_budget_audit.py.
Run:
    python research/min_simple_rough_relay_audit.py 1000 10000 100000 1000000

Fixed diagnostic h=4,A=T/4,U=8T,W0=max(15,T//8),B=32,
Q=210 (small primes 3,5,7). Observed G+3<A is imposed
instead of hB+3<A. Enumerated all 210 translated length-32
gain intervals; each has 4 to 6 integers meeting the
small-prime roughness test (including odd gains in count).
Exact total count verified by averaging the residues.
Literal tick GCD tests at R<=10000; actual origin replay
at all four scales. For R=1000000:
    M=83334, non-twin visits=2564511, total wait=66822800
    anchors=233398, anchor wait=49479900
    budget prefixes=11354, budget wait=2492721
    prefixes with short interior=7787
    all-rough prefixes=3567, wait=738818
    all-rough first repeats=113
    all-rough with some gain>B=890
    checked relays=10656, positive relays=7072.
206 distinct tuples. At R=100000, 79 all-rough prefixes
including one first repeat; 26 have some gain>B. None
at R<=10000. All integer checks passed, including modular
source reconstruction, rough relay membership, final-gain
dependency, first-return relation, six distinct shifts and
their good-prime roots. The finite h=4 case does not exercise
a positive floor(n/8) allowance; the analytic exponential
bound and asymptotic sieve constants are not numerical
claims. No Lean run.

The improvement covers a larger average relay budget
for mostly rough high words. It does not cover arbitrary
moderate or long relay gains, frequent short high waits,
polynomial-scale words without product room, or low
labels below T0. Combining with previous charges does not
yet show that the residual total wait is o(R^2). Next
target is to use the clock dynamics or the mass/phase
constraint to control relay gains outside the logarithmic
budget, rather than just improve an already small class.
