# Restricted band extension: first-repeat control and local displacement

2026-11-26 JST. Continuation of 56614c075015b8f68e89d5bafe2e9ca895e494e0.
Exact simultaneous cutoff perturbation, first-repeat CRT bound, and
a local truncated displacement estimate without enumerating the
enlarged period. Paper deductions and executed finite audit.
No Lean kernel verification or twin-infinitude proof.

## 1. Simultaneous extension and its exact first-use law

Let A be a finite set of odd primes containing 3, with seed period
P=4 product_(q in A) q. Start canonical seeds X=0 mod6 with
v=X/2+3. Let H be any set of primes larger than all primes of A,
contained in [y,2y]. The full enlarged period is P product_(p in H)p.
Let L be a uniform physical gain cap for every consecutive A-only
run from an arbitrary even offset and clock phase. The primorial
wall supplies such a cap, and the offset-only DP in 56614c0 can
improve it for small A.

For every old seed residue, follow its exact A-only path. For each
p in H, mark the p-residue classes in which the first p-clock
strictly preempts some old clock, together with the two classes
giving eligibility at the old terminal. Call this set C_p(X).
This is the one-prime union construction of 56614c0; it can be
computed entirely from the old path. No new prime is selected iff
the seed avoids every one of these sets. Indeed before the first
new prime selection the trajectory is exactly the old path.
At any preemption opportunity a new prime must win (not necessarily
the particular prime marking that opportunity). CRT independence
holds across prime residues conditional on the old seed residue,
not across successive events.

Consequently the exact conditional probability of any new label is

    1 - product_(p in H)(1-|C_p(X)|/p).

In particular if y>6L+5, no preemption of the old initial trajectory
is possible by 56614c0: d>=0 for restricted trajectories,
w<=3(p-1), and the old total gain is <=L. The only opportunities
are the two terminal eligibility residues per p. Thus

    Pr(any H-label) = 1-product_(p in H)(1-2/p).       (1)

This holds for every old seed residue. Write S=sum_(p in H)1/p
and M=floor(L/2)+1. For the full dyadic prime band S=O(1/log y).
All probabilities below refer to uniform canonical seeds in the
FULL enlarged period. No assumption of randomness in the actual
MIN clock competition is needed.

## 2. Fresh labels and the first repetition

Assume y>6L+5. If the high subsequence is p_1,p_2,..., its first
source x_1 is the translated old terminal. For each successive pair
the intervening A-only gain E_i belongs to {0,2,...,2 floor(L/2)}.
Hence

    x_i=x_1+sum_(k<i)(p_k-1+E_k),
    x_i=e_i mod p_i, e_i in {1,-1}.                 (2)

Consecutive high labels cannot coincide: as in 56614c0 a repeated
label with no intervening different high label requires E>=p-1,
contrary to L<y-1. This is independent of phase and deficit.

If the first h high labels are distinct, for each choice of labels,
orientations and intervening gains, (2) fixes one seed residue at
each of h different primes conditional on the old seed residue.
Its probability is product 1/p_i, as an upper bound on actual
realization. Thus

    Pr(first h high labels exist and are distinct)
        <= 2^h M^(h-1) S^h = 2S(2MS)^(h-1).        (3)

For the FIRST repetition at position j>=3, let p_j=p_i, i<=j-2.
The first j-1 primes are all distinct. Subtracting the two source
congruences in (2) gives, for an integer k,

    sum_(t=i+1..j-1) p_t
        = (k-1)p_i+(j-i)-sum_(t=i..j-1)E_t+e_j-e_i.

The original source displacement is at most (j-i)(2y+L)
and nonnegative, so k has at most 4j+3 possible values.
Fix all distinct primes except p_(j-1), all E's, orientations,
and k. Then p_(j-1) is determined; if it is a valid new prime,
its CRT weight is <=1/y. The remaining j-2 distinct primes have
reciprocal-weighted sum at most S^(j-2). Therefore

    Pr(first repeat at j)
      <= 2^j (j-2)(4j+3) M^(j-1) S^(j-2)/y.        (4)

This estimate counts actual path opportunities via necessary
congruences; it does not assume that all candidate words occur.
The relation is about the FIRST repetition, not arbitrary
later repeat positions in an already repeated word.

If 2MS<=1/2, summing the polynomial-times-geometric series in
(4) gives the uniform bound

    Pr(any repeat) = O(M^2 S/y).                    (5)

This includes every possible first repetition in the entire
finite trajectory; the sum may safely be extended to infinity.
By (3), the expected number of high events on repeat-free paths,
weighted by their probability (not conditioned on repeat-free),
is <=2S/(1-2MS).

Write G for terminal displacement in the enlarged system.
The wall ensures finite termination, but its bound on G may be
exponentially large. On repeat-free trajectories, G<=L+(2y+L)h
where h is the number of high events. On repeated trajectories
only use min(G,D)<=D. For ANY truncation distance D,

    E[min(G,D)] <= L+(2y+L)*2S/(1-2MS)
                       + O(D M^2 S/y).             (6)

In particular if L=o(log y) and D=y^2, then
E[min(G,y^2)]=O(L+y/log y+y M^2/log y)=o(y^2).
No untruncated mean upper bound is implied by (6); rare repeated
histories can have very large full terminal displacement.

## 3. Local transfer using only two high labels

The large enlarged period is not needed for a weaker but useful
local estimate. Take canonical roots X in [R,2R), R comparable
to y^2 (or R>=c y^2 for fixed c>0), and keep y>6L+5.
Every first high source lies in [R,2R+L), within L of its root.
It has at most floor(L/6)+1 distinct possible canonical origins.
For a fixed high prime p and side there are O(R/p+1) such
source offsets. Summing over H using the prime upper bound
gives

    #roots with any high event = O(R(L+1)/log y).

For two high events, the labels p,r must be distinct. Given
p,r, the two orientations and E_1, the congruences

    x_1=e_1 mod p,
    x_1+p-1+E_1=e_2 mod r

fix one class modulo pr. The number of possible sources in
[R,2R+L) is O(R/y^2+1). There are O(y/log y) choices per
prime, M possible relay gains, and O(L+1) possible roots
per source. Hence

    #roots with at least two high events
       = O(R(L+1)^2/log^2 y).                       (7)

This is an upper bound on the number of roots, with no
assumption of uniformly distributed terminal basins.
On the no-high paths G<=L. On one-high paths G<=2L+2y.
Use min(G,R)<=R for the remaining paths. Therefore, over the
N=Theta(R) roots in the actual local slab,

    (1/N) sum_X min(G_X,R)
       = O(L+y(L+1)/log y+R(L+1)^2/log^2 y).         (8)

For L=o(log y) and R comparable to y^2 this is o(R).
This is genuinely local, not a full-period-to-short-interval
equidistribution claim. It applies to all actual restricted
clock paths in this sparse-base/dense-band regime.

There is a sharper local bound for the first return word
p,r,p. For each p, E_1,E_2 and three orientations, the
relation from section 2 determines r up to O(1) choices
of k. There are O(y/log y) p choices, M^2 relay choices,
and O(R/y^2+1) possible sources by the two-prime CRT.
Counting roots as before gives

    #roots whose first three high labels are p,r,p
       = O(R(L+1)^3/(y log y)).                     (9)

The polynomial saving here is stronger than the two-label
bound, but does not bound returns later in a long word.

## 4. Remaining dense-cutoff problem

These results cover adding a dense prime band to a base whose
arbitrary-phase run cap satisfies L=o(log y). They do NOT cover
adding [y,2y] to all primes below y: the latter cap cannot be
assumed small, and the previous full-period lower bound
E G=Omega(y/log y) even rules out that cap for full initial
segments of primes. The restricted terminal may still have
composite neighbors because intermediate primes are omitted.
Consequently (8) alone is not the short termination theorem
needed for twin infinitude.

The concrete missing estimate is a replacement for the uniform
small relay cap in (3)-(9), controlling the actual origins
and lower relay lengths under repeated dense-band additions.
The exact conditional first-use law in section 1 remains true
without a small cap, but its residue sets may be large. The
analysis does not treat them as independent across trajectory
steps. No bound for the full-cutoff mean displacement in slabs
R comparable to y^2, and no proof of twin infinitude.

## 5. Executed audit

Source research/min_local_restricted_band_extension_audit.mjs,
commit 72a6a718a5cdf58aeb6ac88ae60d354f20a1c03a,
blob 2db1b9e5a57b082ccbe33cee016f828ebec9e419.
Exact remote readback and re-execution with identical counts.
Run: node research/min_local_restricted_band_extension_audit.mjs.
Executed in ECMAScript tool runtime, not a separate Node/Lean run.

Four complete enlarged-period controls (finite prime subsets
of dyadic bands, A and H as specified in the script):
4,462,812 canonical root incidences, 1,331,581 events,
843,432 first-high incidences, 127,728 second-high,
19,835 third-high, and 8,649 first-repeat checks.
All exact first-use product counts and finite inequalities
passed. The finite first-repeat upper bounds are very loose
and do not measure the asymptotic constant in (5).
All trajectories in these controls terminated within y^2.
For A={3}, H={31,37,41,43}, 4,044,322 roots and 8,649 repeats
(first at position 3:7552, 4:966, 5:131); maximum observed
high count 6. Example X=24270276: first high labels 43,41,43,
with low relay gains 0,2; first repeat obeys k=2.

Separate local controls use ALL primes in [y,2y], with sparse
base alphabets and a displacement truncation R:

    y       R      L    roots    >=1 high  >=2 high  repeat   mean min(G,R)
    31      10000   4     1667      513       136       3        17.8884
    103    100000  16    16667     4028       996      32        50.1700
    293   1000000  46   166667    32813      6246      56       109.2770
    907   1000000 148   166667    23641      3298       0       223.2147

351,668 root incidences, 907,862 actual events,
10,676 two-label CRT controls, 60 first-three return controls,
91 total first-repeat incidences. The finite L values do not
satisfy the asymptotic L=o(log y) requirement as a sequence;
the tests check exact relations and finite upper counts.
No failed assertions. No changes to canonical Lean targets
or sibling branches.
