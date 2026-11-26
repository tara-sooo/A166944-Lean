# Two-deficit macros, alternating words and five-condition pair supply

2026-11-26 JST. Continuation of 89e5bacf996c5e4c53c02bbf38c3c1b0b74491c1.
Exact ordinary uncut MIN. Paper deductions and executed finite controls.
No Lean verification, novelty claim, or proof of twin infinitude.

## 1. Short-clock two-deficit macros

Write d=2v-u. Consider sources 6|u, d in {0,6}. Define a main
event to have prime p>=13 and post-deficit d'=0 for minus-side
(e=+1), d'=6 for plus-side (e=-1), where p divides u-e.
Equivalently its actual wait satisfies 2w=p-1+d'-d.
These are actual first events, not arbitrarily chosen clocks.
For minus side u=pm+1, the even clock gives m=3 mod 4;
for plus u=pm-1, the odd clock gives m=1 mod 4.
In either case u=p-1 mod 4, hence u=0 mod 12 if p=1 mod 4,
and u=6 mod 12 if p=3 mod 4.

The raw arrival u+p-1 is 0 mod 12 if p=1 mod 6,
and 4 mod 12 if p=5 mod 6. In the first case no relay is needed.
In the second put J=u+p-1, d'=0 or 6:
- d'=6: the very next tick is minus-3, wait 1, gain 2.
  The arrival is 6 mod 12, deficit 6.
- d'=0: the next four ticks have relative divisor candidates
  from -3,5,1,9 (alternating plus/minus). The first plus-3
  is not eligible since J+1=2 mod 3. At tick 2, 5 wins
  iff J-1=0 mod 5. Otherwise the first hit is minus-3 at
  wait 4, gain 2, returning to 6 mod 12, deficit 6.
  If 5 wins, the arrival is 8 mod 12, deficit 0;
  plus-3 then minus-3 each fire at wait 1. This returns
  to 0 mod 12, deficit 0, with total relay gain 8.

Thus append exactly the indicated relay (none, 3, or 5,3,3)
to the main event. A macro maps the two-deficit domain to itself.
Its physical gain is p-1+E, E in {0,2,8}.
For large sources the relay sources cannot be twin centers,
since their residues mod 3 are nonzero.
The original ordinary MIN remains unchanged; other events can
occur between macros and are not assumed to fit this definition.

For d=0 and d=6 at the SAME offset, the latter clock starts
three ticks later. At d=0 the first three ticks can contain
only a minus-5 at tick 2 (u=0 mod 12, u=1 mod 5), or
a minus-7 at tick 3 (u=6 mod 12, u=1 mod 7).
This follows by eliminating u from the clock and neighbor
divisibility, with possible odd factors of -3,3,-1,5,1,7
and 3 ineligible. If neither early event occurs, the two
initial deficits select the same main event whenever either
does, with waits differing by 3 and identical arrival state.
This identifies when the two start phases can be collapsed.

More generally for an actual event with d,d' in [0,H],
p>max(H+6,12), the firing congruence forces d'=0 (minus)
or 6 (plus). Indeed d'=0 mod p or d'=6 mod p respectively.
If its wait exceeds 6 then 3 cannot divide either neighbor,
so 6|u. This explains why the two-deficit states arise
after large events within a bounded-deficit corridor.
It is not a proof that the actual orbit stays in such a corridor.

## 2. Label cap and mixed gain accounting

For a non-twin main event with p>=37,

    p^2 <= 3(u+1).                                    (1)

If p>sqrt(u+1), the selected neighbor is pm with m<p.
If m=1, the other composite neighbor gives w<=2 sqrt(u+1),
whereas w>=(p-7)/2 and u+1<=p+2, impossible for p>=37.
If m>1 composite, it has q<=sqrt(m)<sqrt(p), whose competing
clock fires within 2q<(p-7)/2. Thus m is prime; m<=7 is
excluded by 2m<=14<(p-7)/2. For m>=11 the candidate
same-side clock has wait (k m+c-d)/2, k=1 or 3, with
c=-1 on the minus side and c=5 on the plus side, by the
exact firing congruence. It is positive. The selected clock
has wait (p+c-d)/2, hence p<=3m and (1).
For 13<=p<37 use the trivial cap p<=31. The unqualified
p^2<=3(u+1) is FALSE: u=162,d=6,p=23,w=8, minus,
neighbors 7*23 and 163. The prior single-deficit special
plus cap is not changed by this exception.

Same label and same orientation at two main sources implies
a drift divisible by 12p (source mod 12 determined by p).
Even across arbitrary other events, there are at most
D/(12p)+1 such occurrences in a half-open interval of width D.
Let J count distinct (p,e) pairs among main events (not
the number of events), let B count the gain of all other
events, including any relay ticks that are not main events,
and stop a crossing at first arrival >=X+D. If all sources
are non-twin, put Pmax=max(31,sqrt(3(X+D+1))). Then

    D <= B + J D/12 + J Pmax.                         (2)

All final events included. For fixed J0<12, rho>=0 with
J0/12+rho<1, D=ceil(C sqrt X), a sufficiently large reset
with J<=J0, B<=rho D and C>sqrt(3)*J0/(1-J0/12-rho)
must encounter a twin. J<=2K if K counts labels only.
This extends the gain certificate to both signs and both
deficits, at the cost of weaker constants. If all macro
main labels >=T, the total gain of their appended relays is
at most 8/(T-1) times their main gain, including a truncated
final relay. Thus they may be charged multiplicatively instead
of included in B. The unbounded favorable-reset supply is open.

## 3. Two-label macro runs and an exact twin-label characterization

Adjacent macros cannot use the same label p: the two selected
neighbor congruences would give p dividing E+e-1-f, a nonzero
odd integer in [-3,9]. Consequently a two-label macro word
alternates. For a triple p,r,p with orientations e,f,g and
first two relay gains E,F,

    r = k p + 2+g-e-E-F,   k odd.                     (3)

This follows from the drift p+r-2+E+F and source congruence
difference g-e modulo p. The additive constant is in [-16,4].
If the middle label r is smaller than the endpoint label p,
k=1 necessarily, so p-r<=16. In a four-word p,r,p,r at least
one triple has this ordering. With both primes >=37, both
instances of (3) then have k=1, since |r-p|<=16 and k>=3
would require the larger prime >=3*smaller-16.
The two occurrences of either label are separated by at most
2*label+30<12*label. Their signs must therefore be opposite.

Let c=r-p, first two signs e,f, and first three relay gains
E,F,G. The two triple equations are now exactly

    c=2-2e-E-F,  -c=2-2f-F-G.                         (4)

The possible residues mod 12 are 1,5,7,11, and source class
is S(p)=0 or 6 according to p mod 4. Impose the three
transitions S(next)=S(current)+current-1+relay mod 12.
For p=1 mod 6 the relay is 0, for p=5 mod 6 and sign -1
it is 2, otherwise it is 2 or 8. Enumerate c even nonzero
in [-16,16], signs +/-1, and these relay possibilities.
There are 296 combinations after imposing residue agreement;
the exact finite enumeration leaves ONLY:

    p mod12  r mod12  c   e   f   E F G
        5        7    2  -1  +1   2 0 2
        7        5   -2  +1  -1   0 2 0

Hence every actual alternating four-macro word with labels
>=37 contains a twin PRIME LABEL pair, even if all source
offsets themselves are non-twin. No crossing length or
large-label/offset scale relation is needed for this implication.

In fact no two-label contiguous macro run can have length 5,
even for labels >=13. A length-5 word starts either with the
larger label (which occurs 3 times, pre-span <=4*larger+28
<12*larger) or the smaller. In the latter case the triple
with larger endpoints gives larger-smaller<=16 by (3),
so the smaller's 3 occurrences have pre-span at most
4*smaller+60<12*smaller. Three signs force a repeated
orientation, contradicting the 12p spacing in either case.
Under finite twins, sufficiently large labels therefore allow
at most 3 consecutive macros on two labels.

## 4. Precisely which twin labels can generate the four-word?

Write the smaller label p, larger r=p+2, p=5 mod 12.
In both surviving patterns the four main sources form an
arithmetic progression with step h=p+1=r-1.
For labels >=37, w>=15, so neither neighbor at any main
source may have factor 5 or 7 (otherwise a clock within
2*5 or 2*7 would win). For q=5, four equally spaced centers
with both +/-1 forbidden exhaust all residue classes
unless h=0 mod 5. For q=7 direct finite enumeration gives
h=0,+/-1,+/-2 mod 7; the +/-1 cases are already impossible
because p=h-1,r=h+1 are primes >7.
Together these force

    p in {29,209,389} mod 420.                         (5)

Conversely for any fixed twin pair p,p+2>=37 satisfying
(5), a four-macro word exists from arbitrarily large ordinary
resets X divisible by 12. Construct the first pattern in
section 3. Impose X=-1 mod p, X=2 mod r.
Across main sources X+i h, i=0,1,2,3, the p residues are
-1,0,1,2 and the r residues 2,1,0,-1. These realize the
required orientations and no unwanted use of p,r.
For each other odd prime q<=r+7 avoid X+i h=+/-1 mod q.
For q=3 this follows from 12|X; for q=5 choose X=0 mod 5
(which also prevents the optional 5 relay after the third
main event); for q=7 an allowed residue exists by (5).
For q>=11 there are at most 8 forbidden residues.
CRT combines the choices. The main short-clock waits are
(p-1)/2, (r-7)/2, (p-1)/2, (r-1)/2; the two relays
are minus-3 at waits 1 and 4 respectively. Their pre- and
post-deficits follow section 1. At each main tick through
the claimed first hit, all possible competing labels divide
the relative odd integers d+2t+1 (even clock) or d+2t-5
(odd clock), of absolute value <=r+7. So the exclusions
are sufficient, not merely necessary.
Fresh distinct primes >r+7, one per source, can be imposed
as factors of the opposite neighbor. Taking sufficiently
large CRT lifts makes both neighbors composite at all four
main sources without changing the word.

Thus unbounded large alternating-word label supply is
equivalent to unbounded twin-pair supply in the three
classes (5), a restricted twin-prime statement. This does
not prove the general conjecture; direct CRT construction
of the four-word from already-known labels cannot prove
their unboundedness. The route needs an independent MIN
argument forcing these alternating patterns. This precise
equivalence also shows the limitation of treating their
repetition as a generic arithmetic construction.

## 5. Upper sieve for near-square-root consecutive macros

Use the two non-twin main sources x in [R,2R), y=x+p-1+E
with both labels p,r>=eta sqrt(R), fixed eta>0, R large.
The caps give p,r=O(sqrt R), y<=3R; write x=pm+e,
y=rn+f. Then

    rn=p(m+1)+a, a=E+e-1-f in [-3,9], a odd nonzero.

Both waits are asymptotic to half their labels, so both
neighbors at each source avoid all odd prime factors
<=c_eta sqrt R for sufficiently small c_eta. The selected
neighbors are proper semiprimes: primality would give
label comparable to R, contradicting the non-twin cap;
three factors with multiplicity would exceed 3R.
In particular r,n are both prime. For fixed p,e,f,E,
r,n range over intervals of length O_eta(p), with
rn=a mod p. For any small sieve prime ell>7, ell!=p,
the following five conditions are excluded:

    r=0, n=0, rn=p+a, rn=p+a-2e, rn=-2f (mod ell).

The first axes exclude both target factors; the next two
are source selected/cofactor and opposite-neighbor roughness;
the last is target opposite-neighbor roughness.
For the set C={p+a,p+a-2e,-2f} let k be the number of
distinct NONZERO residues of C modulo ell. The exact
forbidden-pair count is

    rho(ell)=2ell-1+k(ell-1).

Indeed the two axes have 2ell-1 points and each nonzero
product fiber ell-1 disjoint points. Generically k=3,
so g(ell)=5/ell-4/ell^2. Exceptions occur only at divisors
of a nonzero integer Delta formed by the product of the
three constants and their pairwise differences; |Delta|
=O(p^4). Nonzero follows from p>=37, |a|<=9.

Apply the elementary modular-hyperbola Fourier estimate
from pinned parent's min-direct-modular-hyperbola-three-root-source-sieve
(sections 2--4): each residue pair mod squarefree d coprime
to p has count N0/d^2+O_eta(p^(3/4)log^2 p), N0=O_eta(p).
The inherited estimate derives the elementary complete
Kloosterman O(p^(3/4)) bound by Cauchy-Schwarz and a second
moment; no Weil theorem is invoked here. Sieve only
nonexceptional primes 11<=ell<=z=floor(p^(1/128)).
The same explicit Selberg weights |lambda_d|<=d have
main term N0/G(z). Total error after squaring is
O_eta(p^(3/4)log^2 p*z^8)=o(p/log^5 p).
The Euler-product/weighted-log Markov truncation in the
parent gives
G(z)>>log^5 p/product_(ell|Delta)(1-1/ell)^(-5).
The denominator is O((log log p)^5): split at log p,
use Mertens for smaller primes; above log p there are
O(log p/log log p) divisors and their reciprocal sum is
O(1/log log p). Thus fixed p has at most
O_eta(p (log log p)^5/log^5 p) candidate pairs.
Summing p over its O(sqrt R/log R) prime possibilities
(Chebyshev) and the constant sign/relay options gives

    # distinct near-scale non-twin macro-pair source offsets
       <<_eta R (log log R)^5 / log^6 R.               (6)

The bound is for offsets, not multiplicity of origins;
each fixed tuple determines x, and both initial phases
could count the same offset. It does not imply a pair-free
long path or any lower bound on the supply. It complements
the exact four-word obstruction: near-scale repeated macro
routes are arithmetically sparse, and an abundance argument
cannot simply regard consecutive large labels as independent.

## 6. Executed audits and persistence

Source 1: research/min_local_two_deficit_macro_audit.mjs,
commit 5338b7cb919e592918b5280198644285462e7cc7,
blob 03814123bffe46cdd943934f5bfac665ac65d5e0.
Run node research/min_local_two_deficit_macro_audit.mjs 1000000.
Actual ECMAScript execution in research runtime, exact remote
readback and re-execution. No Node process or Lean process
invoked. All 333330 states 6|u, 12<=u<=1000000, d=0,6:
94804 macros, 78470 non-twin main sources, relay gain counts
0:43087, 2:31781, 8:3602. 101489 literal GCD tick controls.
Non-twin near label >=sqrt(u)/4: 11347 state incidences.
22658 consecutive macro-pair incidences with first non-twin,
506 with both non-twin and both labels >=sqrt(first u)/4.
Of canonical d=6 starts, 256 such non-twin near pairs.
365 repeat congruence controls, 3618 five-condition roughness
controls, 540 exhaustive finite local-density checks.
The first cap trial failed at u=162,d=6,p=23; the final code
retains this finite exception and checks the corrected p>=37
cap. All final assertions passed. All these counts are state
incidences, not distinct trajectories or a density estimate.

Source 2: research/min_local_alternating_macro_audit.mjs,
final commit da744fe89e1caa815195403d89b26e57462a20e9,
blob a3bc00a34b6292fed3bffd7774d1688c7fad53d7.
Run node research/min_local_alternating_macro_audit.mjs.
296 exact residue configurations, two survivors listed above.
Actual BigInt CRT construction for known pairs (809,811),
(1049,1051), (1229,1231); chosen roots of 348,456,535 decimal
digits; 1620+2100+2460=6180 literal GCD ticks checked.
All four main sources in each example forced non-twin by
proper factors on both sides. For p=809, h=810, main source
shifts 0,810,1620,2430; full labels 809,3,811,809,3,811
with waits 404,1,402,404,4,405. Deficits at main sources
6,6,0,6. This verifies actual realizability of the surviving
word, not unbounded label supply or a square-root crossing
(the chosen roots are extremely large compared with labels).
Exact remote readback and re-execution passed.

## 7. Next obstruction

The two-deficit macros enlarge the domain of the explicit
gain certificate, and alternating four-words identify twin
labels without needing a complete crossing. But unbounded
four-word supply is exactly the restricted twin-pair problem
above; the CRT controls do not independently supply it.
The next useful direction is an actual recurrence argument
on mixed paths forcing either a twin center or these words,
or proving unbounded favorable resets via the weaker gain
certificate (2). In particular control the gain in events
leaving the two-deficit domain rather than assuming it small.
The near-scale pair sieve is only an upper bound and cannot
be substituted for this missing existence argument.
No canonical Lean target or sibling branch modified.
