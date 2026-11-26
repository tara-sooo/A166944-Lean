# Three-point roughness, exact clock CRT, and short return words

2026-11-26 JST. Continuation of 9326aa8f3f471029955bca565ce9bf4cb9acaade.
Paper deductions and executed finite audit. Builds on the inherited
ordered-descent-pair sieve and elementary modular hyperbola estimate,
rather than treating consecutive labels as independent. No Lean
verification, proof of full stable transport, or twin-infinitude proof.

## 1. Setup and exact pair/clock identities

Same common-boundary reset system: R large, X in [R,3R/2], 6|X,
(X,X/2+3), exit at first U>=2R. M=R/12+O(1). Every event increases
u by p-1 and v by w, with w<=2q(u)<=2sqrt(2R+1) at non-twin
sources and w<=2p everywhere. q is the least odd factor of either
neighbor. Hence a relay of physical gain E has total wait <=3E.

Mark any subset of non-twin events in a single dyadic band
T<=p<2T. Consider three consecutive marked source offsets x,y,z
with labels p,r,t and orientations e,f,g in {-1,1}, so that
p|x-e, r|y-f, t|z-g. Orientation +1 means even firing, -1 odd.
Let the two relay gains E,F (nonnegative even integers) satisfy

    y=x+p-1+E,       z=y+r-1+F.

If E,F<=B and B<T-3, consecutive marked labels differ: if r=p,
then p divides E+e-1-f, a nonzero odd integer of magnitude <p.
Likewise r!=t. With D1=p-1+E and y=r s+f, we have the nonzero
modular hyperbola

    r s = E+e-1-f (mod p).

The actual first two firing times n,N obey
n=c_e mod 2p, N=c_f mod 2r, where c_e=0 for e=+1 and p+2
for e=-1 (replace p by r for c_f). Write tau=N-n.
The clock and relay bounds imply 1<=tau<=3E+2r. For a prescribed
integer tau, parity must match and then exactly one residue
of n modulo 2pr is possible:

    n=c_e+2p k,  k=(c_f-tau-c_e)/2 * p^(-1) mod r.

The first firing n is in an interval of length O(R) by the
time envelope. Thus for fixed pair of source offsets, labels,
orientations, relay gain, and prescribed tau, at most
O(1+R/(pr)) distinct first firing times are possible.
For tau restricted to a real interval of length A this gives
O((A+1)(1+R/(pr))). In particular with p,r comparable to
sqrt R, a prescribed tau admits O(1) clock phases, even though
unrestricted tau=O(T) need not give any saving.
If p,r,t are pairwise distinct, specifying both successive
time differences similarly fixes n modulo 2prt, provided the
parities agree. These are necessary congruences, not sufficient
for exact MIN selection. They do not bound seed mass at a phase.
This is an exact clock constraint separate from the offset sieve.

## 2. Unconditional short-return wait bound (all depths)

Consider the return word p,r,p (t=p) in the same dyadic band,
with E,F<=B<T/4 and T sufficiently large. Since z-x=p+r-2+E+F,
divisibility by p at both ends gives

    r=j p+c,    c=2+g-e-E-F,    -2B<=c<=4.

The integer c is even, hence j odd. Comparability, positivity,
and B<T/4 force j=1; c=0 is excluded by r!=p. Consequently

    r=p+2+g-e-E-F.

When E=F=0, c=2 or 4, so r>p. In particular an immediate
four-event alternating word p,r,p,r with p,r in the same
dyadic band and large cannot occur: its first triple needs
r>p and its second needs p>r. The return relation does not
assume long waits, efficiency, or reset-origin reachability.

For fixed E,F,e,f,g, the two-form upper sieve applied to p and
p+c bounds the number of prime pairs in [T,2T) by

    << T S(c)/log^2 T,    S(c)=product_(ell|c, ell>2) (1-1/ell)^(-1).

Here c!=0. For completeness, the sieve has two forbidden residues
modulo odd ell except when ell|c, where there is one. The explicit
Selberg weights and truncated Euler-product proof of the inherited
record-displacement-and-supply note, section 3, apply with this
local density. Taking cutoff floor(T^(1/10)) gives error O(T^(3/5))
and G>>log^2 T/S(c), by omitting one Euler factor for each prime
dividing c. This is an upper bound, not an assumption of any
prime-pair infinitude. The singular factor has bounded average:
expand S(c)=sum_(d|c,d odd squarefree) prod_(ell|d)1/(ell-1).
Then sum_(1<=|c|<=A) S(c)<<A since
product_(ell>2)(1+1/(ell(ell-1))) converges.
For each E and orientations, as F varies the nonzero c are distinct
in [-2B,4], so the sum of S(c) over E,F is O((B+1)^2).

For each such tuple, x is in one residue class modulo 2pr
from x even, x=e mod p, x+p-1+E=f mod r. In [R,2R) there are
O(1+R/T^2) possibilities. If T<=C0 sqrt R, with C0 fixed,
this is O_C0(R/T^2). Each actual path is strictly increasing
in x, and the following marked events uniquely determined
on that path. Summing all tuples therefore bounds the number
of actual short-return triples on ANY single path by

    <<_C0 R (B+1)^2/(T log^2 T).

Counting the waits of all three events (even with overlap,
an upper bound) costs <=12T per triple. Hence

    W_return(T,B) <<_C0 R (B+1)^2/log^2 T.                (1)

For 0<=beta<1/2 choose B(T)=floor((log T)^beta), with T large.
Sum (1) over dyadic T>=T0 tending to infinity up to C0 sqrt R.
The integral comparison for the dyadic log series gives

    sum_T W_return(T,B(T)) <<_C0,beta R/(log T0)^(1-2beta).

Summing over the M reset origins, including arbitrary merger
mass and all generations, yields O_C0,beta(R^2/(log T0)^(1-2beta))
=o(R^2). In particular beta=1/4 gives the inverse square-root
log saving. The bound can be applied to any selected marked
subsets, including significant events or stable carriers.
This is an actual unconditional removal of these return-word
waits, not another hypothesized traffic inequality.
Events with p>C0 sqrt R have total non-twin wait O(R/C0)
per origin by w<=2sqrt(2R+1) and the <3R gain budget.
If desired their contribution can be made arbitrarily small
as a fraction of R^2 by letting C0 increase AFTER taking limsup.
The fixed-C0 estimate is not stated uniformly in C0.
No bound here on returns with long relays or other repeated
words containing more than two distinct labels.

## 3. Three rough sources: seven-condition hyperbola sieve

Now mark events in [T,2T) whose actual wait is at least alpha T
for fixed alpha>0. For any such event, both neighbors avoid
odd prime factors <alpha T/2. Take T growing, T<=C0 sqrt R,
B<T/4, and consider three consecutive marked events with
E,F<=B. For each fixed p,e,f,E,F use the hyperbola from
section 1; the third label t need not be specified. With
D1=p-1+E and y=rs+f, the six rough neighboring forms of x,y,z
give the following exclusions modulo an odd sieve prime ell:

    r!=0,
    rs not in C_ell={D1-f-1,D1-f+1,-f-1,-f+1},
    r(s+1) not in H_ell={-F-f,2-F-f}.

The axis r=0 is excluded by primality of r>ell. The four
product residues have exactly m=4-nu_ell distinct elements,
where nu_ell=2*1_(ell|D1)+1_(ell|D1-2)+1_(ell|D1+2)
for ell>5, just as in the inherited ordered-pair sieve.
The two H residues are distinct. For r!=0, the two sets
of hyperbolas intersect at exactly one point for each pair
c in C_ell,h in H_ell with c!=h: r=h-c, s=c/r. These points
are distinct since a point determines both products.
Thus the exact count of forbidden residue pairs is

    rho(ell)=ell+(m+2)(ell-1)-2m+|C_ell intersection H_ell|.

In particular the local density is
g(ell)=(7-nu_ell)/ell+O(1/ell^2), uniformly. This is two
more roughness conditions than the five-condition pair sieve.
The extra third-source forms cause only O(1/ell^2)
intersection corrections, not a new singular factor in F.

For the local interval version take D=ceil(R^(15/16)),
I contained in [R,2R) of length <=D, all x,y,z in I.
The target r ranges in a length O(T) interval, the cofactor s
in a length O(D/T+1) interval (enlarge to cover any shorter I).
Put N=D/T. For each residue pair modulo squarefree d coprime
to p, use the Fourier argument in the inherited note
research/2026-11-26-min-direct-modular-hyperbola-three-root-source-sieve.md,
sections 2--3. Its elementary complete nonzero Kloosterman
bound O(p^(3/4)) applies since the hyperbola right side is
nonzero. The geometric-sum normalized Fourier l1 norms of
the two interval progressions are O(log p) and
O(log p+N/p) respectively; this is true even when N<p.
Replacing progression cardinalities by interval length/d
costs O(1+N/p), so the count per residue pair is

    N0/d^2 + O(p^(3/4) log^2 p (1+N/p)),    N0=O(N).

For the seven-condition sieve use odd primes 7<ell<=z0,
z0=floor(T^(1/256)). They are <alpha T/2 for large T.
The explicit Selberg diagonalization in the inherited sieve
has weights |lambda_d|<=d (g<=7/ell, ell>=11).
Summing the errors in its square costs at most

    O(p^(3/4) log^2 p (1+N/p) z0^8).

Relative to N this is
O(log^2 T*(T^(-7/32)+R^(-3/64))) for fixed C0,
using T^(7/4)/D<<R^(-1/16) and z0^8<=T^(1/32).
It is o(log^(-7) T), uniformly in the specified scales.
The truncated Euler-product argument gives
G(z0)>>log^7 T/S(D1),
S(D1)=prod_(ell>7)(1-1/ell)^(-nu_ell):
the local factors (1-g)^(-1) differ from
(1-1/ell)^(-(7-nu_ell)) by a uniformly bounded convergent
product, since the correction is O(1/ell^2).
The truncated product is converted to d<=z0 using the
same weighted log-d Markov bound, g<=7/ell. Thus

    # {(r,s) surviving} <<_(alpha,C0) D S(D1)/(T log^7 T). (2)

This bound is valid without any clock-phase or seed-density
assumption. It counts possible distinct source offsets for
fixed p,e,f,E,F, since (r,s) fixes y and x. A single path
has at most one triple at each source. In the whole slab
one may take D=R with the same argument. The exact clock
constraint of section 1 is additional; (2) does not multiply
an assumed independent clock probability into the sieve.

## 4. Three-event support/relay estimate for actual waits

Let S be the number of distinct marked labels in an actual
consecutive path segment in a block of width <=D. Let G be
the sum of relay physical gains between consecutive marked
events there (disjoint relay interiors). Count the waits
of marked events; omit the last two, costing O(T).
For short triples with E,F<=B, apply (2), weight <=4T,
and sum over p in the support, four e,f orientations,
and all E,F. The averaged singular-factor bound (1) of
the inherited ordered-descent-pair sieve applies to
D1=p-1+E and gives sum_E S(D1)<<B+1+(log log T)^4.
Summing over F contributes B+1. Each long relay E>B or
F>B appears in at most two consecutive triples; the number
of affected source events is <=2G/(B+1). Hence

    W_marked(I) << T
      + D S (B+1)(B+1+(log log T)^4)/log^7 T
      + T G/(B+1).                                       (3)

Constants depend only on alpha,C0. This extends the
five-condition pair bound to the triple-rich, short-relay
case, without a bound on the carrier's mass.
For any fixed epsilon>0 with R^epsilon<=T<=C0 sqrt R,
choose B=floor(log T). If S<=log^4 T and
G<= (D/T) sqrt(log T), then

    W_marked(I) << D/sqrt(log T).

Indeed the first sieve term is O(D/log T), the relay term
O(D/sqrt(log T)), and the end cost negligible.
For a fixed dyadic scale T=T(R) in that range, the total
actual origin-weighted marked wait on heavy-chain block
pieces satisfying these two hypotheses is O(R^2/sqrt(log R)):
apply the bound to each piece, each origin visits at most
ceil(R/D)+1+log_2 M pieces as in the preceding note.
No assertion that ALL pieces satisfy the hypotheses or
that this particular bound can be summed unchanged over
O(log R) dyadic scales. Under finite twins the residual
macroscopic wait can include dense support, long relays,
small labels, and mixed-scale transitions. Neither (1) nor
(3) controls all such remaining traffic.

## 5. Executed independent finite audit

Source research/min_simple_triple_clock_audit.py at
a3403be3a5f919cd819fbb57469808652d87ccca, Git blob
6dc0a036f2f09b9e4a2fded49f02142306932f4a; exact remote
readback matches executed local source (git hash-object).
Python stdlib + inherited min_simple_crossing_audit.py. Run:

    python research/min_simple_triple_clock_audit.py 1000 10000 100000 1000000

Brute enumeration of 540 local densities for ell=11,13,17,19,23,
six p values, E=0,2,6, F=0,2,8, both f orientations verifies
the exact formula of section 3, including coincident product
residues. Per-origin modular-clock replay, caching exact states;
checks product relations, exact CRT clock residues, relay wait
bound, seven local exclusions, return prime differences,
and exclusion of immediate alternating four-event returns
where tested. Uses diagnostic relay cutoff min(8,(T-4)//4)
for dyadic T>=8; theorem cutoff additionally min((T-4)//4,
max(1,floor(log(T)^1/4))). A long-wait triple diagnostic
requires each of three waits >=T/2. Counts overlap by shared
paths and sliding triples; wait sums can double count events.

    R        M      non-twin events  total wait   short triples  return triples
    1000     84              530          2966            0             0
    10000    834           11192        105828            9             1
    100000   8334         165348       2595177          318           183
    1000000  83334       2564511      66822800         6236          2798

At R=1000000: 294268 cached states including twin terminals;
1606 long-wait triple visits (123 distinct offset/label/relay
tuples), 282 distinct recorded clock controls, 188 distinct
return tuples. 2794 return visits have positive relay gain.
Diagnostic return wait upper sum 105899, versus total wait
66822800. The smaller theorem cutoff includes just 4 return
visits (wait upper sum 96), all in T=8; no asymptotic trend
inferred from that tiny sample. No returns at bands T>=64
in these finite diagnostics. Long-wait triples do occur at
T=512 (59 visits). All checks passed; numerical audits
do not verify the asymptotic sieve or resolve the remaining
stable transport. The necessary prime-pair sieve and
seven-condition estimates are paper arguments, not Lean
formalized. No proof of W=o(R^2) or twin infinitude.

Next: exploit clock congruences to control arbitrary long
mixed-scale relay histories or establish a bound on the
dense-support/high-relay part of stable transport; the
short-return estimate does not exclude high-diversity paths.
