# Negative MIN: compressed multi-idle sieve and mod-30 gain potential

2026-11-26 JST. Continuation of 74a679672fe14567354fb95c8a5a5b9827744de3.
Retain only positive selected-prime congruences in the modulus,
treat all negative priority constraints as a single sieve across
the stationary states, and construct actual canonical roots with
a fixed number of polynomial-length successive idle segments.
Independently improve the full-prefix gain criterion via a finite
priority potential modulo 30. Paper-level arguments and finite
computational certificates, not Lean-verified theorems.

## 1. Compress a complete signed word to a single sieve

Use A=6j, v0=3-3j. Fix parity of j and a word of m
selected labels and signs (p_i,e_i), with e=-1 for the
minus/even clock and e=+1 for the plus/odd clock.
At source i, cumulative gain G_i is fixed by the
earlier labels. Eligibility for p_i>=5 fixes

    j = (G_i+e_i)/6 mod p_i.

For p_i=3, test -G_i=e_i mod3 instead. The parity
and positive residue determine the wait w_i uniquely
from the preceding elapsed time t_i, using the
candidate-clock formula of d577559. Hence the times
and waits of the prescribed signed word are uniquely
determined, even before imposing the priority tests.
No separate enumeration of possible waits is needed.
A repeated positive label must require the same
residue every time, or the word is impossible.

Pin these positive congruences and the parity to
one class j=b mod M, where

    M=2 prod_(distinct selected p>=5) p.

Additional fixed congruences may be imposed if desired.
Prime 3 is always a deterministic eligibility/clock
test, not a variable residue. For every other prime q
and every source i, prohibit the root residue
(G_i+e)/6 mod q whenever its candidate (wait,q)
would lexicographically precede (w_i,p_i).
On the terminal stationary state, also prohibit all
candidate sides that would fire within a specified
additional idle window of K ticks. The number of
stationary states is at most m+1. Thus the union B_q
of forbidden residues for prime q satisfies

    nu_q=|B_q|<=min(q,2(m+1)).                    (1)

Pinned primes are tested exactly; if any prohibited
residue is pinned, reject the entire class. The same
holds for the deterministic prime 3 gate. For free
q>=5, a full set of forbidden residues makes the
word impossible. If it is not full, pass its
forbidden set to the single simultaneous sieve.

Let t_end be the predetermined elapsed time of
the last selected event. By the exact height-local
scan (0116e3e), only q<=z=2(t_end+K)+7 need be
checked. More precisely, if an untested competitor
preempted the prescribed word, at the first divergence
its actual height would be <=3+t_end+K, and its label
would divide one of the two height expressions, hence
be <=z. A pinned selected clock itself is eligible
at the predetermined time. Induction gives the
converse: a surviving root has precisely the
prescribed word through that time and the K-tick
idle extension. If a formal prescribed word would
have an inadmissible height, a root satisfying all
these conditions cannot realize it. Physical stopping
must be excluded separately; for t_end+K=o(A), the
height bound G_t<=2t+6 and initial clock ensure this.

Thus an arbitrary *fixed-length* word, including its
idle tail, has an exact positive-congruence and
negative-sieve representation on actual finite
root intervals. It is unnecessary to pin all
primes ever queried negatively. This extends the
one-state stationary sieve of 74a6796 to the
complete prescribed history.

## 2. Uniform sieve for bounded-length words

Set d0=2(m+1). In an interval of N consecutive j
values, the progression j=b mod M has N_b=N/M+O(1)
members. For squarefree d supported on free primes,
CRT gives remainder

    |r_d|<=prod_(q|d)nu_q<=d0^omega(d).

For a compatible word all local factors are positive.
For q>2d0, nu_q<=d0, so the sieve product condition
of dimension d0 holds, uniformly for fixed m; the
finitely many q<=2d0 have factors at least 1/q
when compatible. In particular

    V=prod_(q<=z, q free)(1-nu_q/q)
        >>_m (log(2z))^(-d0).

Apply the fundamental lemma used in 74a6796
(Terence Tao, 254A Notes 4, Lemma 17 and Corollary
19, source recorded there), at level D=floor(sqrt N_b),
s=log D/log z. The elementary bound
sum_(d<=D) d0^omega(d)<=sum_(d<=D) tau_d0(d)
<<_m D(log(2D))^(d0-1) follows by counting products
of d0 positive integers. We obtain

    count = N_b V (1+O_m(exp(-s)))
                 + O_m(sqrt(N_b)(log(2N_b))^(d0-1)).    (2)

This is a relative asymptotic if m is fixed,
M<=R^delta, delta<1 fixed, N comparable to R and
z=R^o(1). For z<=C_m R^eta it is a two-sided
constant-factor estimate when eta>0 is sufficiently
small depending on m and delta. The constants are
not uniform in growing m. The prior full exposed
modulus can be enormous without harming (2);
only the positive modulus matters. If several
different words specify the initial events up to
the same word length, their realizing roots are
disjoint. Therefore uniform lower bounds for
individual compatible words can be summed.
No assertion of lower bounds for all candidate
words, or arbitrary repeated prefixes, is made.

## 3. A concrete family with many separated polynomial idle segments

Fix any integer r>=1. We construct r additional
large minus events after the explicit p=7 plus
event at elapsed time 3 in j=55 mod154 from 74a6796.
Let Y=R^alpha and K=floor(R^eta) with
0<alpha<eta small fixed (depending on r), r alpha<1/4.
Use the following positive constraints.

Let d*=2(r+1), counting the stationary states
AFTER the initial 7 event, up to the final state.
Fix all odd primes q<=d*, except 3,7,11,
by j=1 mod q; retain j=55 mod154.
Let L be the fixed product of 2,3,7,11 and these
additional primes. Choose r primes p_i in the
bands

    [32^(i-1)Y, 2*32^(i-1)Y],    p_i=1 mod L.

For large R these primes exceed every fixed prime.
Write G_1=6 and G_(i+1)=G_i+p_i-1.
Pin j=(G_i-1)/6 mod p_i, so at state G_i the
chosen p_i is minus eligible. All G_i are 0 mod6;
the 3 clock is never eligible in these states.
The fixed primes 7 and 11 remain ineligible as
after the first jump, since all later p_i-1 are
multiples of them. Additional pinned q have a=0
mod q at every such state.

Require that p_i be ineligible at every other
state G_h (h in 1..r+1). At earlier states h<i
the residue is -1+(G_i-G_h), with
2<G_i-G_h<p_i by the geometric separation;
hence it cannot be +/-1. Immediately after
its own minus jump p_i the new residue is 0.
When choosing a later p_i, forbid the at most
two residue classes modulo each earlier p_k
that would make that old p_k eligible at the
new state G_(i+1). Explicitly prohibit
G_i+p_i-1-G_k = 0 or -2 mod p_k.
Each such residue rules out only O_r(1) integers
in the i-th band because p_k>=Y and the band
length is O_r(Y). Thus at every step the total
number of excluded candidate integers is O_r(1).
By the standard prime number theorem for a fixed
arithmetic progression, each band contains
>>_r Y/log Y primes in the residue 1 mod L.
It follows that there are >>_r (Y/log Y)^r
admissible ordered prime selections.

Fix such a selection. The positive modulus is
M0 prod_i p_i, where M0 is the constant fixed
root modulus for the 7 prefix and small primes.
At each of the r+1 states G_i prohibit BOTH
spatial eligibility residues for every free prime
q<=z, where z=2(t_end+K)+7. This is stronger
than the exact priority sieve, hence sufficient.
The free primes exceed d*; thus the at most d*
forbidden residues cannot exhaust any free prime.
All pinned primes are neutral except the chosen
label at its own source. The initial p=7 prefix
is already forced by the original j congruence.

The selected clock waits w_i are fixed by the
positive congruences and parity. They satisfy
w_i<=2p_i. Let h denote the height just before
starting the waiting interval. It is nonnegative
and <=6+2 sum_(k<i)p_k <=6+4p_i/31.
At minus firing the pre-firing height b=h+w_i
satisfies p_i|2b+1; since b>=1, this requires
b>=(p_i-1)/2. Hence for all sufficiently large Y,

    w_i>=p_i/5.

Thus each intermediate waiting interval is
polynomially long, of length at least Y/5.
The final idle extension is K, with no further
gain. The total gain through the final horizon is

    G_end=6+sum_i(p_i-1)=O_r(Y),

and t_end=O_r(Y). Since alpha<eta, z=O_r(R^eta).
All physical roots in [R,2R] are still far from
the half-distance and time boundaries on this
horizon. Apply (2), now with dimension d* after
the fixed initial event. M=O_r(Y^r)<=R^delta
for some fixed delta<1, and choose eta small
enough for the fundamental lemma. Each word
is realized by

    >>_r R/(Y^r (log R)^(2(r+1)))

actual canonical roots. The words have the
same number of selected events and are disjoint
by deterministic MIN. Summing over the selected
prime sequences gives

    # roots in [R,2R] with this pattern
          >>_r,alpha,eta R/(log R)^(3r+2).         (3)

On each such root, the first event is 7 at
elapsed 3, then exactly r further events with
polynomial waiting times, then no event for K
ticks, and G_{t_end+K}=O_r(R^alpha)=o(K).
All exponents are fixed small constants for
fixed r; no bound uniform in r or prescribed
large eta is claimed. The prime number theorem
in fixed progressions and the fundamental lemma
are standard literature inputs; (3) is a
deduction for this specific MIN family, not
a claim of literature novelty.

This is a real finite-slab multi-segment
existence result with variable growing
selected primes. It does NOT establish a
linear-scale gain upper bound: the available
time horizon is still o(R), and later events
may consume a macroscopic gain. Increasing r
with R would require uniform sieve control
and bounds for the positive modulus as well
as the prime band construction.

## 4. Independent finite-state improvement of W/G

Use state (a mod30, v mod30) with a even. There
are 15*30=450 states. Let (p0,w0) denote the
restricted winner among 3 and 5 at this state,
or w0=infinity if neither eligible. Their
eligibility and clock waits are exactly known
from the residues (periods 6 and 10).
Every actual event of label 3 or 5 must equal
this restricted winner. Every actual event of
label p>=7 has

    1<=w<=2p,  w<w0.

The strict inequality follows from least-prime
tie priority. Relax the other eligibility and
clock constraints on p>=7; this only enlarges
the set of transitions. A transition is

    (a,v) -> (a-p+1, v+w) mod30.

For each state and each prime p<=151, enumerate
the possible transitions as follows. For
3,5 use only the restricted winner. For p>=7
take all integer waits through min(2p,w0-1).
The compressed version retains only the
largest wait for each class mod30, since
the target state is the same and that wait
has largest weight. Assign integral weight

    c=4w-9(p-1).

Starting at F=0 on all 450 states, repeatedly
replace F(target) by max(F(target),F(source)+c)
over the compressed edges, until no change.
The audit supplies a finite certificate:
after 16 passes including the final unchanged
pass, the resulting integer table has min 0,
max 32, and every finite edge satisfies

    4w-9(p-1)<=F(target)-F(source).                (4)

An independent uncompressed edge scan verifies
the same table for every admissible wait,
not just the maxima. For every p>151, w<=2p
implies 4w-9(p-1)<=9-p<=-32, whereas
F(target)-F(source)>=-32. Hence (4) is
universal for all actual MIN events, with
no bound on a or v. This is a finite,
algorithmically reproducible potential
certificate; it is not a Lean certificate.

Sum (4) over a contiguous complete-event block:

    W <= (9/4)G + (F_end-F_start)/4
      <= (9/4)G+8.                               (5)

This improves W<=3G. The coefficient is not
claimed optimal; e.g. an exploratory relaxed
graph check with coefficient 20/9 fails.
That failure is for the relaxed graph only,
not a lower bound on the best actual MIN
coefficient.

## 5. Stronger gain criterion for twin infinitude

Use the original stopped prefix, INCLUDING
the half-crossing event if it occurs at
or before tick -1. Suppose no twin center
in (A/2,A]. In the half-crossing case
G(A)>=A/2 directly. In the time-stop case
the last unfinished source is in (A/2,A]
and its next wait is <=2sqrt(A+1), by
the non-twin least-factor bound. Thus

    W(A)>=A/2-4-2sqrt(A+1).

Together with (5),

    G(A)>=min(A/2,(4/9)(A/2-4-2sqrt(A+1)-8))
         = (2/9)A-O(sqrt A).                     (6)

A strict violation of the finite bound
certifies a twin center in (A/2,A].
If twins are finite, (6) holds for all
large canonical roots. Conversely at
arbitrarily large twin centers A the
first firing is at zero and G(A)=0.
Consequently the following is equivalent
to twin infinitude:

    liminf_(6|A,A->infinity) G(A)/A < 2/9.         (7)

The earlier 1/12 criterion was only sufficient
and unnecessarily stringent: even W<=3G and
separating the two stops would give 1/6.
The new coefficient yields 2/9. No asymptotic
upper bound below this threshold is established.

One may also stop at elapsed T=floor(c A),
0<c<1/4 fixed. For large A, height ensures
G<=2T+6<A/2 and the time boundary is later.
In a locally twin-free interval, the last
completed-event time at T is at least
T-2sqrt(A+1). By (5),

    G_T >= (4/9)(T-2sqrt(A+1)-8).                 (8)

Thus an unbounded sequence with
G_T/A bounded strictly below 4c/9 suffices.
The converse at twin centers again gives
zero. This allows the remaining gain-saving
problem to be posed at a fixed linear horizon,
rather than a trajectory-dependent stop.
The construction of section 3 has not
reached that horizon.

## 6. Finite audits and persistence

Multi-idle certificate:
research/min_local_negative_multi_idle_sieve_audit.mjs
commit c51dc4412085b945d88dfebe6e7aa2137da60ed1,
blob 35587a8f64c50b30cf1acc1a431333fec047aecf.
Executed in ECMAScript research runtime,
fetched at exact commit and re-executed with
identical output. Reproduce with node.

    signed-word / idle-tail controls       1020
    actual root / word equivalence checks 204000
    rejected incompatible certificates      324
    compatible certificates                 696
    forbidden-set size checks             11805
    CRT remainder checks                    5900

Direct event rule on actual j=1200..1599
of the prescribed parity independently
compared with compressed certificate.
Words taken from actual prefixes of up
to 3 events, then append 0,7,25 idle
ticks. Negative outcomes include old
clock conflicts. All checks passed.

Constructed separated marks: five
formal CRT residue environments for
r=1,2, eight additional selected primes
total, 57 pinned eligibility checks,
164614 free-prime admissibility checks,
1034743 tick checks. The complete clock
sequences agree with the specified words
and terminal idleness. The environment
has genuine integer representatives by
CRT but their enormous integer values
are not materialized and are NOT
claimed to be roots in the polynomial
physical slab. The latter asymptotic
is derived via the sieve in section 3.
One proposed finite band (r=1,Y=900)
contained no prime in the chosen class
and was skipped, as allowed in finite
controls; the large-Y statement uses
PNT in the fixed progression. Example
r=2,Y=3000: p_1=4621, p_2=97021,
last elapsed firing 50820, total gain
101646, subsequent idle length 101657.
No growing-r test or empirical proof
of the lower sieve.

Mod-30 potential:
research/min_local_negative_mod30_gain_potential_audit.mjs
commit ed68a4dda7d45d3c8faf8a7127a4bf5b69e168d5,
blob aed949a04e4264476fda32203cd39682871227b4.
Executed in ECMAScript research runtime,
fetched at exact commit and re-executed
with identical output. Reproduce with node;
output includes the complete 450-entry
potential. No separate Node or Lean run.

    states                               450
    small restricted edges               360
    compressed larger edges           117930
    total compressed edges            118290
    independent uncompressed waits    466410
    potential range                       32
    relaxation passes                     16

All finite inequalities and the uniform
tail inequality passed. Actual canonical
A=12,18,...,300000: 49999 roots,
1040604 complete events and telescopes,
34685 labels exceeding the enumerated
cutoff 151; all per-event inequalities
passed. 3 half stops, 49996 time stops;
6 locally twin-free prefixes in this
sample, all satisfy (6). 49935 strict
gain witnesses all visited a twin source.
Fixed elapsed horizon floor(A/8):
49999 checks, 49378 strict gain witnesses
all visited a twin source by that horizon.
The maximum observed W/G for nonzero gain
was 2.5; this is compatible with the
additive constant 8 in (5).

## 7. Remaining target

The bounded-length multi-segment sieve
removes the negative-query modulus cost
for the entire fixed word, and gives
actual polynomial-horizon small-gain
families. The finite priority potential
relaxes the required linear-horizon
gain threshold from 1/12 to 2/9 for the
original stopped prefix, or to 4c/9
at fixed elapsed cA. Neither gives
a gain upper bound at linear horizon.
The central missing theorem is an
unbounded sequence satisfying (7) or
(8)'s strict violation; in particular
the sieve dimension and positive
modulus currently obstruct extending
section 3 to a linear horizon. No
twin-infinitude proof or Lean
verification; no canonical Lean targets
or sibling branches modified.
