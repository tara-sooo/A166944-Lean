# Negative MIN: fresh-prime word counting and the finite-interval entropy barrier

2026-11-26 JST. Continuation of afd3469f7f5b61d8c4bf0336cd5a4b1cd9382bc4.
Begin counting compatible canonical origins for ordered high words
rather than only computing a posteriori gain certificates. Derive
exact fresh-prime scalar increment laws, a coupled clock Laplace
bound, finite-interval CRT counts and a bounded-band word union
estimate. These count relaxed necessary conditions, not actual
MIN word probabilities. Paper deductions and finite audit;
no twin-infinitude proof or Lean verification.

## 1. Fresh-prime triangular CRT law

Use canonical distance A=6j, half-distance x=3j, v0=3-x.
Fix an ordered high word p_i>=5, signs e_i in {-1,+1},
and (for the clock version) fixed integer marked waits w_i.
No dependence of this prescribed word on j is allowed.
For the notation of afd3469 put

    H_i=sum_(h<=i)(p_h-1)/2, V_i=sum_(h<=i)w_h,
    alpha_i=x-H_(i-1)-e_i/2 mod p_i,
    beta_i=x-3-V_i+c(p_i,e_i) mod 2p_i.

Division by 2 in alpha_i is modular. The scalar monotone
greedy certificates S_i,U_i start at zero and round up
to the alpha_i,beta_i residues, respectively.
Let F be the set of distinct primes in the fixed word,
Q=prod_(p in F)p, and k=|F|. All are coprime to 6.

A fresh occurrence means the FIRST occurrence of p in
this word. At each such step let X_p=S_i-S_(i-1).
Take j uniform over a complete residue period modulo Q.
Before the fresh step the earlier S and H depend only
on previous prime residues. For p newly appearing,
x mod p is uniform independently of those residues.
Thus X_p is uniform on {0,...,p-1}, conditionally on
the entire previous residue data. In particular all
fresh X_p are mutually independent, even if the word
contains repeated labels between them.

More strongly the map from j mod Q to the ordered
fresh-increment vector (X_p) is bijective: given the
increments, reconstruct each x mod p from the previous
S, known H, sign, and X_p. Repeated steps between
introductions are deterministic from the recovered
residues. The recovered x residues uniquely determine
j mod Q by CRT. Both cardinalities are Q.

Since repeated steps are nonnegative, any realization
with total unmarked half-gain <=B must have

    sum_(p in F) X_p <= S_final <= B.

The generating polynomial for the number of fresh
vectors with sum b is exactly

    product_(p in F)(1+z+...+z^(p-1)).

Let N_F(B) denote its cumulative coefficient sum
through degree B for integer B>=0. This gives at
most N_F(B) admissible canonical root classes.
The number of root classes for the full scalar
certificate can be smaller because of repeated steps.
In particular

    N_F(B) <= min(Q, binom(B+k,k)),                (1)

by ignoring individual upper bounds (stars and bars).
The expected fresh half-gain over the period is
sum(p-1)/2 and the variance is sum(p^2-1)/12.
Neither is the expected actual gain of a MIN path.

For any lambda>0 a fixed word has the full-period
small-budget bound

    Pr(S_final<=B)
       <= exp(lambda B) prod_p f_p(lambda),

    f_p(lambda)=(1-exp(-lambda p))/
                         (p(1-exp(-lambda))).

For example, if all fresh p>=T and B<=delta k T,
choose lambda=1/(delta T) (with delta T>=1).
Then exp(lambda B)<=exp(k) and
f_p(lambda)<=2delta, using 1-exp(-y)>=y/2 for
0<=y<=1. This bounds the fraction by (2e delta)^k.
This is exponential suppression for a fixed prescribed
word at sufficiently small delta; it is not a bound
on the union of all actual words.

## 2. Clock correlation: not an independent second factor

Fix j parity and take j over that parity class modulo
2Q; equivalently j=2l+epsilon with l mod Q. All
previous S,U depend only on previous prime residues
and this parity. At a fresh step define Y_p=U_i-U_(i-1).
The residue relations give, conditionally on earlier
residues, a fixed eta in {0,1} and fixed delta mod p with

    Y_p=eta mod 2,
    Y_p-X_p=delta mod p,
    0<=Y_p<2p.

Thus Y_p runs exactly once over eta,eta+2,...,eta+2(p-1)
as X_p runs through 0,...,p-1. It is a permutation,
not an independent draw from the clock residue space.
The permutation and parity may depend on previous
residues and the fixed word. The spatial law from
section 1 is unchanged after conditioning on j parity.

For lambda,mu>=0, by the rearrangement inequality
on the two decreasing exponential lists,

    E[exp(-lambda X_p-mu Y_p) | past]
        <= exp(-mu eta) f_p(lambda+2mu)
        <= f_p(lambda+2mu).

Iterating conditional expectations yields the necessary
joint budget estimate for fixed word with fixed waits:

    Pr(S_final<=B, U_final<=C)
       <= exp(lambda B+mu C)
                         prod_p f_p(lambda+2mu).   (2)

The same inequality holds for the other parity and
hence the full root period. Repeated increments are
nonnegative and can only make the actual greedy
budgets larger. This does not assert independence of
Y_p from previous data, or of X_p and Y_p at a single
prime. In particular multiplying two independent
one-coordinate probabilities would be unjustified.
The joint bound (2) is a conservative rearrangement
bound, not necessarily optimal. It only applies
with waits fixed as part of the word; a union over
unknown marked waits would add further combinatorics.
No counting assertion about the four-variable coupled
cone itself is made; it dominates the scalar bounds.

## 3. Short intervals and partial-prime certificates

Let j run over ANY interval of N consecutive integers.
A residue modulo Q occurs at most ceil(N/Q) times.
Hence for the fixed spatial word,

    # compatible roots <= ceil(N/Q) N_F(B)
        <= (N/Q+1) binom(B+k,k).                   (3)

For a fixed parity use N consecutive values of l
instead; both formulas remain valid. In a root
interval without fixing parity the spatial law already
has period Q. For the joint clock law one may apply
the same count separately to the two parities using
the actual count of good joint residues or its (2)
upper bound. This retains the boundary correction:
when Q is much larger than N, the +1 term cannot
be dropped.

There is an arbitrary-subset projection that need
not be an initial prefix of fresh labels. Choose
one marked index for each of d distinct primes
p in a subset F' of F, in chronological order.
Any realization with cumulative unmarked half-gain
<=B supplies nondecreasing actual s_i between 0
and B at these selected indices. The number of
possible such d-tuples is binom(B+d,d). Given that
tuple, the source congruences fix one residue of
j modulo Q'=prod_(p in F')p. This also holds for
the scalar-relaxation witnesses themselves.
Therefore

    # compatible roots <= ceil(N/Q') *
                          min(Q',binom(B+d,d)).     (4)

Choose any subset, including one with Q' comparable
to but not greater than N. No distribution assumption
about the omitted labels is needed. The price is
that the bound uses the entire budget B even for
the smaller subset. The word's known cumulative
high gains H_(i-1) remain in the congruences even
for omitted labels. Removing them would be wrong.
For B very large relative to selected primes (4)
can become trivial.

## 4. Union over distinct words in a fixed band

Consider the family of ALL signed words of k
pairwise distinct labels from a specified finite
prime band P contained in [T,2T), T>=5. There are
no other marked events between these k marks;
unmarked relays may be arbitrary. Fix the threshold
defining which labels are marked. We are counting
the relaxed possible first k marked labels, not
asserting that every candidate word can occur.
Clock waits need not be specified in this section.

Let H_P=sum_(p in P)1/p, Qmax=(2T)^k
(or the actual product of the k largest band primes).
Sum (3) over all ordered distinct label choices and
signs. The exact sum of 1/Q is 2^k k! times the kth
elementary symmetric polynomial of (1/p)_{p in P},
bounded by (2 H_P)^k. Consequently

    # roots admitting any such word with low
      half-gain <=B
      <= (N+Qmax) binom(B+k,k) (2 H_P)^k.           (5)

The minimum with N can always be taken. This is
a union bound; multiple candidate words at one
root need not be disjoint. It is uniform over
adaptive selection of an actual word in this
family because ALL candidate words have been
included. It does not include arbitrary repeat
patterns or labels outside P.

Using the standard Chebyshev upper bound for the
number of primes in [T,2T) gives H_P=O(1/log T).
If (2T)^k<=N, then (5) divided by N is bounded by

    2 [C (B+k)/(k log T)]^k

for an absolute C, from binom(B+k,k)<=
[e(B+k)/k]^k. In particular for fixed k>=1 and
B=o(log T) as T tends to infinity this fraction
is o(1) (with N at least (2T)^k). For growing k
and B<=delta k log T with a sufficiently small
absolute delta, the fraction is exponentially small
in k once log T is sufficiently large. This is a
rigorous obstruction to having many DISTINCT marked
labels in a narrow band with extremely small
total low gain. It is not an upper bound on W.

An extension allows a prescribed word length m>=k
with exactly k distinct labels in P. The number of
possible first-occurrence patterns is at most
binom(m-1,k-1); once the pattern and ordered new
labels are fixed there are at most k^(m-k) choices
at repeat positions, and at most 2^m signs.
Therefore the same proof gives an upper bound

    (N+Qmax) binom(B+k,k) *
      2^m binom(m-1,k-1) k^(m-k) H_P^k.            (6)

This is useful only if the repeat-pattern entropy
is controlled. It deliberately overcounts words
whose repeated labels have not yet been introduced.

## 5. Why this has not closed the stopped-prefix problem

The current goal is liminf W(A)/A<1/4 on unbounded
canonical A, using cc62807. Fixed-word CRT laws do
not directly imply such a sequence. In actual MIN
the next selected label depends on the same initial
residues used in the fresh-prime distribution; one
cannot apply the fixed-word law after conditioning
on that selected word. The honest union (5)-(6)
accounts for this on bounded word families, but
it demonstrates two limitations of this counting
approach:

* At T comparable to sqrt A and a root interval
  N comparable to A, a product of even three such
  fresh primes is already much larger than N.
  A full-period exponential probability is then
  not a short-interval probability. The arbitrary
  subset certificate (4) avoids this error at
  the cost of retaining only very few constraints.
* Even with a period that fits, the word-union
  bound restricts small low budgets on the scale
  k log T, whereas the macroscopic gain budget
  on a long prefix can be on the scale k T or
  larger. Prohibiting small-relay fresh words alone
  does not prohibit long prefixes with larger
  relay gain. The upper bound also does not rule
  out paths with many small events and few marks.

Thus the next genuine requirement is a bound on
the number/entropy of actually eligible ordered
words, or a different short-interval counting
mechanism exploiting least-clock priority and
the coupled time/gain invariant. Merely improving
the fixed-word Laplace transform or taking more
fresh primes in an enormous CRT period does not
provide the needed existence theorem.

## 6. Executed audit

Source research/min_local_negative_fresh_word_count_audit.mjs,
commit e8e328ddf73323c95cba6e709afd8b4d7b5bdf61,
blob de3fe02c3a1d8fe09a9fbb0feb8852180fd2e7da.
Executed in ECMAScript research runtime; fetched
at exact commit and re-executed with identical output.
Reproduce:
node research/min_local_negative_fresh_word_count_audit.mjs
No separate Node or Lean invocation.

48 fixed-word/sign/parity controls, including repeated
labels, 170100 complete-period root incidences and
fresh-vector bijection checks; 674100 conditional
fresh increment and coupled clock residue checks each,
22260 conditional uniformity/clock-permutation cells.
All fresh-vector coefficient distributions matched
the exact convolution. 48 Laplace checks, 720
finite-interval bounds, 240 arbitrary-subset bounds
passed. The audit uses lambda=.13, mu=.07 for the
finite Laplace tests; the general proof above is
not a numerical estimate based on these parameters.

Explicit union enumeration for band P={11,13,17,19},
k=2,3, B=0,1,3,6, j interval of length 2500 starting
at 101. 960 signed word/control incidences, 2400000
root-word evaluations, 41161 compatible relaxed
root-word incidences summed over controls. All
exact per-word and union upper-bound checks passed.
For k=3,B=0, 147 distinct roots admit at least
one relaxed word; the word sum is 155, the direct
CRT bound 240, the simpler harmonic bound 1167.
For k=3,B=6, 1648 roots admit a relaxed word and
the bounds are already greater than the interval
length. These are relaxed spatial certificates,
not actual MIN word counts. The fixed-band union
formula (6) with repeats was not separately
enumerated, but follows by the combinatorial
overcount in section 4.

Independent actual-path controls: every canonical
A=12,18,...,120000, four thresholds T=11,23,53,101.
Stop before the half-crossing event or a firing
after -1; retain at most the first three marked
events. 79996 root/threshold controls,
927750 completed events, 114599 actual greedy
space/time lower-bound checks, all passed.
26474 controls reach three marks, of which 23902
have distinct labels. For the latter, count low
half-gain <=3 and average half-gain through
the third mark:

    T     distinct  low half-gain<=3   mean low half-gain
    11     10979       2097                 7.8241
    23      7347        192                29.9609
    53      3970         27                81.8456
    101     1606          8               180.2839

These are conditional finite samples, not restricted
to a fixed band [T,2T), and not tests of the asymptotic
word-union estimate for actual long non-twin paths.
The mean increase illustrates why a small-budget
hypothesis cannot be assumed from the scalar law.
No asymptotic conclusion follows from these data.

## 7. Status

Exact fixed-word fresh-prime CRT laws and finite-interval
union counts established at paper level, with executed
finite controls. The stopped-prefix existence theorem,
a sufficiently strong adaptive-word count and the
required linear wait saving remain open. No twin-infinitude
proof or Lean verification; no canonical Lean target
or sibling branch changed.
