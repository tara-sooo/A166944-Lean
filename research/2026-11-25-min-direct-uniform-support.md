# Uniform finite-support termination for relaxed MIN horizon paths

Continuation of [d7813ad](https://github.com/tara-sooo/A166944-Lean/commit/d7813ad8aaa338027722612ef69030d0f364a8ea) on the independent direct-arithmetic branch. The earlier square-entry geometry is not assumed. The central result is a paper theorem on an even weaker model than actual MIN; finite diagnostics are separate. No ensemble, return-cost or energy decomposition, clock-frequency assumption, prime distribution assumption, or external novelty claim. No Lean kernel verification. Twin infinitude and the A166944 conjecture remain OPEN.

## 1. New target: a uniform bound in the NUMBER of labels, not their magnitudes

Define a relaxed horizon path by even integer H>=4, an odd integer label a>=3 (in particular an odd prime is permitted), a sign e in {-1,+1}, and an edge

    H = e mod a,       H' = H+a-1.                         (1)

The actual adaptive and fixed-pool MIN event sequences are relaxed paths. Forget all time, first-hit competition, tie-breaking and square-root eligibility. In this note a block of events is consecutive, with quiet ticks omitted. A finite-support path uses at most k distinct labels across its entire block.

**Uniform support theorem.** For every positive integer k there is a finite integer L(k) such that EVERY relaxed horizon path using at most k distinct odd integer labels >=3 has at most L(k) edges. In particular, the bound is independent of the sizes of the labels, their product, the initial horizon, and the starting time. Primality is not needed.

This is stronger than the elementary fact that no infinite ray exists for a SPECIFIED finite set of labels. That fact gives a size-dependent product bound; the theorem gives a size-independent bound even when the labels can vary with the length of the proposed path. This note does not determine a numerical L(k) for general k.

## 2. Proof by finite branching and affine recurrence compression

First recall the fixed-set barrier. For a fixed finite set S of odd integers >=3, choose an even multiple J of their product at or above the initial horizon. If H=J there is no permitted label. If H<J and a divides H-e, the positive even distance J-H is congruent to +1 or -1 modulo a. Its least possible value is at least a-1. Therefore H+a-1<=J: no edge strictly crosses J. Each edge increases H by at least 2, so an infinite path on S is impossible.

Now suppose the uniform theorem is false for some k. There are arbitrarily long relaxed paths on at most k labels. In each path sort its distinct labels and name them a_1<...<a_k; if fewer than k are used, fill the unused slots by larger distinct odd integers. Record at each edge the index i of its label and the sign e=H mod a_i, where e is represented by +1 or -1. For every ordered pair j>i introduce a residue variable

    r_ji = a_j mod a_i,  0<=r_ji<a_i.

Use the reduced residue rho_ji=a_j if j<i, rho_ii=0, and rho_ji=r_ji if j>i.

Let positions u<v be consecutive occurrences of index i in the recorded word. Subtract their pre-horizons. Writing i_h for the label index at position h gives

    sum_{h=u}^{v-1}(a_(i_h)-1) = e_v-e_u mod a_i.

Consequently there is an integer z such that the exact AFFINE equation holds:

    sum_{h=u}^{v-1}(rho_(i_h),i-1) - (e_v-e_u) = z*a_i.    (2)

The quotient z has absolute value <=v-u+1: each summand is between -1 and a_i-2, and the sign difference has absolute value <=2. Crucially this bound is independent of the label values. Decorate each occurrence other than the first of its index by this integer z. At every finite word length there are only finitely many choices of index, sign and z for the next position.

Consider the prefix-closed tree of all such decorated finite words realized by some relaxed path with k slots. It has arbitrarily large depth by hypothesis and is finitely branching. By the elementary infinite-branch lemma (König's lemma; equivalently select a child with arbitrarily deep extensions at each step), there is an infinite decorated word every finite prefix of which is realizable.

Its equations (2) are linear homogeneous row constraints on the augmented vector

    V = (a_1,...,a_k, (r_ji)_(j>i), 1),

of dimension d=k(k+1)/2+1 over Q. All equation rows lie in Q^d. Hence their span has a finite basis drawn from the actual rows. Choose a finite prefix that contains the basis rows and the first occurrence of every index ever used in the infinite word (at most k first occurrences). This prefix has an actual finite witness: concrete odd integer labels, their true remainders, and an initial even integer horizon H0. The concrete augmented vector V satisfies the basis, and therefore EVERY equation of the infinite word.

Keep these SAME labels and SAME initial H0, and follow the infinite label-index word, updating the horizon by a_i-1. Every first occurrence satisfies its designated sign congruence because it lies in the chosen realized prefix. At each subsequent occurrence, equation (2) implies the sign congruence from the preceding occurrence of that index: the rho values are the actual fixed residues of the concrete labels. Induction over positions therefore gives an infinite relaxed path on one FIXED finite set of odd integer labels. This contradicts the fixed-set barrier.

Thus a uniform L(k) exists for each k. The proof uses only evenness, integral update a-1, finite branching, finite-dimensional linear algebra and the elementary barrier. It does NOT rely on a prime-tuple theorem or assume that a compatible infinite sequence of modular conditions necessarily has an integer realization; the actual finite witness for the spanning rows supplies that realization here. In particular, the earlier CRT-lift obstruction for unbounded alphabets does not invalidate this finite-alphabet argument.

For distinct prime labels, there is also an exact finite-word compression: given the decorated word and candidate ordered prime vector, it suffices to verify a basis of the affine equations (2), together with the genuine residues. First occurrences prescribe one residue class of H0 modulo each used prime, and parity H0=0 mod2. CRT gives arbitrarily large even H0 satisfying them. All remaining occurrences follow from (2). Choosing H0 sufficiently large also makes all the selected labels square-root eligible, although it does NOT ensure clock order or MIN competition. Since the augmented vector has nonzero last coordinate, a realizable system has rank at most k(k+1)/2. This many independent equalities can therefore represent the repeated-label restrictions even in a much longer word. No bound on the smallest actual prime vector is supplied.

## 3. Explicit optimal bounds for one and two prime labels

For one label p>=5: after an event its horizon residue is 0 or -2 modulo p, neither +1 nor -1, so no second same-label event. For p=3, a plus-side event can be followed by a minus-side event, after which the horizon is 0 mod3. Thus L_prime(1)=2.

For any prime q>=5, between consecutive occurrences of q let G be the intervening gain (NOT including the first q event). If the first q event ends at residue 0, the next pre-residue is +/-1, so the positive even G must be >=q-1. If it ends at residue -2, G is congruent to 1 or 3 mod q and is >=q+1. This simple repeat rule is useful independently of the uniform theorem.

Take two distinct primes p<q.
- If p>=5, consecutive repeats of either are impossible. A second q would have exactly one p between, with gain p-1<q-1, impossible. Hence at most the pattern p,q,p, of length 3.
- If p=3, every consecutive run of 3 has length at most 2. For q>=7 this gives intervening gain <=4<q-1, so q occurs at most once. If the initial run has two 3s, it ends at 0 mod3; after q the residue is q-1 mod3, either 0 or 1, allowing at most one more 3. Otherwise at most one initial 3 and two final 3s are possible. Thus length <=4.
- For {3,5}, a second 5 is possible only after the first 5 ended at 0 mod5 and exactly two 3s intervened (gain 4); the second 5 is then a plus-side event ending at -2 mod5. A third 5 is impossible. The middle two 3s start at 2 mod3 and end at 0; because a 5 adds 4=1 mod3, the first 5 was preceded by residue 1 mod3 (at most one immediately preceding 3), and the second ends at residue 1 mod3 (at most one subsequent 3). Total <=6. If there is only one 5 the preceding argument already bounds the length by 4.

The relaxed word 3,5,3,3,5,3 from H=44 gives horizons

    44 -> 46 -> 50 -> 52 -> 54 -> 58 -> 60.

Each selected label divides a neighbor and is square-root eligible. It attains length 6, so L_prime(2)=6 exactly. This is an extremizer in the relaxed model, not a claim that the actual first-hit MIN realizes that entire word from a canonical root.

An additional separation rule: for an ordered support p_1<...<p_k with p_k>=5, if p_k-1>L_prime(k-1)(p_(k-1)-1), p_k cannot recur inside the block, since all events between two occurrences would be supported on the smaller labels and contribute less than p_k-1. Thus the entire block has <=2L_prime(k-1)+1 events. More explicitly, let B_1=2 and B_i=2B_(i-1)+1=3*2^(i-1)-1. If a prime set obeys p_i-1>B_(i-1)(p_(i-1)-1) for all i>=2, every relaxed path on that set has <=B_k edges by induction. If p_1>=5 the analogous B_1=1 gives 2^k-1. Long paths cannot be produced merely by allowing a few increasingly separated enormous labels.

## 4. Consequence for infinite adaptive MIN under finite twins

Recall from [425a4b9](https://github.com/tara-sooo/A166944-Lean/commit/425a4b9a32e8a4a808582eb75d06cfecb7c56f0a) that if twin primes are finite, EVERY adaptive MIN trajectory starting above the last twin center is infinite. The new theorem gives the following necessary global property of every such trajectory:

For each fixed k, EVERY block of L_prime(k)+1 consecutive nonunit events contains at least k+1 distinct primes, wherever the block begins. In particular this is stronger than saying that the full infinite sequence has unbounded labels. The number of distinct labels in an arbitrary contiguous event window tends to infinity uniformly as its length tends to infinity. The same property holds for ANY infinite relaxed prime-label path, independent of finite twins.

There is a spatial form specific to adaptive square-root eligibility. For one event H' = H+p-1 with p<=sqrt(H+1),

    sqrt(H'+1) <= sqrt(H+1)+1/2.

Given an infinite adaptive path and any even X at or above its initial horizon, let H0 be the first event horizon >=X (or the initial horizon if equal). Overshoot gives sqrt(H0+1)<=sqrt(X+1)+1/2. Let m=L_prime(k)+1. After the next m events the horizon is bounded by

    X + (m+1)*sqrt(X+1) + (m+1)^2/4.

Therefore at least k+1 distinct primes are selected inside that horizon interval for EVERY such X. For each fixed k the required width is O_k(sqrt(X)); the constant is independent of X and of the source. This is a necessary consequence of the infinite-ray hypothesis that does not use accumulated return costs or any source ensemble. It is not a lower bound on the density of primes in ordinary short intervals, nor does it say the selected primes themselves lie near sqrt(X).

A new sufficient proof target is to show that for some fixed k, arbitrarily large canonical roots cannot support the required L_prime(k)+1 events without remaining within an alphabet of at most k primes (or stopping earlier). This would force stopping for those roots and hence twin infinitude. Equivalently one could construct infinitely many roots with an a priori bounded support for their entire adaptive trajectory. Neither has been shown. The actual support can grow with horizon, and finite-twins alone does not bound it. Mere existence of the universal L(k) is not a contradiction.

One useful obstruction to proving the target using only finite CRT constraints: arbitrary finite words can be lifted to huge roots as shown earlier, enlarging the time until absence of clocks certifies primality. The present proof succeeds in fixing a single integer witness precisely because the alphabet is bounded; it does not extend automatically when the number of variables grows. The next challenge is to derive a bounded-support segment of the requisite length from absolute-scale arithmetic or another constraint, rather than trying to apply compactness across an unbounded alphabet.

## 5. Finite diagnostics and reproducibility

[Audit at b088a02](https://github.com/tara-sooo/A166944-Lean/blob/b088a0273bd3627f57ee61a4b2e6f24181d2891d/research/min_direct_uniform_support_audit.mjs), blob 0dd89c81210e03c2c84895643acb374309e584e9, exact remote readback. Run from repository root:

    node research/min_direct_uniform_support_audit.mjs 59

For each prime support S with product Q, horizon H=2j has period Q in j. No edge crosses j=Q; each permitted edge increases j by (p-1)/2. Dynamic programming backward through j=Q-1,...,0 computes the EXACT maximum relaxed length over all start residues for this fixed S. Translating by 2Q places any representative above H>=4; no cutoff/clock condition is imposed except the explicit two-label eligibility check. For each maximizing word, the audit forms the reduced affine equations, checks the quotient bounds and exact integer satisfaction, performs exact BigInt row elimination, confirms that every row reduces to zero against the final basis, and reconstructs a word by first-occurrence CRT. The initial elimination implementation was revised to sort the pivots before the final run; the final maximum path lengths are unchanged.

Executed the actual ECMAScript function in the tool runtime, not a separate Node process. All prime sets of sizes 1,2,3 drawn from 3..59 (16,120,560 sets respectively) checked, 2,464,460 permitted edges in the periodic DAGs and 914 affine rows in their maximizing words. Maximum observed lengths 2,6,18, respectively. The 18-edge example uses {3,5,17}; the maximum among sampled three-label supports excluding 3 is 9 for {7,11,23}. Seven selected four-label sets were also tested:

| support | exact fixed-support maximum |
|---|---:|
|3,5,7,11|36|
|3,5,7,17|54|
|3,5,17,19|26|
|3,11,13,17|20|
|5,7,11,13|10|
|7,11,23,47|10|
|11,13,17,19|7|

The values 18 and 54 are lower bounds for the universal optimal L_prime(3), L_prime(4), NOT universal upper bounds or evidence that a proposed formula has been proved. General uniformity is proved above independently of these finite computations. No external literature novelty assessment was performed. No Lean executable available, no Lean changes. Main and siblings unchanged.

## 6. Research status / next independent direction

The theorem is a global statement valid even without the actual clock rule and arbitrary label magnitudes. The finite-dimensional proof opens an alternative to path cost/merge accounting: study support growth and affine recurrence constraints, and try to turn the necessary uniform diversity of every infinite adaptive ray into a contradiction using actual first-hit arithmetic. Immediate concrete next work: seek explicit bounds on L_prime(k) beyond k=2 (or stronger ones for actual clocks), analyze what constraints can force a small support in a sufficiently long event window at controlled absolute scale, and investigate whether the clock conditions admit a finite-dimensional compression for growing support. No unbounded family of stopping roots, finite-twins contradiction or original record conjecture proved.
