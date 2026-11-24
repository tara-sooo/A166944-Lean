# Cube-free complete prime words and signed-square restrictions

2026-11-24 JST. Companion to research/2026-11-24-min-lag-cycle-obstructions.md on the same branch. New unconditional paper theorem; not Lean-checked. The twin-prime conjecture and full-horizon correlation estimate remain open.

## 1. Cube-free theorem for arbitrary complete MIN words

Consider any finite consecutive event sequence, starting at even C, with odd prime labels p, eligibility p|(C+sigma), sigma in {-1,+1}, and update C<-C+p-1. This includes all canonical MIN trajectories, but does not require the MIN clock rule or an upper bound on primes. The side sigma is unique since p is odd. The earlier even-multiple barrier applies: for a finite set S of odd primes and D=2 product_(p in S) p, consecutive events drawn from S cannot advance past the least multiple of D at or above the initial even horizon C; total gain is strictly less than D.

**Theorem:** No nonempty finite word w of prime labels occurs as the contiguous block www. Let w have length k, gain G=sum_(i=1)^k(p_i-1)>0 and distinct-prime set S. At each corresponding position of the three copies the pre-horizons are C_i, C_i+G, C_i+2G. Eligibility gives
    p_i | G+sigma_2-sigma_1,
    p_i | G+sigma_3-sigma_2.
The two differences are in {-2,0,2}, which are pairwise incongruent modulo EVERY odd prime (including 3). They must be equal. Three signs in {-1,+1} with equal successive differences are constant, so p_i|G. G is even, hence D|G. The barrier for the first copy gives 0<G<D, contradiction.

This strengthens the restricted repeated large-prime word observation in section 3(b) of the preceding lag-cycle note: the conclusion for an exact triple repetition holds without a bound on block length, without a bound on lag, and with arbitrary small primes included. It is a theorem about the FULL contiguous label word; a filtered or sampled subsequence can have cubes because deleted events change the gain.

## 2. Squares and sign changes

For a block ww with G>0, each p in S satisfies p | G+sigma_2-sigma_1. If every position has the same side in both copies, D|G and the same barrier gives a contradiction. Thus a repeated word has at least one side change. More precisely the difference sigma_2-sigma_1 is determined uniquely by -G mod p; for any prime whose difference is nonzero, every occurrence of that prime must start on the SAME side in copy 1 and change to the opposite side in copy 2. If both sides already occur for p in copy 1 then p|G and no side change for p is possible.

For G>2, split S into the three disjoint classes S_- ,S_0,S_+ according to p dividing G-2,G,G+2. These are disjoint for odd primes, and their products divide (G-2)/2, G/2, (G+2)/2, respectively. Consequently
    product_(p in S) p <= (G-2)G(G+2)/8.
For G=2 the only possible w is the singleton 3; it can repeat with a side change, but not three times. In the canonical full window G<=5X, B^2 asymptotic to 7X. With Q=ceil(B/log^(1/3)B), for sufficiently large X, Q^7 exceeds (5X+2)^3/8. Hence every contiguous square ww contains at most SIX distinct labels >=Q in its word w, regardless of length or the number of small labels.

## 3. Application to repeated lag words

At each common-label asynchronous step with positive output lag h, the selected prime p satisfies 2p|h. If all labels in the interval are >=Q and 0<h<2Q^2, at most one eligible large prime divides h/2, so the output lag uniquely identifies the label within that band. Thus any contiguous cube of lag values in this restricted regime is impossible, and any square uses at most six distinct large labels in one copy for sufficiently large X. The result does not prohibit long aperiodic common-label paths, mixed-band lag cubes or arbitrary revisits of individual lag values. Cube-free words alone do not bound trajectory length for an alphabet with multiple labels. No estimate of total far-pair energy is implied.

## 4. Reproducible finite audit

    python3 research/min_cube_free_audit.py 256 1024 4096 16384 65536

Python 3 replay of full original trajectories and exact contiguous-slice equality. For every square ww it checks the side words differ, and whenever there is room for a third copy checks that it differs in labels. All runs pass. Tested local Git blob 73c1dc904b170c9ef6636496992d9054696d8290, exact remote readback at e46d6f7cdf3e7881fa5747442c331865c78ada04.

| X | events | max word length | squares | third-copy checks |
|--:|--:|--:|--:|--:|
|256|1354|26|94|82|
|1024|4146|39|228|189|
|4096|30191|83|1471|1317|
|16384|161096|123|7719|7038|
|65536|796161|195|33422|30911|

At all these X the first square example is 3,3 with signs +1,-1 at the first source M=X+1. Total squares 42934, third-copy checks 39537. The six-distinct-large-prime bound is an asymptotic paper deduction and is not asserted as a tested finite threshold here.

The previously interrupted lag-cycle audit and note already existed remotely. The C++ and independent literal Python source blobs were re-fetched from the branch and matched local Git hashes; C++ was recompiled and rerun through X=262144 with identical results, and the literal Python oracle re-run at 256 and 1024 with agreement. The prior largest run at X=1048576 survives in its local results file and the existing note. Main unchanged; no new Lean compilation. Next task: bound the source-weighted length of aperiodic common-label segments and common suffixes, not merely exclude further exact repetitions.
