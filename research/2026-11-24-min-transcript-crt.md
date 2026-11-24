# Exact relative-history cylinders and a conditional CRT comparison

2026-11-24 JST. Continuation of the source-preserving merge ledger (9450ea5e3ebd0909bffb775093330e2d37cd968e). New elementary paper identities and finite audit. The finite-window distribution estimate and twin-prime conjecture remain OPEN.

## 1. Exact factorization of a transcript

Use the canonical MIN wheel, original odd M in [X,2X), B=ceil(sqrt(7X)), initial t=M+2, C=2M-2, and cutoff K(M)=floor((7M-1)/4). A transcript H of j events fixes the successive relative times v_i=t_i-(M+2), labels q_i, and therefore gains G_i=sum_(h<=i)(q_h-1). At a fixed plateau with (G,s), C=2M-2+G and t=M+2+s.

For an odd prime p<=B, its candidate relative time, with infinity when ineligible, is a function only of M mod p: the parity restriction on M determines M mod 2p. A finite candidate requires one of 2M-3+G or 2M-1+G to vanish mod p. The two eligibility residues are distinct. Compute the first strict subsequent tick in the appropriate parity-clock progression. For a given prescribed next pair (v,q), require the candidate of q to be exactly v and all other candidate pairs to be lexicographically larger. These tests factor prime by prime. Intersect the allowed residue sets over every step, obtaining A_p(H) subsets of Z/pZ. Then an original root has this prefix IF AND ONLY IF
    M mod p in A_p(H) for EVERY odd p<=B, and 3M>=9+4v_j.
The latter is exactly the original cutoff restriction at the last event (and implies it at all earlier events). Proof by induction using the unique actual lexicographic MIN rule. This is not just a necessary eligibility test: the competition constraints are included.

For a nonempty consistent cylinder, every selected prime has exactly ONE remaining residue. Every never-selected p loses at most two residues per step, so |A_p(H)|>=max(0,p-2j). Write D(H) for the product of distinct selected primes; the selected conditions fix one residue modulo D(H). The even-multiple barrier gives G_j<2D(H). Thus a sufficiently long-gain transcript cannot contain two distinct roots separated by less than D(H) (indeed odd roots differ by a multiple of 2D(H)). This controls identical RELATIVE transcripts, not physical coalescence of different transcripts.

## 2. Conditional comparison on the complete CRT period

For this comparison only, remove the source-dependent cutoff, and choose an odd residue uniformly modulo 2 product_(odd p<=B) p. Conditional on a consistent prefix, residues are independent with uniform distributions on A_p(H). This independence is an exact CRT fact for the full period. It is NOT established on [X,2X). In particular for a never-selected p>2j, its probability of being eligible at the current plateau is at most 2/(p-2j). With Q=ceil(B/log^(2/3) B), for j<=Q/4, the conditional probability of ANY fresh p>=Q being eligible is at most
    sum_(Q<=p<=B prime) 2/(p-2j)
    = O(log log B/log B).
The same upper bound applies to fresh large labels winning the next clock. It does not bound returns of already selected labels. An actual next-event renewal calculation should therefore track already selected labels separately and apply this formula only to fresh candidates.

There is also an exact relative-clock check independent of the selected root after eligibility has fixed its residue. At relative event time v and pre-gain G, if the side is -1 (even absolute time, v odd), p divides 2v-G+7. If the side is +1 (odd absolute time, v even), p divides 2v-G+1. These follow by eliminating M between eligibility and the clock congruence. Both integers are odd and hence nonzero. The invariant 2t-C>=0 bounds their sizes by O(1+v). They can be factored to enumerate candidates/competitors at relative time v instead of scanning every prime. This identity applies to the actual consistent transcript and all candidate residues at its prescribed plateau.

## 3. The finite-window bridge (open)

For a fixed consistent transcript with selected product D and p not dividing D, the possible roots with a fresh p candidate lie in at most two residue classes modulo Dp by CRT. Counting odd roots in [X,2X) gives O(X/(Dp)+1), even after ignoring the other exclusion conditions. Sum over Q<=p<=B to get
    O((X/D) log log B/log B + B/log B)
candidate root-label incidences for this transcript. Thus if D<=B and the actual cell has size >=c X/D for fixed c>0, the desired conditional bound of order log log B/log B holds on the actual finite window as well. This last size hypothesis is not established and often fails for thin cells. With D>B, the +1 errors are especially serious. The product can become large after just a few large-prime hits. One must not condition on complete CRT uniformity as if it held on the original short interval.

Concrete next work:
1. Use the exact A_p to build a symbolic prefix tree. Measure selected products, actual cell sizes, and excluded-residue densities for short histories. Separate the errors when D small from the sparse-cell regime D large.
2. Develop an aggregate sieve / moment estimate on those cells with real source weights. The residue-counting identity is the new arithmetic input; adaptivity alone is no longer a reason not to write explicit sieve conditions. A separate bound for already selected-label return blocks (e.g. the shadow with seen primes only) is still needed.
3. Link an actual finite-window bound on long survival or original-source weighted return cost back to the already proved full clock budget. This is a proposed alternative to counting all pairwise physical mergers; it is not a proved global contraction. In particular a successful CRT model on the full primorial period does not prove anything about actual survival in the dyadic interval without a transfer estimate.

## 4. Finite audit

Run python3 research/min_transcript_audit.py 256 1024 4096. For prefix lengths 1,2,4,8 the code groups all real roots that reach the length, computes exact A_p by modular tests, and verifies equality of the predicted and actual complete source sets, including the original cutoff. It asserts singleton selected-prime residues and at most two exclusions per nonselected-prime per step. All checks pass. Number of distinct nonempty prefix cells checked (sum over lengths): 211, 594, 2414 respectively, total 3219. At X=4096, j=8, 1212 distinct cells covering 1248 sources that have at least eight events; this illustrates the thin-cell problem, not a proof of the needed estimate. No Lean compilation. Main unchanged.
