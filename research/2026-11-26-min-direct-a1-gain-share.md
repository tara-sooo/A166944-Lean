# A1 gain-share ceiling and sharp six-decrease nonreset recovery

Continuation of [1924deb](https://github.com/tara-sooo/A166944-Lean/commit/1924deb3d9c5a23fc6f07a796ad579520006f631). Two new directions: an additive recovery budget implies a uniform upper bound of 5/14 on the macroscopic horizon gain supplied by A1, independently of endpoint deficit; combined with dense modular barriers this forces additional B events or a stronger A1 count in root-sparse windows. Separately the previous six-decrease lower bound is sharp even for canonical integer ancestry, with arbitrarily small relative waiting times in the recovery. No twin-prime contradiction or Lean kernel verification.

## 1. Uniform A1 gain share

At an event p, with gain g=p-1, pre/post ordinary deficit d,d', and side indicator I=(1-e)/2, the exact identity is d'=d+2w-g, w>=1. For A1 (p>=47,p>=5d+15,D=2p), d'=2p+6I and hence
    5(d'-d)>=9g+24+30I.
All other events have d'-d>=2-g.

In any finite contiguous block of actual canonical events, let F be the gain of ANY designated subset of A1 events, m their count, and G the total block gain. If m=0 the ceiling is trivial. Otherwise truncate the block immediately after its last designated A1, with gain G_*<=G; let n_* be the count of other events in that prefix, d_a the initial deficit, d_* the final deficit. Summation gives the exact stronger inequality
    14F+24m+10n_*+30 sum_marked I <=5G_*+5(d_*-d_a).       (1)
The right endpoint is an A1, so d_*<=2C+6 where C=floor sqrt(Y+1), Y bounds all pre-horizons of the block. Since d_a>=0,
    F <= (5/14)G+(10C+30)/14.                            (2)
Crucially the actual final deficit of the full block can be arbitrarily high: it is not an error term in (2). The last designated A1 is a suitable endpoint automatically. The same inequality applies to all A1, or just high-far A1, with all unmarked events counted as other events. In particular the other-event gain in that prefix satisfies
    G_*-F >= (9/5)F+(24/5)m+2n_*+6 sum_marked I-(2C+6)+d_a.
This is an additive counterpart to the earlier logarithmic recovery budget. It allows ordinary increases between recovery events, all reset types, and arbitrary repeated labels. No requirement of small deficit at the end of the original window.

## 2. Coupling the ceiling to dense barrier capacity

Use the high-far subset and notation of [cafea3c](https://github.com/tara-sooo/A166944-Lean/commit/cafea3c33ea989eb4134c90125d85f5f0e36efd5) and [3f1448b](https://github.com/tara-sooo/A166944-Lean/commit/3f1448b7868095d73e15492d75b323faf760b98a). For a cutoff R, P=P_R is the product of odd primes <=R and alpha=alpha_R the even-position barrier density. The residual L0=G-N_g-2P(N_c+1) uses high-near gain/count N_g,N_c. Every high-far event is either A0 (large-label low-deficit reset), A1, or B (failure of the low-deficit test). Let (F_i,m_i,b_i) be gain, count, covered barriers of each class, i=0,1,B. For sufficiently large R>=47 this is a partition, with
    2(b_0+b_1+b_B)/alpha >= L0,
    2b_i/alpha <= F_i+2P m_i,
    F_i>=2b_i.
Using (2) for the designated high-far A1 events gives the finite constraint
    2b_B/alpha >= L0-(5/14)G-(10C+30)/14-2P m_1-F_0-2P m_0.  (3)
The RHS need not be positive on a short finite block. When positive it is simultaneously a lower bound on F_B/alpha, F_B+2P m_B, and (C+2P)m_B. More precisely each of those three quantities is at least 2b_B/alpha.

For an infinite canonical ray crossing [X,lambda X], lambda>1 fixed, take R=floor(c log X), 0<c<1/(8 log 2). Then P=o(sqrt X), C=O_lambda(sqrt X), G=(lambda-1)X+O(sqrt X), L0>=G/2-o(X). The seven-tick normalization associates each A0 reset to a canonical reentry (up to one pending at the right boundary), hence m_0<=N+1 where N is the root count in the window. If N=o(sqrt X) along a sequence of windows, F_0+2P m_0=o(X). Consequently
    2b_B/alpha + 2P m_1 >= G/7-o(X).                    (4)
This is new: the previous trichotomy alone allowed all far-barrier capacity to be assigned to A1, even with only O(sqrt X) such events. The gain-share ceiling removes that possibility in root-sparse windows.

In particular along any sequence of root-sparse windows:
* If m_1=o(X/P) (including m_1=O(sqrt X)), then
    m_B>=((lambda-1)/(7 sqrt(lambda))-o(1))*sqrt X,
    F_B>=((lambda-1)/7-o(1))*alpha X,
    F_B+2P m_B>=((lambda-1)/7-o(1))*X.
All B events are high-far, with pre deficit d>(p-15)/5, so their distinct pre-deficit sum is also Omega(alpha X).
* If m_B=o(sqrt X), then b_B/alpha<= (C+2P)m_B/2=o(X), and (4) yields
    m_1>=((lambda-1)/14-o(1))*X/P.
Since F_1<=O(X), at least half of these A1 events have labels <=1+2F_1/m_1=O(P), by counting labels with g>2F_1/m_1. Thus Omega(X/P) A1 events have R<p<=O(P), and their preceding plateau is rough to p-1 and globally least factor as in 3f1448b.
* More generally (4) forces one of m_B=Omega(sqrt X) or m_1=Omega(X/P) on each sufficiently large root-sparse window, using the capacity per B event. In the B branch the corresponding positive fraction of alpha X barriers also gives F_B=Omega(alpha X). Constants can be chosen uniformly over the ray once the root sparsity error is small. The dominant branch may vary between windows.

For example c=1/(16 log 2) gives P<=X^(1/4), so if both N and m_B are o(sqrt X), A1 must have Omega(X^(3/4)) events, not merely Omega(sqrt X). Choosing a smaller fixed positive c makes this exponent arbitrarily close to 1, at that chosen cutoff. It is not a uniform assertion simultaneously for growing cutoffs or a contradiction with finite twins. The new result gives a genuine upper bound on A1 gain but leaves the possibility of numerous lower-label A1 or B events.

## 3. Rigidity at the six-decrease boundary

Recall the previous A1 pair p,r with no deficit-decreasing reset in between and r<=p. Let u=d+3. For a decreasing nonreset with label s and post D=2hs, integer h>=1, we have d'=2hs+6I and
    u/u' = 1+(s-1-2w)/(2hs+6I+3) < 1+1/(2h).
The exceptional label3 never decreases deficit. A1 endpoint ratio u'_p/u_r >10p/r. Any nondecreasing events only reduce the net recovery ratio, so six decreasing events give a product upper bound (3/2)^6. If one has h>=2 the product is <=(3/2)^5*(5/4)=1215/128<10, impossible. Therefore when exactly six decreases suffice:
    every decreasing nonreset has D=2s;
    r>(640/729)p.
The latter follows from 10p/r<(3/2)^6. Also each of the six decrease steps has u/u' >10/(3/2)^5=320/243, since the other five supply at most (3/2)^5. This imposes a relative waiting restriction via the displayed exact ratio. Nondecreasing events may occur between these decreases; the conclusion on the six steps does not exclude those events.

If two adjacent actual nonunit events both have adjusted D=2 times their label, with labels a,b>3 and indicators I,J, the wait v for the second obeys
    3b=2a+1+2v+6(I-J).                                (5)
This follows by substituting d=2a+6I,d'=2b+6J into the update. In particular v=1 is impossible by reduction mod3, and v=0 mod3 for a=1mod3, v=2mod3 for a=2mod3. The restriction is specifically for adjacent events with these adjusted deficits, not for intervening nondecreasing events or other D.

## 4. The six-decrease lower bound is sharp, with short recovery waits

We construct an actual canonical trajectory with A1 label p, exactly six consecutive decreasing nonresets, then A1 label r<p, without any reset or intervening nonunit event. There are such constructions for arbitrarily large p. Fix any 0<eta<=1/1000. Choose p large prime with p=3 mod4 and p=1 mod every odd prime <=16. Choose six labels s_i in
    (2/3+eta)s_(i-1)<s_i<(2/3+2eta)s_(i-1), s_0=p,
and a final label r in (0.94p,0.98p). All seven later labels are primes 1mod4 and 1mod every odd prime <=16. Since (2/3+.002)^6<0.09, for sufficiently large p these conditions ensure r>=10s_6+15. The six decreases are strict and their waits are
    w_i=(3s_i-2s_(i-1)-1)/2,
which are positive even integers, each less than 3eta*s_(i-1). Thus waits in the recovery can be made arbitrarily small relative to the labels. The A1 events themselves have long waits.

Here is the selection and CRT compatibility proof. Write a_0=p,a_1=s_1,...,a_6=s_6,a_7=r, h_i=sum_{j<i}(a_j-1). At every desired stage i require H_i=H0+h_i=1 mod a_i, and H_i avoids +-1 modulo every other odd prime l<=B_*=3p+6. All a_i are distinct, positive constant multiples of p, since eta is fixed. At chosen primes enforce mutual compatibility during the sequential selection:
* A new a_j must not divide h_j-h_i or h_j-h_i-2 for i<j; these positive integers are O(p) and the candidate prime is Omega(p). Only O(1) candidates are excluded for each i. This ensures the earlier stages avoid +-1 modulo a_j.
* At the next shift h_(j+1)=h_j+a_j-1, require h_(j+1)-h_i not congruent to 0 or -2 modulo a_i for each i<j. This excludes at most two residue classes for each older prime, and only O(1) candidate integers in the chosen interval of length O(p), since a_i=Omega(p). For the current a_j the next H coordinate is 0 modulo a_j automatically. These checks ensure later stages avoid +-1 modulo previously chosen primes as induction proceeds.
The intervals have length Omega_eta(p) for every fixed eta>0. The classical prime number theorem in the fixed arithmetic progression 1 mod (4*product odd primes<=16) gives arbitrarily many candidates as p grows, so these bounded exclusions cannot obstruct the selections. Existence of arbitrarily large initial p in its own reduced class follows from the same theorem (or Dirichlet). At each small odd prime l<=16 all shifts vanish, and residue H0=0 works; at unchosen primes l>16 there are at most 16 excluded residues, leaving one. At each selected prime the above consistency proves the forced residue is allowed. CRT together with H0=0mod4 gives a fixed nonempty set of residue classes for each selected word. Choose a representative large enough that all chosen labels are eligible. This uses no prime-tuple conjecture.

From the canonical start t0=H0/2+3, p fires on the even side at wait (3p-7)/2. Post deficit is 2p and H1=2mod4. All subsequent chosen primes are 1mod4 so the horizon stays 2mod4; all later event times are even because their intended waits are even. For each recovery stage the selected even-clock defect reaches 3s_i at its proposed wait, with no earlier multiple in the relevant 4-class (the preceding such multiple is -s_i, whereas future defects are positive). The final A1 stage has the same first positive multiple rule. Before and at each desired event the raw gcd divides its signed odd defect, of absolute value <=3p+6. All prime factors except the chosen one on its correct side are excluded by CRT. Thus the true least-eligible MIN clock gives precisely the prescribed sequence and D=2a_i at all eight events. All intermediate ordinary deficits exceed 6, so there is no canonical reentry, even in quiet ticks, between the two A1 events. This is actual canonical ancestry, not merely abstract plateaus.

Hence no argument can strengthen the uniform six-decrease bound to seven in the r<=p case, or require any recovery wait to be a fixed positive fraction of its label. The family has a varying initial integer and does not show such recoveries repeat on one infinite ray.

## 5. Reproducible diagnostics

[Audit f0362b2](https://github.com/tara-sooo/A166944-Lean/blob/f0362b27d195543873ba3f4a4976e3da57d4b517/research/min_direct_a1_gain_share_audit.mjs), blob 69a41e0f7bb669fd3df4371de434e568f16fc443, exact remote readback. Run node research/min_direct_a1_gain_share_audit.mjs 100000 180. Actual ECMAScript function execution in tool runtime, not a separate Node process.

49,998 odd canonical roots<=100000, 1,020,339 actual events, 9,591 A1, 184,526 decreases, 49,989 stopped before cap, 9 cap-unresolved. 12,400 exact additive prefix inequalities, 91,568 block gain-share checks, 12,219 other-gain checks, 366,272 modular barrier coupling checks for R=5,7,11,13 (30,464 positive residual checks). The audit uses the A1 vs non-A1 high-far partition for these small cutoffs; the analytic large-window A0/A1/B split uses R>=47. All assertions passed; no observed macroscopic crossed window claimed.

A finite search with 2,843 extension attempts found an admissible word, using direct CRT compatibility rather than the much stronger fixed-AP recipe in section4. Constructed a 9,962-decimal-digit canonical root with the eight consecutive even events:
|label|wait|pre deficit|post deficit|A1|
|--:|--:|--:|--:|--|
|7687|11527|6|15374|yes|
|5233|162|15374|10466|no|
|3541|78|10466|7082|no|
|2389|42|7082|4778|no|
|1621|42|4778|3242|no|
|1093|18|3242|2186|no|
|733|6|2186|1466|no|
|7369|10320|1466|14738|yes|
20,600 stage-residue checks, 22,195 literal BigInt gcd ticks, including actual eligibility, all pass. The audit reconstructs the full root by CRT and does not need a stored giant decimal string. The previous scan found no reset-free A1 pair; this explicit example shows that absence was only finite-sample behavior. No Lean kernel verification. Main/sibling branches unchanged.

Next: exploit (4) by bounding the contribution of the numerous smaller A1 events when B and canonical returns are sparse, or find a global frequency bound on B. The sharp recovery construction means a proof based only on ruling out a fixed finite sequence of fast nonreset decreases cannot succeed for this minimal pattern. No contradiction with finite twins yet.
