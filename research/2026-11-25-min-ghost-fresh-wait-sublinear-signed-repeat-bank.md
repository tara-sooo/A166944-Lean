# Fresh completed waits are sublinear, and the signed repeat bank

2026-11-25 JST. Continues b83a40a75a628d4cbd23c981ca005f56465c59e1 on the SAME research/min-cycle-forest-2026-11-24 branch. Original probability/deterministic deductions using the established exact CRT history law and the elementary prime-count upper bound. Finite shared-CRT simulations and exact pathwise ledger checks. No external search, no Lean compilation. The fresh-wait bound is unconditional; the repeat-bank convergence and the physical far-coalescence bound remain open.

## 1. Work with completed waits rather than raw label gains

Use the common infinite CRT ghost of research/2026-11-24-min-infinite-crt-ghost-cutoff-conditional-gaps.md, including its exact conditional law after revealing selected labels and quiet ticks. The results below also hold uniformly for any fixed finite alphabet of odd primes, even one depending on the observation horizon U. Write s_i for executed event times, with s_0=0; p_i for labels; w_i=s_i-s_(i-1); g(s) for cumulative horizon gain. The signed height at attained events is 2s_i-g(s_i). A label is fresh at its first selection in this path, and repeated at every later selection. Freshness is relative to the original time zero, not a reset after each block or time window. No extra waiting time after the last executed event is counted.

For integer U>=2 define
    F(U)=sum_(s_i<=U, fresh) w_i,
    Rw(U)=sum_(s_i<=U, repeated) w_i.
The claim of this note is
    E F(U) = O(U/log(2U)),
with an absolute uniform constant. This is stronger than just bounding the positive signed increments at fresh large labels, and requires no tail estimate for the lifetime of any finite ghost.

At every event, even in the relative CRT ghost with signed height possibly negative, the selected prime is eligible throughout the frozen interval since the preceding event. Its next matching clock is at distance <=2p from that preceding attained state. Hence w_i<=2p_i. This argument does not use the canonical physical height nonnegativity; it holds on the random phase rectangle.

Set z=ceil(sqrt(2U)). The sum of all fresh waits for labels p<z is at most 2 sum_(p<z prime) p, deterministically, since each such prime is counted once. The elementary prime-count upper bound makes this O(U/log(2U)).

For labels p>=z use the filtration containing the entire tick history through s-1, for each tick s<=U. In particular let ell(s) be the last selected event time strictly before s (0 if none), and w=s-ell(s). Both w and the set of unused labels are measurable in this past. For any unused p, its allowed coordinate set has cardinality at least p^2-(s-1). The conditional probability of selecting p at s is at most the probability of its matching pair, therefore
    Pr(p is selected fresh at s | history) <= 1/(p^2-(s-1)) <= 2/p^2
for p>=z. A selection at this tick necessarily has p>=w/2. Thus the conditional expected F-contribution at tick s from these large fresh labels is at most
    2w sum_(p>=max(z,w/2) prime) 1/p^2
      <= O(w/[max(z,w/2) log(max(z,w/2))])
      <= O(1/log(2U)).
The bound uses w/max(z,w/2)<=2, and log z comparable to log(2U), including histories with very long existing quiet plateaux. It is uniform in the history; no distribution for the plateau length is assumed. In the finite alphabet sum only over its available primes; the infinite sum is an upper bound. The prime reciprocal-square tail estimate follows by partial summation from pi(x)=O(x/log x).

Sum this predictable one-step expectation over s=1,...,U and add the deterministic small-prime term. This proves the claim. It is important here that w is known BEFORE the label at tick s is selected. Summing the crude individual first-selection probabilities times p instead would lose a harmonic-prime factor over a large label range. The wait-dependent lower bound p>=w/2 is what eliminates it.

In particular for any fixed epsilon>0,
    Pr(F(U)>epsilon U)=O(1/(epsilon log(2U))).
The maximum F(s) over s<=U is F(U) by monotonicity. The sum V_f^+(U) of positive signed increments at fresh events satisfies V_f^+<=2F(U), so has the same O(U/log(2U)) expectation bound. These conclusions hold even if a fresh selection has a huge negative signed increment, and do not require finiteness of the expected cumulative gain in the infinite model. Only completed waits are integrated. They also hold as upper bounds on these nonnegative quantities through any earlier stopping time <=U.

## 2. Preserve the negative credit of all first selections

Let G_f(s)=sum_(fresh events through s)(p-1), G_r(s)=sum_(repeat events through s)(p-1). Define the signed repeat bank on attained times
    B(s)=2 Rw(s)-G_r(s)-G_f(s)
        =sum_(repeat through s)(2w-(p-1)) - sum_(fresh through s)(p-1).
The fresh gain is a debit, so all of its negative height effect is preserved, even for labels which never return. Set B(0)=0 and Bmax(U)=max(0,B(s_i):s_i<=U). Use D_infty(U) for the corresponding attained-event signed peak in the infinite ghost (D_(Y,U) in a finite alphabet <Y). The exact pathwise identity is
    2s_i-g(s_i)=2 F(s_i)+B(s_i).
Since F is nonnegative nondecreasing, this gives the TWO-SIDED bound
    Bmax(U) <= D_infty(U) <= Bmax(U)+2 F(U).
Consequently
    0 <= D_infty(U)-Bmax(U),
    E[D_infty(U)-Bmax(U)] <= O(U/log(2U)).
Both maxima are finite and at most 2U, even if the expectation of G_f itself were infinite. In particular the previous sufficient criterion D_infty(2S)/S ->0 in probability along a diverging sequence is EQUIVALENT to Bmax(2S)/S ->0 in probability along that sequence. This is a reduction with an actual sublinear error estimate, not an assertion that the remaining bank vanishes. It also applies to arbitrary finite cutoffs. The stronger condition Rw(U)=o_prob(U) would suffice but is not required, since Bmax uses all negative gain as credit.

For example, a path with no repeated selections has Bmax=0 and D<=2F. More generally, the probability of attaining epsilon U while Bmax<=epsilon U/2 is O(1/(epsilon log U)), unconditionally, no matter how many labels were selected. Thus large attained peaks outside the proved error must come from the remaining repeat bank. This does not show that positive variation at repeated labels is itself small, and does not give a deterministic bound Bmax=O(1).

## 3. Absorb the repeated small-prime events into signed high blocks

For an auxiliary cutoff A>=5 let L_A=2 product_(3<=p<A prime)p. In this section high means p>=A, irrespective of whether it is fresh. Split the event sequence through U into the initial run of labels <A and then blocks consisting of one high event followed by all successive low events up to the next high event or the end of the observation window. A block at the last high event may have no low events; a final incomplete waiting interval is omitted. The earlier low barrier and w<=2p bound imply that every contiguous low run has signed maximum increment <=5L_A, irrespective of previous gain or relative signed height. In the common CRT ghost this follows by translating the relative horizon to the even representative modulo L_A, and the relative time to the representative of its clock phase. Every low step agrees with the low-only ghost until the next high interruption.

For high block i let p_i,w_i describe its starting high event and d_i be the nonnegative maximal signed increment of its subsequent actual LOW-only prefix, including empty prefix. Thus 0<=d_i<=5L_A. Relative to the attained state immediately BEFORE that high event (before its waiting interval), the maximum nonnegative height gain over the block is exactly
    b_i=[2w_i-(p_i-1)+d_i]_+.
The initial low run contributes at most 5L_A to the peak. Total peak is bounded above by this initial maximum plus the sum of b_i, since each block's endpoint increment is <=its maximum, and an attained peak belongs to some block. This is an upper bound, not an equality of the global maximum with a sum of block maxima.

At a fresh high event,
    b_i <= 2w_i + (5L_A-p_i+1)_+.
Every such p_i is distinct, so summed over ALL fresh high blocks the extra correction is at most
    C_A=sum_(A<=p<=5L_A+1 prime)(5L_A-p+1)_+
       = O(L_A^2/log(2L_A)).
Thus, with
    E_A(U)=sum_(repeat high block starts through U) [2w_i-(p_i-1)+d_i]_+,
there is a deterministic inequality
    D_infty(U) <= 5L_A+2F(U)+C_A+E_A(U).
The same holds for any finite alphabet. In particular choose any A=A(U)->infinity slowly enough that L_A<=sqrt U (for example the maximal permitted primorial cutoff), then 5L_A+C_A=O(U/log(2U)). The fresh blocks and initial low block can be removed from the peak estimate at an expected O(U/log(2U)) cost. No need to separately count repeated selections of primes <A, or to control the total positive drift of each low block independently of its entering label. The negative gain of the entering high label offsets its following low peak.

There is a further explicit split of E_A. For repeated block starts with p>=10L_A+2, a positive b_i forces
    2w_i>p_i-1-d_i >= p_i/2,
hence w_i>p_i/4. For smaller repeated high starts, A<=p<10L_A+2, the per-block surplus is O(L_A) because w<=2p and d<=5L_A. Therefore
    E_A <= O(L_A * #repeat starts in [A,10L_A+2))
         + sum_(repeat starts p>=10L_A+2, w>p/4) [2w-(p-1)+d]_+.
This is a possible more focused route to the signed peak condition. The count of intermediate repeated starts and the large repeated long-wait block surplus are not shown sublinear here. The previous terminal-gap and global clock-isolation estimates may be applied to the latter where their scale assumptions hold, but do not by themselves bound the sum over all such labels. The bank in section2 is potentially stronger because it allows negative blocks to compensate later positive blocks; E_A is only a nonnegative sufficient majorant.

## 4. Finite diagnostics

Saved research/min_ghost_fresh_wait_signed_bank_audit.mjs and research/min_ghost_fresh_wait_signed_bank_results.json, exact remote readback at afa45b6eb0bdc0f1a25afb41fefcae29a76af131. Independently sample the common CRT coordinates with fixed pseudorandom seeds and finite alphabet of odd primes <=4U, U=256,1024,4096,16384,65536; 512 paths per U except 256 at U65536. This is a finite cutoff test; the asymptotic coupling error to the infinite path is O(1/log U), not a calibrated finite sample error. Simulate the exact earliest next clock and least-label tie break. At each attained event check w<=2p, decomposition of elapsed time and gain into fresh/repeat parts, positive/negative signed increment ledgers, and bank/peak inequalities. For the large fresh-wait compensator integrate 2w sum_(p>=max(z,w/2), p<=4U)1/p^2 over every tick including the last frozen tail, using prefix sums indexed by w. This is a predictable upper bound, not an exact conditional expectation and not a pathwise bound on realized fresh waits. Check the deterministic low fresh budget 2 sum_(p<z) p. No empirical verification of the asymptotic implied constant.

Track actual blocks for A=5,7,11 (L_A=6,30,210), including the initial and final blocks. Check each low-only signed peak <=5L_A, fresh block surplus bound, large repeat positive implies 4w>p, decomposition of repeat surplus into the two label bands, and global peak upper bound by initial/fresh/repeat block sums. The actual d_i is measured only over executed low events in the observed block; no hypothetical complete low suffix beyond the window is substituted. No Lean compilation.

Selected sample means:
    U       F(U)          Rw(U)       D(U)        Bmax(U)
    256     86.2715       29.3926     85.0703     3.2969
    1024    307.5645      66.6230     262.2188    3.1094
    4096    1056.8184     129.6992    732.0938    4.3086
    16384   3609.3555     204.9746    2481.9102   2.8516
    65536   12562.0391    292.7773    9710.8984   3.8125
At U65536, 56 of256 samples have D>U/4, but none has Bmax>U/4. 107 have F>U/10. Mean fresh positive variation10572.3125, repeat positive348.0546875, repeat negative52.6328125; mean fresh gain21075.921875 (finite alphabet only). 15066 executed-event ledger checks at that window. For A11 the mean repeat block surplus is230.484375 (206.1796875 medium,24.3046875 large), and 1 of256 paths has E_A>U/10. Across the samples there is substantial repeated event count (mean43.828125 at U65536), while repeated elapsed waits are much smaller than fresh waits. These are empirical observations, not a proof of sublinear repeat waits or bank convergence. The exact identity explains why the bank can be much smaller than the repeat positive variation.

## 5. Remaining work

The unconditional O(U/log U) fresh completed-wait theorem removes an entire class of actual events from the signed peak problem, including positive contributions from fresh large labels across all scales. The negative fresh gains can be kept in the repeat bank at no additional error. Alternatively group the small-prime repeats with the high event which initiated their block and retain only positive repeated-high block surplus. Neither the repeat bank nor its sufficient majorants are proved sublinear. Further work should seek a return/credit estimate for repeated labels; the global physical far-coalescence estimate remains independently unresolved. The barrier-geometry scale obstruction of the preceding note is unchanged. No new branch, no main edit, no twin-prime proof.
