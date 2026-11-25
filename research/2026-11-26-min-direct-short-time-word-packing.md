# Short-time CRT word packing and support-barrier budgets for repeated returns

Continuation of [7005b51](https://github.com/tara-sooo/A166944-Lean/commit/7005b5164212f265aab5f10f244c94fa3c9f9712). Single fixed-cut congruences give no extra uniform saving at unit waits. Here count entire tick words with bounded initial deficit. The fixed starting deficit and time parity determine a branching process with few possible prime labels per tick, while the distinct selected labels impose simultaneous horizon congruences. This gives a subpolynomial occurrence bound for short bursts of logarithmic-size primes at polylogarithmic deficit. Independently, repetition of an identical word at fixed deficit and parity requires gain from outside its support, quantified using dense horizon barriers. No global stopping theorem.

## 1. Tick words and bounded branching

Use the established adaptive MIN rule: at tick n=t+1, side I=n mod2, e=1-2I, choose the least odd prime s dividing gcd(n-2I,H-e) with s^2<=H+1 if one exists, otherwise quiet. A quiet tick has gain 0; a selected prime s gives gain s-1. Write d=2t-H before the tick, d_new=d+2-g. On canonical trajectories d>=0 throughout. At any selected tick,
    s divides F=d+3-6I.                                 (1)
Indeed F=2(n-2I)-(H-e). This integer is odd and nonzero even when d=0 or2. Since H-e is odd, the raw gcd equals gcd(F,H-e). For a fixed initial deficit d0, fixed starting time parity I0=t mod2, and word of tick labels (0 for quiet, odd prime for event), all later deficit values and side parities are determined independently of the starting horizon.

Fix integers D>=0, L>=1. Consider words of exactly L ticks starting with 0<=d0<=D on actual canonical trajectories. More generally the counting proof applies to any adaptive starts/words staying in d>=0 during the word. Since each tick increases deficit by at most2, the absolute value of F throughout is <=D+2L+3. The distinct odd prime divisors of a nonzero odd integer F are at most floor(log|F|/log3) (zero if |F|=1). Hence for each fixed initial d0,I0, the number of possible words is at most
    B^L, B=1+floor(log(D+2L+3)/log3).                     (2)
At each tick there are at most B-1 possible prime labels by (1), plus the quiet choice. This overcounts because not every such choice is compatible with the horizon residues, tie rule, or cutoff; an upper bound is sufficient. This is a deterministic branching count, not a distribution model for deficits or prime factors.

For a fixed word, let G_j be the sum of gains before its j-th tick. Every selected label s at that tick requires
    H_start= e_j-G_j mod s.                              (3)
Here e_j is fixed by starting parity and index. If a repeated label gives inconsistent residues then the word has no starts. Otherwise for the distinct support F of selected labels put P_F=prod_{s in F}s. Equation (3), together with
    H_start=2I0-d0 mod4,
places the possible starting horizons in a single congruence class modulo 4P_F. This assertion is necessary, not sufficient; it requires no assertion about which abstract starts are reachable. For any interval [A,A+G] of starting horizons, the number of possible distinct starts for this word,d0,I0 is at most
    1+floor(G/(4P_F)).                                   (4)
A fixed pair (H_start,d0) specifies the absolute tick uniquely, so on one ray it cannot be counted twice, even if the horizon is constant at quiet ticks. We can count overlapping words without double-counting their start ticks.

## 2. Packing many large labels into a short time

If a selected prime s occurs at two ticks n1<n2, with sides I1,I2, the clock condition implies
    s divides n2-n1-2(I2-I1).
For the same side this difference is positive even, hence >=2s. For opposite sides it is odd and nonzero. If I2-I1=1, the value is >=-1; since s>=3 its divisibility forces >=s, giving gap >=s+2. If I2-I1=-1 it is positive and >=s, giving gap >=s-2. Thus in all cases
    n2-n1 >= s-2.                                       (5)
This holds regardless of any intervening events. For integer S>=4, a word of L ticks has at most
    m=1+floor((L-1)/(S-1))
occurrences of any one label s>S. If the word contains at least k such events (1<=k<=L), it contains at least j=ceil(k/m) distinct labels >S. Its full support product is therefore >=(S+1)^j. In particular for L<S (or L<=S-1) all such labels are distinct; the stronger L<S-1 convention used below also suffices.

Combine (2)-(4) and count at most D+2 combinations of even d0 in [0,D] and parity I0. We get the finite bound on distinct admissible starting states, and hence on all such start ticks of a single canonical trajectory with starting horizons in [A,A+G]:
    count <= (D+2)*B^L*(1+floor(G/[4*(S+1)^j])).         (6)
Here B is (2) and j=ceil(k/m). All low-label relays, quiet ticks, and possible increases of ordinary deficit are allowed. The only time-density condition is at least k selected labels >S within the L ticks. No independence or roughness hypothesis is used. This bound counts occurrences on an actual trajectory, not the density of root integers.

## 3. Subpolynomial supply of short high-label bursts

Consider any canonical ray and starting horizons in [X,lambda X], lambda>1 fixed. Let S be an integer cutoff with S~a log X for fixed a>0. Choose
    k=ceil(log X/log(S+1)), L=ceil(A0*k),
where A0>=1 is fixed. Let the initial deficit bound D<= (log X)^C for any fixed C>0 (integer roundings harmless). For sufficiently large X,
    L=O(log X/loglog X)=o(S), j=k,
    (S+1)^k>=X,
    B=O_C(loglog X).
The product of the first two factors in (6) is
    (D+2)*B^L
       =exp(O_{A0,C}(loglog X + log X*logloglog X/loglog X))
       =X^o(1).
The final factor of (6) is O_lambda(1). Thus uniformly for the whole horizon window,
    #start ticks with d0<=D and >=k labels >S in next L ticks
       <= X^o(1).                                       (7)
Equivalently for every fixed epsilon>0 this count is <=X^epsilon for sufficiently large X (constants depend on a,A0,C,lambda,epsilon). This is an actual power-scale upper restriction on a narrowly defined supply population. It is far smaller than the prior Omega(X^(9/11)/log X) required recovery precursor count under the sparse assumptions, but the two populations are NOT proved to coincide: that earlier population consists of individual recovery clusters, not necessarily rapid bursts of k labels with polylogarithmic starting deficit. In particular (7) does not upper-bound all of those precursors.

A weaker time-density variant: take L=floor(c log X/logloglog X) for a fixed 0<c<1, same k,S,D. Still L=o(S), j=k. Since log B<=logloglog X+O_C(1),
    count <= X^(c+o(1)).                                (8)
This allows k events over a growing average tick separation of order loglog X/logloglog X; it is not a count for arbitrary long intervals.

Concrete recovery consequence. Take cutoffs S~a log X and R~b log X with 0<a<b, as in the earlier lower-band recovery theory (the choice of S here need not satisfy its earlier matching cutoffs). Consider A1 marks with p>R, p<= (log X)^C and p>=R*k, where k above. Immediately after an A1 the ordinary deficit is 2p+6I, bounded by (log X)^(C+1) eventually. Suppose recovery to x=d+3<=p occurs and from the post-mark state to that first recovery all selected labels lie in (S,R], with each event wait at most a fixed integer W>=1. The net deficit drop is at least p+3, and each event lowers it by at most R-1. Therefore the recovery contains at least k events; its first k selected labels occur within W*k ticks after the mark. Apply (7) with A0=W and starting horizons in the enlarged [X, (lambda+1)X] (a mark changes H by at most sqrt(lambda X+1)). Distinct marks yield distinct post-mark start ticks. Hence there are at most X^o(1) such fast completed recoveries in a crossed [X,lambda X] window. This theorem applies even if intermediate deficit increases were allowed; no restriction to a monotone recovery is needed. If the size interval for p is empty (e.g. C<2 asymptotically), the assertion is trivial. If the recovery does not complete, uses labels <=S or >R, or has slow waits, it need not belong to this population.

A variant permits arbitrary smaller relays in a recovery completed within L=A0*k ticks, all selected labels <=R. If p>=S*L+R*k, the required drop >=p+3 implies at least k selected labels >S, because fewer would give total gain at most (S-1)*L+(R-1)*(k-1)<p. Thus (7) applies to this variant as well, without a bound on individual waits. These conditions are additional to the earlier sparse hypotheses; they have not been derived from them or finite twins.

The fixed-word CRT constructions of 7005b51 are compatible with (7)-(8). Their word length is fixed as horizons grow and their large-label cutoff is not S~log X for each fixed recovery label. Also the horizons may be much larger than the mark p. No counterexample to those constructions is claimed.

## 4. Repeated words and their necessary outside-support gain

The previous counting theorem used the product of distinct labels. A second result controls what must happen BETWEEN two repetitions. It applies to any fixed finite nonempty-event tick word W, with starting deficit d0 and starting parity I0 fixed, no upper bound on d0 or word duration. Let F be the distinct prime support, P=prod_{s in F}s and
    A_F=prod_{s in F}((s-1)/2), alpha_F=A_F/P.
These are the H-barrier count per period and density for precisely this finite set F, not necessarily all primes below a cutoff.

An even cut J is a support barrier when J mod s belongs to {0,2,...,s-3} for every s in F. No jump selected by s in F can cross that cut in the half-open sense H<=J<H+s-1: J-H is even in [0,s-3], H=e mod s; the residues e+(J-H) never lie in the allowed even set modulo s. This is the same elementary horizon-barrier argument as in 584d6aa, now using the support of the word. In integer coordinate J/2 these barriers have period P and exactly A_F elements per period by CRT. In particular multiples of 2P are barriers. The gain of any contiguous word using only F is strictly less than 2P, since its disjoint jump intervals contain no such cut. A word with no events is excluded (support empty would not give positive gain).

If W occurs at two distinct start ticks with the same d0,I0, their starting horizons H1<H2 differ by a multiple of 4P by (3)-(4). They cannot have equal H, since d0 fixes t at a given H. Therefore
    H2-H1=4P*m0, m0 positive integer.                   (9)
The first occurrence completes before the second starts: it gains <2P and the later start is at least4P farther in H. Between the starts the half-open H interval contains exactly 2*m0*A_F support barriers. Only events with labels OUTSIDE F can cross any of them. Let G_out be the total gain of all outside-F events between these starts, and n_out their count. A jump of gain g crosses at most g/2 cuts in total, and at most alpha_F*(g/2+P) support barriers by period counting. Therefore
    G_out >= 4*m0*A_F,
    G_out+2P*n_out >= 4*m0*P=H2-H1.                    (10)
If every outside event has gain <2P, it crosses at most A_F support barriers and hence n_out>=2*m0. All inequalities are exact finite statements; they do not assume the intermediate path has bounded deficit. In particular the outside gain is >=alpha_F times the whole intervening gain.

For M>=1 occurrences of the same word with same initial deficit/parity in a given finite block, the intervals between consecutive starts are disjoint. Summing (10) gives the repetition supply bounds
    M <= 1+ G_out_total/(4*A_F),
    M <= 1+(G_out_total+2P*n_out_total)/(4P),             (11)
where the totals may be over the whole block (or only between the first and last starts). If there are no outside-F events, the word cannot recur at all. This is stronger than the local single-cut bound in a different dimension: it charges repeated patterns to gain outside their own label support, even if their selected primes have no competing clock exclusions at unit waits. It does not assume distinct patterns have disjoint intervening intervals.

Fixed-deficit return special case. If a word starts and ends at the same deficit d0 and parity I0, its gain equals 2 times its elapsed ticks and its duration is even. By the support barrier this gain is <2P. Two consecutive identical copies of such a return word are impossible: the second start would have the same d0,I0 and be shifted by that gain, in conflict with (9). More generally every later copy of the same return word needs the outside gain budget (10). For repeated nonreset downcrosses of a fixed cut b with the same label s and side I, the post deficit is fixed by the multiplier formula of 7005b51; the intervening tick words from one such post-state to the next are thus closed-deficit return words of this form. There is a real restriction on repetitive returns even if each individual crossing is locally saturated. But varying the words/supports can evade a single-pattern bound; one cannot sum (11) over all patterns without accounting for overlapping outside-gain charges.

## 5. Diagnostics and persistence

[Short-time word audit bee3796](https://github.com/tara-sooo/A166944-Lean/blob/bee379642f40086e8bae1b14dd6f20d61bd91874/research/min_direct_short_time_word_packing_audit.mjs), blob 424da03a5ee7041436774ca06daf63ed0acbdab3. Exact remote readback. Run node research/min_direct_short_time_word_packing_audit.mjs 12000. Actual ECMAScript tool-runtime execution. 5998 odd canonical roots through12000, 869890 literal integer ticks,87242 selected events, cap4000 ticks per root (no claim all roots stopped within the cap). Also51794 exhaustive abstract start controls with H100..1200, small deficits and word lengths4/8/12. 387827 word groups,392724 distinct start occurrences in the checked groups (overlapping diagnostic sample sets),4897 exact congruence spacing checks,3774028 per-tick defect/branch checks,447021 high-label occurrences checked for repetition separation,14855 closed-deficit return words,106 repeated return words,3132 repeated fixed cut/label/side downcross pairs. No adjacent identical return observed. Diagnostic ranges use exact integer horizon counts, prime-factor table and exact BigInt support products; the branching formula uses small integer log computations. Reconstructed the previous canonical p79 followed by31/7/41/13 word at three distinct CRT translates, one98-digit and two99-digit roots; 357 literal BigInt ticks,156 CRT prime-residue incidences; verified the expected identical four-label burst, d=158 at its start and the support-product congruence between starts. These are distinct roots, not repeated bursts on one ray. All assertions passed.

[Support repetition audit 85ba971](https://github.com/tara-sooo/A166944-Lean/blob/85ba9717e57aca9acd19302bd2fec24be4e23660/research/min_direct_word_support_repetition_audit.mjs), blob d540e24762ec5a4c55432d1cd113ef70cc5659c4. Exact remote readback. Run node research/min_direct_word_support_repetition_audit.mjs 12000. Same finite root and tick controls, with word lengths2/4/8 and equal-deficit/parity return words. 458673 word support-capacity tests,14652 repeated-word pairs including106 closed-return pairs,239304 exact support barrier incidences,70668 outside-event incidences and1314194 outside-gain units (overlapping sample intervals),11076 pairs spanning more than two support periods,34076 short outside-jump checks, maximum repetition separation multiplicity m0=45, maximum tested word support size12. Exact integer barrier enumeration and BigInt products, all assertions passed. Repeated occurrence intervals were checked separately, not treated as disjoint across different words. Neither audit measures an asymptotic macroscopic infinite-ray population.

No new Fourier exponent, no external novelty claim, no Lean kernel verification, no observed infinite ray or contradiction with finite twins. Main and sibling branches unchanged. Next investigate whether prior recovery matching forces enough time-dense high-label bursts, or obtain global budgets on varying-support returns without charging the same outside gain multiple times. Neither sparse-window assumptions nor these extra burst conditions follow from finite twins.
