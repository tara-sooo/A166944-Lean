# Negative MIN: local pair-energy envelopes and exact good-phase occupation

2026-11-28 JST, Issue #10, parent #1. Continue from 14f5f5841793be7ce6b1a02ffda330c1dd1ff111, verified 562-declaration core 396b66c373e05c9e52d7239eed282ef713c7a3df. Goal remains unbounded twin primes for the actual negative MIN clock, not the stronger A166944 parent record conjecture. No unconditional asymptotic lower bound established.

## 1. Exact local reverse joint charge (kernel checked)

Let C_J(w) be the joint reset-block count from the previous note; P(B) is the 0/1 score of a reset-free block B (broad count >K AND narrow distinct count >Ddiv). Let head(w) be the prefix before its first reset label >=Ystar. For p<Ystar,

    C_J(p::w)-C_J(w) = P(p::head(w))-P(head(w)).

For p>=Ystar the left side is zero. The latter is a separate case, NOT the formula obtained by substituting an empty head(p::w) in the former: when p itself resets, the entire following head remains counted. The first Lean attempt at a universal formula exposed this mismatch and the statement was corrected, rather than making an unjustified equality. The final charge theorem has the intended unconditional positive-charge premise.

If the decrement is positive, p<Ystar and at least one of:
    z<p<Yb and broad(head(w))=K;
    z<p<Y0 and distinct_narrow(head(w))=Ddiv and p is absent from head(w).
The other threshold must be satisfied after adding p. The distinct-count recurrence adds exactly one iff the new label passes its filter and did not previously occur. Thus this is a genuine last-use pin, not merely a high count. Kernel: resetBlockScan_head_difference, resetBlockCost_cons_reset, jointWordCount_cons_exact, distinctFilteredCount_cons, jointBlockScore_cons_threshold, jointWordCount_cons_charge.

## 2. Local envelopes for record pair-energy

The preceding bounded-defect potential gives |F_A(k)-G_A(k)|<=E=wS+wL for all prefix net values, where F_A is additive potential net and G_A is the original history net. For any sequences f,g uniformly E-close on prefixes through k, their running peaks are E-close and their reflected debts are 2E-close. If two additive trajectories meet at their respective ages a,b, their remaining relative suffix net is identical. Let H(k) be the maximum LOCAL suffix net using C(word of the suffix) starting fresh, not a global terminal potential; by bounded defect the additive suffix peak differs by <=E. Let d=max(history debts of A,B at contact). Then the exact additive pair record overlap W satisfies

    max(0,H(k)-d-3E) <= W <= max(0,H(k)-d+3E).

Also W<=D*k. This holds at first observed contact, including already-coalesced roots at u=0. The two prefix approximations and the local suffix approximation are distinct: no independence assumption. Generic kernel lemmas PrefixClose, runningPeak_close, recordDebt_close, common_suffix_pair_profit_local_upper/lower combine with the prior actual_contact_pair_profit and wordPotential_prefix_bounds.

A sharper second paper envelope uses each root's actual history peak at contact and at retirement. Put r_A=P_hist,A(end)-P_hist,A(contact), similarly r_B. By identical additive suffix increments after contact, the smaller additive debt gives weakly larger record increments throughout; hence W=min(P_add,A(end)-P_add,A(contact),P_add,B(end)-P_add,B(contact)). Uniform peak stability gives

    |W-min(r_A,r_B)|<=2E.

Intersect both envelopes and [0,D*k]. They allow evaluation of the exact additive Q within local bounds without simulating beyond observation end, even if the common terminal clock defining the potential is much later. Sum over actual ordered contact pairs, including diagonals. Do not discard the error per pair: the uniform NE optimal-value error does NOT imply a uniform NE bound for Q. The error may be much larger than the required polylogarithmic moment bound if raw collision counts are high. This motivates the next alternative representation.

## 3. Mixed finite support and long reverse tails

For an actual even-state segment of length k, suppose regular alphabet S has uniform gain bound B and there are j nonzero exceptional labels outside S, each <=P. Split at these j firings. There are j+1 regular segments, giving

    gain <= (j+1) B + j P.

If S is finite and every label <=Ystar, the prior finite-support event theorem gives B=finiteSupportLimit(|S|)*Ystar. The proof does not enumerate the exceptional labels' order. Moreover any actual segment ending immediately after a nonidle firing, starting from an arbitrary state, has k<=3*gain (decompose at its first event and induct, using the actual first-event wait theorem). This DOES NOT bound arbitrary idle tails with no next firing in the prefix. Kernel: gain_evolve_add, finiteSupport_gain_bound, mixedSupport_gain, completed_segment_wait_bound.

Apply to a reverse charge whose reset-free tail after p is Bword. Let s0 be the number of possible nonzero base labels <=z; h fixed. If the broad threshold is exact, there are K exceptional broad occurrences and regular labels consist of base and the medium labels >=Yb (all <Ystar). If there are at most h distinct such medium labels, the gain of the whole tail is <=(K+1) finiteSupportLimit(s0+h)*Ystar + K*Yb. If instead the novel-narrow threshold is exact and at most h distinct labels in [Y0,Ystar) occur, the regular support has size at most s0+Ddiv+h, and gain <=finiteSupportLimit(s0+Ddiv+h)*Ystar. These bounds apply to every initial segment of that tail; no restriction on repeats. Thus whenever the completed gain exceeds the applicable bound, the tail must contain more than h distinct medium labels. If the time to the last firing exceeds three times the bound the same conclusion holds. This is an actual deterministic arithmetic alternative, even if there is a long final idle interval. In a future CRT scan use the first h distinct medium pins, not a full word enumeration. No sieve estimate on their occurrence frequencies is claimed here. At current z,Ddiv, B_support=L^o(1), K polylogarithmic; for fixed h these gain bounds are subexponential in L (far below T), but can still be far larger than a desired short observation cutoff.

## 4. A direct good-phase field, removing all history debt from the lower target

This section is a paper transfer of the prior, still unreviewed uniform upper-sieve estimates, NOT an independently established analytic upper bound. The finite optimization itself is kernel checked.

Use exactly the high/medium scans of the quantitative support note at 943848e0467c77bfa931c90379e97a3812837dec: L=log R, T~sqrt R exp(-L^.5), M~L^2.1, Pmax=T exp(-L^.6), Y0=exp(L^.1), Yb=exp(L^.45), Y1=exp(L^.85), Ystar=Y1/(2(B_support+1)), U=L^3, fixed h=12 (or larger as appropriate). Integer roundings and sufficiently large R are understood. J is the joint counter with reset Ystar; N_c is the low nonempty chunk counter reset Y0.

For each observation bin (u,Jwindow,x), follow its deterministic future until its own window retirement. The next firing label p, if it exists, and the tail after that firing are uniquely determined by this bin, irrespective of its ancestor. Within a stationary phase at x with common next firing time, all ticks have the same flag. Classify the ticks as:

* bad low: next firing p<Y0;
* bad medium: Y0<=p<Y1, and the forward medium scan from its completed source stops at first narrow z<r<Y0, a big label >=UY1, or retirement. Good medium iff it stops at a fast NEW high label or the h-th distinct slow new high label (use the exact scan stop priority and waits from the postsource state);
* bad high: Y1<=p<Pmax and the full following reset-free block before the next >=Ystar event or retirement has joint score 1. Good high iff this score is 0;
* good near-max: p>=Pmax;
* good terminal: no firing before retirement.

The phase flag only needs the future from that state through retirement, not any pre-observation charges or history. Window ID is part of the bin. In particular a terminal proxy phase is not by definition a twin; terminal non-twin occupancy is one of the prior analytic upper-sieve obligations. Good phase classification is not meant to assert that a root has paid no previous cost.

### 4a. Deterministic transfer of bad occupation to old counters

For any prefix policy d, even uncapped, let B_A be the observed bad ticks of one root before death. Write G_A for completed total gain before death (<=3T+6 on canonical roots). Let J_A,N_A be the two counters through that completed prefix including pre-observation history. Take B=B_support large enough to cover the intermediate support lengths in both old scans, Qz positive even base primorial (Qz<=Y0 for large R).

Each completed bad high source belongs to its own following large block. If the block score has become one by prefix end it is counted in J_A. Otherwise at most ONE such completed source can have its qualifying block still incomplete. One final partial high phase can add at most 3Pmax more ticks. Every completed/partial phase with its next firing within the full window has full wait from birth or previous firing <=3(p-1). Thus
    B_high <= 3 Pmax (J_A+2).

For bad medium completed sources whose full scan stop is within the selected prefix, at most B+1 sources can point to any one narrow or big stop (the intermediate support bound limits their event-index distance). A first narrow stop is the first narrow after the last high, hence begins a nonempty low block, counted by N_A. Big stops <=G_A/(UY1-1) by gain. A completed source whose scan ends after prefix or reaches retirement can only be among the final B+1 firing indices, because before any stop the allowed support has at most the prescribed fixed number of high labels plus the base. The final partial medium phase has length <=3Y1. Thus
    B_med <= 3 Y1 (B+1) (N_A+G_A/(UY1-1)+1)+3Y1.

Completed low labels are split at resets >=Y0 and saturations, as before. Each nonempty chunk has gain <=B Y0; empty base-only chunks gain <Qz. Their number <=1+G_A/(Y0-1)+N_A, since reset count <=G_A/(Y0-1). One final partial low phase costs <=3Y0. Hence
    B_low <= 3 B Y0 N_A + 3 Qz (1+G_A/(Y0-1)+N_A)+3Y0.

Sum all three. These are deterministic completed/partial-phase inequalities (use observed time <=full phase time); they do not use the cap or sieve. The cost of the actual selected prefix includes all pre-observation labels, so using J_A,N_A does not omit them. For sufficiently large R, choose the constant C in the old history expense large enough (fixed independent of R) and scale weights with reward D:
    wS >= 3D Pmax,
    wL >= 3D [(B+1)Y1+B Y0+Qz].
Then
    D * badObservedTicks(d) <= historyExpense(d)+ err_det,
    err_det/(DNT) = O(Pmax/T+(B+1)Y1/T+(B+1)/U+Qz/Y0+Qz/T)
                  = o(L^(-.25)).
Rounding weights upward and the fixed constant can be absorbed in the old cost normalization. This paper implication is stronger than simply approximating the history cost by a future potential, since the bad field has a nonnegative complementary reward and no pre-observation debt. It is not claimed for the tiny proxy weights wS=2,wL=1 in the audit.

### 4b. Uniform good occupation estimate, conditional on the old analytic argument

For a capped selected prefix, every good high source with completed forward scan cannot have both old bad abort conditions in its selected prefix (they imply joint score one in its full block); if the full block score is zero, at least one old scan can be counted by its good sieve case. The last incomplete source/scan contributes the same Pmax/T tail remainder. Good medium sources have one of the two old good scan stops; if that future stop is beyond selected death, charge the bounded support tail or directly count their full-future witness at the source state (cap needed only at source phase). Nonrough high/medium phases contribute negligible time by the wait-vs-gain lemma. The old near-max and terminal estimates handle the good near-max and good terminal categories; unfinished phases of a selected prefix are included in the prior partial/terminal error bookkeeping. Thus, *provided the earlier six-/multi-form upper-sieve, terminal and window-normalization bounds are valid in their stated uniform form*, their same argument yields

    goodObservedTicks(d) <= B0 M T twinCount + o(NT L^(-.25))

uniformly for full-capped d. No good-occupation lower bound follows from this upper estimate. A rigorous independent audit of the analytic upper sieve including the transfer of partial phases remains required. The distinction between future witness counted at source and a selected-prefix event is explicit here.

### 4c. Exact finite optimization (kernel checked)

For ANY nonnegative field w(b) on observation bins, define m_b=fullObsFiber length. The full-horizon deadline d(A)=observeAge(A)+T and exact deadlineClip simultaneously attain min(M,m_b) live roots at EVERY observed bin and remain FullCapped before observation. Therefore

    max_(FullCapped d) sum_b w(b) liveMass_d(b)
      = sum_b w(b) min(M,m_b).

No choice of history, future potential, debt, stopping profit, or flow optimization is needed. Kernel: fullDeadline_obsFiber, deadlineClip_obsFiber_exact, fullDeadline_field_exact, binFieldMass_upper, fullDeadline_field_optimal, good_bad_field_partition, goodField_dominates_history. For w=D*1_good, call the unscaled clipped mass G_M. Section 4a implies V_history^*/D <= G_M+err_det/D, so under the stated constants this lower target is no stronger than the old net target, up to the explicit negligible error. The reverse comparison is not asserted. The generic conditional twin bridge is GoodFieldEstimate, goodField_upper, twin_above_of_goodField: if the uniform good field estimate holds and D G_M>err with Btarget+3T+6<R then a TwinCenter above Btarget exists.

The new arithmetic target is simply G_M/(NT)>=c L^(-.25) along unbounded R (under 4b). No requirement of cheap entire histories. If S_G=sum_good m_b,Q_G=sum_good m_b^2, then prior exact clip_sharp gives G_M>= M S_G^2/((M-1)S_G+Q_G). The first and second moments now count raw roots ONLY at good bins, not record increments or debt. In particular one can search for a population of occupied good physical phases with sufficiently long waits and modest actual arrivals. This is an alternative lower-bound approach, not a proof of such a population.

## 5. Exact stationary-phase arrival integrals

For each window/site/common-next-firing phase (terminal retirement if no next event), let t_end be its last observed tick (pre-firing, inclusive), and list all canonical roots arriving in that phase by their first observed time a_i (clamp pre-observation arrivals to observation start). Positions only decrease and no outgoing event occurs before t_end, hence roots cannot leave that phase before its end in the FULL trajectory. A phase is allowed to begin empty; a later arrival at the same site after a previous firing defines a new phase.

Let d_i=t_end-a_i+1, order arrival times increasingly. Then
    integral m = sum_i d_i,
    integral min(M,m) = sum_{i<=min(M,n)} d_i,
    integral m^2 = sum_{i,j} min(d_i,d_j).

The earliest M arrivals are used as an integral identity, not a new independently chosen feasible policy at each phase; feasibility of simultaneous clipping follows from the full deadline theorem. The good flag is constant within each phase, so restrict to good phases in all three sums. This reduces the actual arithmetic task to first-arrival order statistics, without per-tick simulation. A noninitial arrival at x comes from x+p'-1 and the verified height/spatial pins: at even arrival clock n, p'|x and p'|n; at odd n, p'|x-2 and p'|n-2. Thus p'>=5 cannot divide either neighbor x±1, and in particular is distinct from the next firing label at x. For odd p'=3, p'|x+1 can occur; do not discard that case. This exact arithmetic distinction suggests a CRT analysis of first M arrivals into a long rough stationary phase. It does not establish their density.

## 6. Independent finite tests

Source research/lean/negative_min_local_good_field_audit.mjs @e1f7767e614f569c9572c50646c6cf367064930d blob e26e073e9e71d71762f395985c49adf7fb7b8391. Reproduce with node research/lean/negative_min_local_good_field_audit.mjs. Exact ECMAScript execution and remote replay. 6,206,437 checks; 2,081 canonical roots in 159 deterministic sampled windows; 401,448 ticks (literal eligibility independently compared at R=600), 16,941 ordered contact pairs incl diagonals, 1,324 positive reverse charge tests, 1,231 mixed-support segmentation checks, 68,287 physical observation-bin mask checks, 3,503 phase integral comparisons. Every observed and pre-observation cap tested by explicit priority simulation; arbitrary random deadline prefixes checked for mask upper bound. Pair min of cumulative record increments agrees with full tick-by-tick overlap. Both local envelopes tested, not assumed.

Proxy z=3,Y0=13,Yb=23,Ystar=31,Y1=47,Pmax=max(48,floor(.75T)),K=2,Ddiv=1,h=2,U=4,wS=2,wL=1,reward D=1. These do NOT satisfy the growing-scale assumptions or deterministic history domination weights. At R=192000,T=288,M=16,N_sample=720, actual record energy/(NT)=11.18558, combined local envelope [10.92152,11.33810], raw energy=11.42018. All contact pair weights positive in this light-cost audit (no evidence of strong debt-based exclusion). Good phase clipped mass/(NT):
    R          T      M      all good     interior good    near-max     terminal
    600        18     1      .340484      .004950          0            .335534
    2400       36     2      .431389      .007963          .053149      .370278
    12000      72     4      .544358      .029774          .072425      .442159
    48000      144    8      .578602      .140090          .094242      .344271
    192000     288    16     .733743      .058078          .070375      .605290
At the largest scale, most good mass is unfinished terminal phases, not verified twins. The interior good fraction falls between the last two configurations; no monotonicity or asymptotic extrapolation. Exact first-M arrival formula reconstructs all three quantities (raw mass, cap integral, raw energy) including good-only restriction.

## 7. Status

Final CI and source details appended after exact verification. No literature novelty claim, no new public web search, no independent human review. Main and sibling branches unchanged. Next actual arithmetic work: use the stationary phase decomposition and distinct incoming/next-prime pins to study first-arrival distribution in good high/medium phases, and the terminal non-twin bound. Need growing-scale lower of G_M or the earlier record moment criterion, independent audit/formalization of uniform good upper and Mathlib bridge. Issue #10 remains open.

### Verification checkpoint

Confirmed green core 62ab609ee757fe18b76edb5d9f52aeedd6073b99 (blob 30a6632e23ba6d95bb627a57522f8f849c7a9f42), 10,116 lines, 592 theorem declarations (+30), [CI 46053619071](https://github.com/tara-sooo/A166944-Lean/actions/runs/46053619071), pinned standalone Lean v4.33.1. All selected new axiom dependencies are subsets of propext, Classical.choice, Quot.sound, no forbidden declarations. Intermediate failed runs 46052775428,46052938709,46053276179,46053483993 fixed; canceled runs 46053152878,46053201762. The initial reset boundary equality was false and separated as explained in section 1; other corrections were elaboration/normalization. Exact remote readback inspected. Full project/Mathlib build not performed.

The four additional phase-integral theorem candidates (arrivalMass_sum, arrivalMass_clip, stationaryPhase_clip_integral, stationaryPhase_pair_integral) are at 570eb1213ed94ffd0992bcd78edfff8295cca164, blob ac354ab23ded89d91ca4278b8af038691f98df47 (596 declarations). CI 46053710911 was queued at checkpoint. Unless success and dependencies checked, count these as mathematical derivations and exact tested formulas with unverified Lean candidate code, NOT kernel-checked declarations. The 592-declaration pinned green version is the verified recovery point. Audit final exact remote replay succeeded with all 6,206,437 checks. No unconditional twin theorem.
