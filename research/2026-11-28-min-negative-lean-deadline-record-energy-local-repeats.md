# Negative MIN: exact deadline clipping, first-contact record energy, and local repeat budgets (2026-11-28 JST)

Continuation of c4204661641459617950d0db4ac4b5fe2d7306ed. Original target, physical cap, and weighted criterion unchanged. Final Lean core b55d4371092097686f924bf4f49c811261eba1c1 (blob 700a5527537081e71d5cffda7f7d98902d3763c0), CI run 46029932098 passed with pinned Lean v4.33.1, core only. 362 theorem declarations (49 more than 313 at 70180a4). Printed axiom dependencies of the new key theorems are subsets of propext, Classical.choice, Quot.sound; no sorry/admit/new axiom declaration. Earlier elaboration failures fixed. No new Mathlib downloads or full build.

## 1. Arbitrary individual history deadlines (kernel checked)

Let d(A) be any deadline age on the actual deterministic trajectory of A. It can be computed from the entire full trajectory, including a history-dependent counter; no state-additivity hypothesis on the counter. The priority key at physical time n is the absolute deadline birth(A)+prefixAge(d,A), later first, then the fixed root ID. Use the already verified payDeath policy with unit cost and individualized offset.

For every physical fiber including pre-observation birth times, the selected live count is exactly min(M,m), where m is the count of full roots alive under d in that fiber. The priority never reverses after contact, and a displaced root never returns before its deadline. The policy is FullCapped; each selected prefix age <= its original deadline prefix. Hence every monotone root-prefix expense remains <= its value at that deadline, even if different histories have different expense increments after coalescence. Maximum lifetime among policies respecting these deadlines is achieved, since every other such policy has count <= min(M,m) at each tick.

Verified deadlineClip_fullCapped, deadlineClip_prefix_le, deadlineClip_exact, deadlineClip_live_exact, deadlineClip_sharp_moment, deadlineClip_cost_le. For the list of deadline fiber masses, with S=sum m, Q=sum m^2, V=sum min(M,m), M>0,

    M S^2 <= V ((M-1) S + Q).

## 2. Record-energy moment, not raw endpoint moment (kernel checked)

Use the previously proved exact net optimizer, for any nonnegative state-dependent integer inc and reward D. Let g_A(n) be the nonnegative running-peak increment of that root (physicalProfit), between 0 and D. At an observation bin b and integer threshold 0<=t<D, put m(b,t)=# full roots in that physical fiber whose increment >t. Let S=sum_{b,t} m, Q=sum_{b,t} m^2, V=optimalRecordMass=sum_{b,t} min(M,m). Then

    M S^2 <= V ((M-1) S+Q).

The key theorem optimalNet_record_sharp is cross-multiplied and connected to the ORIGINAL exact policyNet, not a proposed proxy. Moreover, by counting the common thresholds of each ordered pair,

    Q=sum_b sum_{A,B in fullFiber(b)} min(g_A(b),g_B(b)),

including diagonals. Kernel checked threshold_square_pair, recordEnergy_pairs, recordMasses_sum. S is total full-root observation record increment; Q <= D times raw observation pair-ticks. This avoids charging the cap for overlaps in which at least one root has no positive record increment.

## 3. Exact first-contact pair contribution (kernel checked per pair)

For arbitrary integer sequences f,g at respective indices a,b with equal relative suffix increments, denote their running peaks by P_f,P_g and debts d_f=P_f(a)-f(a), d_g=P_g(b)-g(b). Write H(k)=max_{0<=i<=k}(f(a+i)-f(a)). The sequence with larger initial debt has weakly larger debt and weakly smaller record increment at every subsequent index, since the suffix increments are identical. Telescoping the smaller increments gives

    sum_{i<k} min(recordProfit_f(a+i),recordProfit_g(b+i))
         = max(0,H(k)-max(d_f,d_g)).

Verified peak_suffix, common_suffix_debt_order, common_suffix_profit_order, common_suffix_pair_profit, contact_netSuffix, actual_contact_pair_profit. The last specializes to actual MIN contact including equal window, equal physical state, possibly different birth clocks. The observation reward schedule and future state-dependent expense are common after contact.

Consequently, by finite regrouping of section 2 (paper corollary, audit verified), Q equals the sum over ordered root pairs in the same window of this formula at their FIRST OBSERVED contact, with k the remaining observation ticks. If no observed contact the contribution is zero. If contact precedes observation, start at observation beginning; diagonal pairs likewise. One need not examine every later tick. The debt of the more indebted root and the common future peak determine the entire pair weight. This is not a claim that debt is large enough to bound Q.

## 4. Localize narrow repeat expense simultaneously in time and space

At root A's age i, take physical grid cell of side H>0 with coordinates (floor((absoluteAge(birth)+i)/H),floor(x_i/H)). A root-specific monotone integer index equals time-cell advance plus space-cell decrease. Because clocks increase and positions weakly decrease, equal index means equal physical cell. For any prefix k, gain G<=2k+6 on even canonical roots. The index satisfies H*(index(k)+1)<=3k+6+3H; empty skipped indices are harmless.

In each cell pay its first occurrence of each label separately from repeated occurrences. The exact first+repeat partition gives K=K_first,box+K_repeat,box for original narrow count (z<p<Y0). Each cell uses at most Y0 possible narrow labels, so

    H*K_first,box <= Y0*(3k+6+3H).

A repeated label p>=5 in the same cell has both time difference <H and 2(p-1)<=spatial difference<H. The old repeat_forces_escape additionally forces an intervening label not dividing any chosen even modulus Q0<=p-1. Verified box_cost_partition, narrow_box_error, boxRepeatCost_mono, same_box_gap, same_box_repeat_gap. Monotonicity of repeat cost with prefix length does not assume common incremental costs after contact.

Define boxBudgetDeadline as the length of the initial run of affordable completed ticks, i.e. largest prefix <= horizon with local repeated count <= budget. Use exact deadlineClip. The resulting boxBudgetClip is FullCapped, has exact clipped live count and original narrow count bounded per root by

    H*K <= H*budget + Y0*(3*(observeAge(A)+T)+6+3H).

All statements checked, including no budget overshoot (boxBudgetDeadline_budget, boxBudgetClip_original_budget, boxBudgetClip_live_exact).

At the prior asymptotic parameters L=log R, T=floor(sqrt(2R+1)*exp(-L^0.5)), M=floor L^2.1, Y0=ceil exp(L^0.45), Y1=ceil exp(L^0.85), a_R=exp(-L^0.6)/(k_relay+1), choose
    H=ceil(T*exp(-L^0.6+2*L^0.45)).
The original canonical prefix age <=1.5T. Uniformly a_R*K_first,box=O(exp(-L^0.45)/(k_relay+1)), smaller than any negative power of L; multiplying by lambda=log L also harmless. This is a deterministic error reduction, not a CRT estimate at side length H, which is still R^(1/2-o(1)).
Take budget=floor(L^(-0.30)/a_R). Then the policy's normalized original narrow cost <=L^(-0.30)+super-polylog-small error. The preceding paper's medium elimination yields C_Q=o(L^-0.25), using its nonformal analytic estimates. Thus it suffices to prove normalized clipped deadline lifetime >=c L^-0.25 on unbounded slabs. This is an explicit policy with its original expense controlled; its lifetime lower bound remains open.

## 5. Separated support for arbitrary segments (kernel checked)

Generalized canonical repeat-gap lemma to any even actual starting state. SupportGainBound(S,B) means EVERY actual segment with all nonzero labels in S has gain <=B. For even Q0>0, the divisor support of Q0 has bound Q0-1 by the verified wall.

If SupportGainBound(S,B), p>=5 and B<p-1, inserting p gives at most one occurrence of p in any segment with support in S union {p}: otherwise take two consecutive p occurrences; their intermediate segment uses only S, yet its gain >=p-1. The old support before and after the unique p occurrence each costs <=B. Thus

    SupportGainBound(S union {p}, 2B+p-1).

Verified evolve_repeat_gap, evolve_repeat_relay, support_insert_once, separated_support_insert. This formalizes and generalizes the separated support idea in sibling 26ad4eab14f0ab0862c9d0313a26a625488a4f44 (no claim of new literature result). For a separated chain p1>=8Q0+12, p_j>=8p_{j-1}, the recursion yields B_j<=(4/3) p_j by induction (2*(4/3)/8=1/3), so if p_j<Y0 the gain is O(Y0). A maximal run within such a fixed support has at most O(Y0/max(1,z)) charged narrow events (for z>=1, each charge has gain >=z). Runs separated by outside firings contribute at most O(Y0/z)*(1+number of outside firings), plus narrow firings outside the support. This bounds repeat expense in such runs, but there is currently no adequate bound on the number of outside firings for all cheap trajectories. A naive global gain bound O(T/z) is still exponentially too large relative to the subexponential budget. No unrestricted repeat-density estimate follows.

## 6. Two explicit sufficient moment targets (paper consequences)

Normalize the record moments by DNT: s=S/(DNT), q=Q/(DNT), v=V/(DNT). Then v>=M*s^2/((M-1)*s+q). For the original boosted narrow cost from c420466 with lambda=log L, D=ceil L^2, the preceding analytic upper estimate would imply v=o(L^-0.25) if twins were finite. Conversely, for any fixed 0<=tau<=0.25, the following on unbounded slabs suffice:

    s >= c L^(-tau),   q <= C L^(2.35-2*tau).

Indeed v>= (1/2) min(s, M*s^2/q) (when q>0), and both terms >= constant times L^-0.25. This would imply >> R/L^2.35 twin centers along those slabs using the prior weighted estimate and medium elimination. A weaker lower bound s>=c/(log L)^2 and q<=L^(2.35-eps) for fixed eps>0 also suffice. If finite twins and the earlier analytic upper estimates hold, with s>=c L^-tau, tau<.25, then q/(s^2 L^2.35) tends to infinity along those slabs. This follows from q>=M*s^2/v-(M-1)*s, since (M-1)*s/(s^2 L^2.35)=O(L^(-.25+tau)). Neither the required positive growing-scale record mass nor the record energy upper bound has been established.

The alternative deadline policy uses D=1 in the pure lifetime moment inequality of section 1, with deadline chosen via box-local repeat budget of section 4. It also suffices to prove s_live>=c L^-tau and q_live<=C L^(2.35-2*tau), where s_live,q_live normalize the deadline masses by NT. These two routes must not be conflated: pure deadline moments count all affordable alive ticks, record moments count peak increments of the original additive boosted objective. The original state-additive optimality theorem is not applied to box-history-dependent repeat increments.

## 7. Independent finite audit

research/lean/negative_min_deadline_record_box_audit.mjs at 2b054d22c56202206c065fb26a3e4f2167d030e3 (blob b338d7c8e9b546586cfbfe01b08198e5bdaa9f73). Executed in ECMAScript runtime before commit and from exact remote readback, matching results. Actual literal gcd-clock updates for R=12000,48000,192000, 42,003 canonical roots, 28,195,500 ticks, 775,263 firings, 524,694 unordered contacts incl diagonals, 936,668 separated-support run checks, 108,668,397 total assertions (not independent samples). Parameters z=5,Y=47,H=floor(T/3) at least 32,D=3,w=13,M=8, repeat budget=3. For each physical tick, exact deadline clipping and no resurrection checked; prefix repeat costs bounded. Independent threshold sum, explicit pairwise overlap sum, and first-observed-contact future peak formula coincide. Sparse alphabets tested are {3,5} with sequential inserts 31,97,307. Actual repeat escape checked for p>=31 with Q0=30.

At R=192000 (N=32001,T=620), S/(DNT)=0.9496990853, Q/(DNT)=22.24614066, raw energy/(DNT)=23.59456136, V/(DNT)=0.4823138591. Narrow count 230554 = box first 194713 + box repeat 35841, global repeat 100596. Deadline count before cap 18785732 observed ticks, after cap 9804150. Fixed small parameter diagnostics, not actual asymptotic scales or proof of growing-scale inequalities.

## 8. Remaining obligations and status

The two exact moment routes now specify the analytic obstacle in terms of local repeats and genuinely profitable first-contact overlaps. Next attack should estimate actual long-window repeats (not just first uses or separation runs), and quantify first-contact weights by arithmetic of actual converging histories. For record energy, investigate whether post-contact future peak can be bounded when both prior histories incur expensive repeated labels; for the deadline route bound duration of histories with local repeat budget unexhausted and their contact moment. Independently review and formalize the prior WeightedEstimate and six-form sieve / normalization adapter. No unconditional twin-prime infinitude or quantitative twin count has been established; issue #10 remains open.
