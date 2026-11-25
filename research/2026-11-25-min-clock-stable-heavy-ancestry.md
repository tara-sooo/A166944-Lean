# Short-clock ordered ancestry stability and true-tick pair absorption

2026-11-25 JST. First checkpoint of the user-selected branch, based on a31a2f7872d58733177936e54c34070367a00a7c. Adapts the prime-source persistent ancestry argument at 7e53c0f869b45f3cf8ff2e865713b224e10da151 to ALL original odd roots and fractional short-clock occupations. Uses the true tick state of the latest base note, rather than only recorded post-event states. Paper deductions and finite diagnostics; no Lean compilation, no full energy bound.

## 1. Reference histories and ordered persistence

Let X be dyadic, N=X/2, B=ceil(sqrt(7X)), a=2B,H=4B. Original M odd in [X,2X), s=M+2,C0=2M-2,K=floor((7M-1)/4). Work for sufficiently large X that H+2B<=K-s for all sources. For bookkeeping only use the exact same deterministic MIN tick histories up to relative H+2B (or earlier twin terminal); this is not a restart, a change to the prime cap, or a claim of occupation after a twin. Natural late occupations still use [a,H). All full waits starting before H finish by this extended reference cutoff. Each non-twin horizon is occupied at integer ticks t in its half-open waiting interval; next state at t+1 is determined by (t,C). Reference includes only active non-twin ticks. The invariant C<=2t, monotone horizon growth and r(C)<=selected p imply total reference gain O(B) per root.

For M and a reference tick t, put n_M(t)=1+# {M'>M: same active physical tick state (t,C_M(t))}. Every such companion remains with M through the rest of M's reference trajectory: larger M' starts later and has no earlier absolute cutoff, deterministic successors agree, and a twin terminal cannot stop one earlier than the other. Thus n_M is nondecreasing. At s_M it is exactly 1, since no larger M' has started. This last observation requires NO primality assumption and does not exclude incoming *smaller* sources to composite roots. Define n_M(t)=1 before its start for the following difference calculation.

Let A(C) count all original reference tags visiting C, not a weighted occupation. Each tag visits C at most once as an interval. Since r<=p<=3(p-1)/2 for completed waits, and the last possibly incomplete wait contributes <=B, the reference budget satisfies
    R_A=sum_C r(C) A(C)=O(NB).                                     (1)
No uniform ancestor-mass bound is assumed.

## 2. Exact clock-window logarithmic budget

Put u=log B, D=max(1,floor(B/u^2)), eps=u^(-1/4). A focal tick of an active reference trajectory is unstable if log(n_M(t)/n_M(t-D))>eps. For any positive integer D and eps>0, telescoping and interchanging finite sums give
    eps * #unstable ticks of M
       <= sum_t [log n_M(t)-log n_M(t-D)]
       <= D log n_M(last active tick).
Each nonnegative log increment is counted at most D times, including initial and final boundary cases. Since n<=N,
    #unstable ticks across sources <= ND log N/eps
                         = O(NB/u^(3/4)) = o(XB).                (2)
Each integer tick of a natural wait contributes 1/2 to the linear r-weighted clock cost, even if a previous mask leaves only part of its wait. Thus (2) permits removal of unstable ticks from the HIGH late occupation with negligible linear loss. It also applies separately to full positive-drift occupations of waits starting before H. It is a bound on tick mass, not on removed quadratic energy. No gain-interval overshoot term B is needed, unlike a whole-event marking at this shorter D scale.

## 3. Relative absorption with arbitrary previous holes

Take any subset of natural ticks in each reference wait, including HIGH late only or all full positive-drift waits starting before H. The argument also works for fractional retention per tick in [0,1]. Write w_M(C)=retained tick mass/(2r(C)), U=sum_M w_M, E=sum_C r U^2. Always w<=1. Remove unstable retained ticks as in (2). At every horizon with U<zeta A(C), where zeta=u^(-1/8), remove the entire remaining occupation; this costs <=zeta R_A=o(XB) in linear budget by (1). Gate is applied AFTER previous holes and instability, or reapplied with fixed reference A if more masks are introduced. Do not claim it persists under arbitrary later deletion.

Define ordered offdiagonal energy of unordered pair M<M' at C by
    e=2r w_M w_M'.
Expand only the smaller tag's weight over its retained ticks t, so each unit tick contributes w_M'. Partition these products:
* OLD: the two actual reference histories share the physical state at t and t-D.
* RECENT: they share it at t but not at t-D.
* NOT-YET: they do not share it at t. Includes truly asynchronous trajectories as well as parts of waits preceding the first true meeting.
The diagonal is separate. This is an exact nonnegative partition; it is deliberately a partition of pair-tick contributions, not necessarily a whole-pair mask. The larger partner may have a different retained age interval; its w_M' is the full retained weight at that C and need not contain tick t.

For a stable focal tick the total number of larger companions that have newly joined since t-D is at most
    n_M(t)-n_M(t-D) <= (1-exp(-eps)) n_M(t)
                    <= (1-exp(-eps)) A(C).
Their sum of partner weights is no larger, since w_M'<=1. Sum over focal ticks, then use the density gate:
    E_recent(C) <= 2(1-exp(-eps)) r(C) U(C) A(C)
                <= beta r(C) U(C)^2,
    beta=2(1-exp(-eps))/zeta=O(u^(-1/8)).
Therefore
    E_recent <= beta E.                                         (3)
No uniformity or prime-source density is used. This relative inequality holds on the actual retained occupation, including arbitrary prior holes and partial waits. It cannot be called an absolute o(XB u^3) energy estimate without a bound on E. OLD products share a true physical history for at least D ticks ending at their focal tick; they need not have shared the recorded pre-event vertex if the true meeting occurred inside a wait. The initial extension is a bookkeeping reference only; all charged weights remain inside their specified actual occupation.

If E_res denotes diagonal + OLD + NOT-YET (minus any independently bounded nonoverlapping pair products), then E <= (E_res+known paid terms)/(1-beta) eventually. In HIGH this is a contraction for the recent sector. MED LOW-destination amplification must still be accounted for: a generic o(XB) tick loss is not sufficient to delete natural MED weights. Do not silently apply these marks there.

## 4. Connection to true birth and remaining obstruction

The identical-tick definition agrees with the earlier true waiting-state birth analysis: for a same-positive-label recorded merger with predecessor horizon D0 and arrival times a0<b0, actual first meeting is (b0,D0), not the next recorded post-state. Thus the present classification can be applied before a recorded merger. In particular at the same recorded pre-state all actual ticks of the smaller root have a larger partner already present; NOT-YET does not occur for that pair. For two overlapping waits at the same C, their common end is forced by determinism (unless one is clipped at its own stop); NOT-YET for the smaller root is confined to the portion before the later arrival. If their arrival lag is <= L, such a pair contributes at most L to NOT-YET (unit ticks times w_M'<=1). The source separation of every supported pair is O(B), by C<=2t and the reference age bound; there are O(XB) such pairs. Hence all overlapping-wait precontact products of lag <= L=log^(5/2) B cost O(XB L)=o(XB log^3 B). This bound holds for both of the occupations above, with arbitrary holes, and does not address nonoverlapping waits or large lag. This last bound is a paper deduction, not separately measured by the audit.

The base true-birth inequality L_shared+K_paid<=24 E_+,off^full concerns NATURAL full positive-drift occupation. Equation (3) also applies to that type of occupation after the stated deletions, but a small LINEAR deletion can remove large full quadratic mass. Consequently (3) on a trimmed positive sector does NOT by itself bound L_shared+K_paid. A separate transfer for deleted contributions or a compatible debit ledger is necessary. The major remaining HIGH terms are OLD long-lived heavy groups, asynchronous/large-lag NOT-YET products, and the unmatched large birth debit. Need show that the oldest common state has controlled ancestor mass or that prolonged heavy histories force a previously payable clock/debit charge. No argument bounding all these terms is available yet. Keep the MED and HIGH sufficient scales of wide-low-transfer/local-partner-quotas unchanged.

## 5. Finite verification and controls

Standalone ECMAScript audit: research/min_clock_stable_heavy_ancestry_audit.mjs, commit 2832c4eb4196df6a5789abf1d14d39b2ff2a8375, exact readback blob 261a811c6b691f45d00c55b4f5c9078bcf487781. Run from repo root:
    node research/min_clock_stable_heavy_ancestry_audit.mjs 256 1024 4096 16384

Actual audit function executed in available JS runtime (not a separate local Node run), 16 runs = four X, two occupation types, two parameter modes. Literal per-tick parity GCD with smallest-factor table, actual individual cutoff and twin stop. Descending source enumeration gives exact larger companion count at every active tick. Checks monotone counts, initial count 1, per-tag and global Fubini bounds, linear density and mask loss, independent pair-product classification using binary search of first common tick (with literal tick scan for all overlapping tested pairs at small X and up to 64 at larger X), partition and per-horizon relative inequality. Stress mode uses eps=1/8,zeta=1/2 and deterministic every-seventh-tick holes, not asymptotic choices. Floating point tolerance for logs and weighted energies. At X=256 the original cutoff clips the extended reference, so full mode counts only completed positive waits; eventual scale gate not claimed there.

Largest X=16384, B=339, N=8192,D=9:
| occupation/mode | raw ticks | gate deleted ticks | kept ticks | retained E | RECENT | OLD | NOT-YET |
|---|---:|---:|---:|---:|---:|---:|---:|
| late HIGH analytic |126343|122195|4140|41160.52|0|39166.54|0|
| late HIGH stress |126343|80350|28252|498460.14|0|488401.45|0|
| full positive analytic |1489385|1282758|142204|4376416.42|9115.78|3393283.03|907189.06|
| full positive stress |1489385|563784|590334|10583784.29|13443.23|7677964.92|2697545.84|

The diagonal is the remaining energy in each row. Global reference unstable ticks 106155 analytic, 228475 stress. Largest full-positive stress: 1011597 pair-horizon terms and 64 independent first-meeting scans. At X1024 full-positive stress, 4243 independent scans. All late HIGH recent terms in these 16 tests are zero, so the recent class is nonvacuous only in the full-positive diagnostics. Analytic beta is not yet a small contraction at these finite sizes. Large density losses in finite runs, particularly late HIGH, are explicitly not an empirical little-o result. No finite residual is a cumulative combination of earlier branch masks, and neither these diagnostics nor the new paper inequalities prove the twin-prime conjecture.

## 6. Next mathematical task

Use the exact OLD pair-tick set to charge the long common heavy histories by their earliest common tick or the deficit minimum over the shared segment. Seek a relative contraction of the positive ascent term or a bound on source-weighted old ancestry at that earlier cut. Compare with long-lag NOT-YET products using the true-birth sieve and prior actual partner quotas. Keep all linear loss, absolute quadratic payments and relative E terms in separate ledgers. Then integrate with the natural MED destination transfer. Main unchanged; no Lean compilation or final theorem claimed.
