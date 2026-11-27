# Negative MIN: age frontier and minority-mass merge entropy

2026-11-27 JST. Continuation of [5e932c4](https://github.com/tara-sooo/A166944-Lean/commit/5e932c408a237debff6fa3672088dc652ebde830). The goal is unconditional twin infinitude, independent verification and Lean formalization. This note treats the full synchronized root population, not selected low-gain trajectories. Unlike the spatial factor-gap code, it charges only actual coalescence, and gives an elapsed-age partition without paying for asynchronous cut clocks. Paper deductions; no asymptotic collision estimate or Lean kernel proof yet.

## 1. Actual merger forest

Use the synchronized windows and Negative MIN clocks of 1d0e2c5 and 5e932c4. For root A, birth b(A)=3-A/2, elapsed age n-b(A), position x and postheight h=n+x/2>=0. Gain A-x=2(age+3-h)>=0. Canonical roots are spaced by 6. At each absolute tick in one window, partition roots born so far by their actual post-tick position. Each occupied component has mass m, and deterministic future at that absolute clock. At a target x there is at most one idle predecessor, a birth of mass 1 (if applicable), and one moving predecessor x+p-1 for each actual winning prime p. A component never splits. Let f(m)=m log m, f(0)=0, Phi(a,b)=f(a+b)-f(a)-f(b), g(b)=Phi(1,b).

For each merger node the entropy increment is f(sum m_i)-sum f(m_i), including births as unit groups. Sum over all windows from first birth through retirement: cancellation gives N H(A|Y,J), where J is the window. The uniform spatial gain cap gives H(A|Y)<=H(A|Y,J)+log B0, B0=O(1). This is the all-root version of the actual physical block ledger of 589743f, now partitioned by age.

## 2. Age frontier without recording individual clocks

Fix integer 1<=u<=T. At each tick classify an incoming component as young when ALL of its roots had elapsed age <u at the preceding tick; births at this tick are young. Otherwise call it old. Equivalently use the largest root in the component. Old status is permanent after first attained, since age increases and roots never separate. Split the node into young groups and old groups, with total masses Y_v,O_v respectively. The exact entropy increment equals
    E_y(v)+Phi(Y_v,O_v)+E_o(v),
    E_y(v)=f(Y_v)-sum_y f(m_i),
    E_o(v)=f(O_v)-sum_o f(m_i).
For every young root arriving at x at time n, its current age is <=u. Thus A lies in [x,x+2u+6], and Y_v<=M_u=1+floor((2u+6)/6). Any young group also implies h<=u+3.

For each root charge its young internal contribution log(Y_v/m_i) while its incoming group is young. These increments telescope along that root's chain of young groups: if a node has no old groups, the outgoing component has mass Y_v; otherwise it becomes old permanently, and the telescoping stops at the young subaggregate. The last young subaggregate has mass <=M_u. Hence sum_v E_y(v)/N<=log M_u. This bound does not require synchronizing each root's age-u cut or encoding a cut clock. All roots join the old population at most once, either by reaching age u or by entering a component that already has an old predecessor. All are old by retirement, since u<=T.

Write lambda_u=N^-1 sum_{mixed v}Y_v<=1 and V_u=N^-1 sum_{mixed v}O_v. Both sums include only nodes with positive Y_v,O_v. By concavity and homogeneity of Phi (the log-sum inequality),
    N^-1 sum_v Phi(Y_v,O_v) <= Phi(lambda_u,V_u) <= g(V_u).
Define D_u=N^-1 sum_v E_o(v). Thus
    H(A|Y) <= log B0 + log M_u + Phi(lambda_u,V_u) + D_u.   (1)
Only actual young/old contacts enter V_u, not all stationary ticks. One root's old side at such a contact contributes once at that node. Since h<=u+3 there, V_u is bounded by the mean old occupation at heights <=u+3 (including the full birth-to-retirement interval). This coarse occupation cap is often substantially weaker than V_u itself.

Every moving young group has p-1<=2u+6 by its total age gain. For a moving old group at a mixed node, even arrival n gives p|h, odd n gives p|h-3: even n is 0 mod 2p and x=0 mod p; odd n is p+2 mod 2p and x=2 mod p. If p>u+3, the only possible mixed-node arrival heights are h=0 (even) or h=3 (odd). At h=0 the old or young idle predecessor is impossible since its previous height would be -1. Large-label old-to-young contact is therefore localized to the two reset heights, rather than being an arbitrary late high-label event. This does not exclude high-label contacts at resets.

## 3. Actual minority-mass bound for the remaining old/old entropy

At a node with k>=2 old incoming groups let b be the maximum incoming old mass and a the total remaining old mass (ties arbitrary). The entropy within the minority is at most a log(k-1), so
    E_o(v)<=Phi(a,b)+a log(k-1).
Set A_u=N^-1 sum a, B_u=N^-1 sum b, rho_u=N^-1 sum a log(k-1), summing ONLY nodes with k>=2. Then
    D_u<=Phi(A_u,B_u)+rho_u.                              (2)
The quantities A_u and B_u are mean actual minority and majority collision incidences along roots, not event counts or number of reverse words. Purely binary mergers contribute zero to rho. The same inequality applies to the low-only old submix. An incoming component belongs to a single prime label (or idle), so away from degenerate height the moving candidate count is at most omega(|h-c|), c=0 or 3 according to parity, and at every height at most omega(x) or omega(x-2). If k>=3, at least two moving prime labels are present; off the degenerate height their product divides the height factor. In particular rho_u <= C_u(loglog R+O(1)), where C_u is the normalized minority mass at nodes with k>=3. No estimate of C_u at growing R is claimed.

Combining (1),(2) and the outgoing-label penalty Q_R in 5e932c4 gives a new sufficient condition, with no event-count hypothesis:
    liminf [log M_u + Phi(lambda_u,V_u) + Phi(A_u,B_u)
                     + rho_u + Q_R]/loglog R < 3.           (3)
All the collision variables are taken on the actual all-root ensemble, not a CRT model. For u=floor(log R), log M_u<=loglog R+O(1). A useful subcase would be V_u=(log R)^{o(1)}, A_u=O(1), B_u=(log R)^{o(1)}, rho_u=o(loglog R). These imply H(A|Y)<=(1+o(1))loglog R. For this implication use Phi(a,b)<=a[1+log(1+b/a)] with the zero-mass case by continuity; uniformly for bounded a, the right side is <=a log(1+b)+O(1). With the existing time criterion, it then suffices on the same unbounded slabs to have limsup(2 sigma_rep,R-theta_R)<1. None of those actual asymptotics has yet been proved. More generally the exact combined expression (3) allows the costs to trade off; do not require each to be subleading.

## 4. Localize the old/old obstruction further

For an old/old node split old predecessors into high p>u+3 and low p<=u+3, treating idle as low. Its E_o decomposes exactly into high internal entropy, low internal entropy and Phi(high mass,low mass). Apply (2) separately to the low submix; apply the same log-sum argument to mixed high/low nodes if bounding high arrivals and competing low exposure. This partition uses the full actual ensemble: deleting high labels from a simulation would change which low events merge and is not justified.

At R=2e6, u=14, the largest old/old cost is low internal (1.5980895), compared to high internal .0429412 and high/low binary .3460965. At u=55 the costs are 1.1566134, .0103789 and .1210463. Thus the next mathematical target is actual low-label collision incidence, including resident mass at incoming low clocks, and young-contact exposure. The rank term is empirically negligible; high factor-rank decoding of every event is not a good proxy for entropy. This is a diagnostic priority, not a proof that high costs are asymptotically negligible.

## 5. Audit and scope

[Audit source 20258f5](https://github.com/tara-sooo/A166944-Lean/blob/20258f50bb0ffeb929a45606758958ba844717e4/research/min_local_negative_age_frontier_audit.mjs), blob c0fee3fc1ec06372e6711f76131d05fe9ceddcb7. Reproduce with node research/min_local_negative_age_frontier_audit.mjs 12000 48000 192000 480000 1000000 2000000. Executed actual ECMAScript function before commit and re-executed exact remote readback. Event-driven merging simulation on synchronized windows, with independent per-root trajectory replay of the endpoint multiplicities (same prime-factor clock implementation); no independent analytic review, Node process or Lean kernel run. Checks exact height pins, age gain, young mass cap, permanence via aggregate maxA, entropy partition, log-sum and minority bounds, old contact low-height restriction, endpoint mass equality, and high old arrivals into young only at reset heights. Counts:
    roots 622004
    occupied-component jumps 2110844
    merger nodes 555743
    counted structural checks 4336567
    (additional local assertions not in the final count)
For R=2000000, N=333333, L_end=3.98901644, H(A|Y,J)=3.57735857.
    u    E_y/N     mixed/N    D_u        lambda      V_u         A_u        B_u        rho_u
    1    0         .987570    2.589789   .431202     2.496434    1.197454   4.803992   .0327351
    14   .453372   1.136860   1.987127   .448224     3.211104    .917377    3.629827   .0084200
    55   1.195877  1.093443   1.288039   .409242     3.526162    .607648    2.234132   .0022850
    210  2.109616  .789212    .678530   .318075     2.673651    .321072    1.197766   .0002579
At u=14, Phi(lambda,V)=1.3607336, minority bound 2.2948104, early cap log 6=1.7917595. The exact costs are smaller than these estimates; do not treat the coarse upper bound as satisfying (3) at finite R. The actual low-height occupation bound for V is 57.473484, much larger than the actual 3.211104. Counting all low-height ticks alone discards important sparsity. The remaining asymptotic problem is to prove a sufficiently small bound on actual collision exposure and minority/majority incidences, and combine it with repeat/terminal occupation. Twin infinitude remains open; no Lean formalization or changes to main/sibling branches.