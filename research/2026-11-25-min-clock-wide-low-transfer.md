# Wide primorial transfer: one natural non-LOW energy criterion at logarithmic cutoff

2026-11-25 JST. Continues 9bd21f843dfed06146d32fc1a91be8a98b631d85 (LOW transfer / two-scale criterion), a16e49ac73e59de5b649b03bbb260723dbd212ba (least-factor support and cubic-log clock target), and 99aa9dbc13e44b2949ece78b4177177f7fb6573b (selected-band linear marks). New: choose a second, substantially wider LOW primorial and use the polynomial saving of the least-factor support at intermediate destinations. This removes the separate small-event condition when the natural larger-sector energy is controlled. It also allows a cutoff of order log B (not merely loglog B or the earlier Z=log^{o(1)} B). It is a sufficient-condition improvement, not a bound on the actual larger-sector energy. Paper proof, no Lean compilation, twin infinitude OPEN.

## 1. Setup

Dyadic X, N=X/2 original odd M in [X,2X), B=ceil(sqrt(7X)), s=M+2, initial C0=2M-2, original K=floor((7M-1)/4), H=4B,a=2B. Assume H+2B<=min(K-s), eventually. Use full original canonical MIN prefixes through first post-event state at/beyond relative H, or twin terminal; no reruns. C strictly increases, t strictly increases, C<=2t, total gain <=G=2H+B+6. At selected prime p, positive least eligible r(C)<=p, wait<=2r(C)<=3(p-1), total selected weight per root <=1.5G. At unoccupied states w=0, at occupied pre-event horizon C, w_M(C)=clipped waiting duration in relative [a,H)/(2r(C)), 0<=w<=1. R_M=sum r w<=B, R=sum R_M, E=sum_C r(C)(sum_M w_M)^2. Under no twins R=NB. Reference can be any frozen subset of original roots; deleting o(X) original tags preserves R=(N-o(X))B. Earlier least-factor upper sieve gives for 2<=T<=B

    S(T)=sum_{0<r(C)<=T} r(C)=O(X T/log^3(2+T)),
    S(B)=O(X B/log^3 B).                              (1)

All sums use even horizons in [2X,7X). No assumption about trajectory distribution.

## 2. General primorial transfer, with two distinct thresholds

Let 2<=z<T<=B, let L_z=product_{p<=z}p (even), and write b=3L_z/2. LOW in this note means selected p<=z, MED means z<p<=T, HIGH means p>T (these are not the earlier medium/high thresholds). Let R_0,R_m,R_h denote original linear slab costs in those classes, E_m,E_h their natural projected energies, with fractional weights restricted to each class. E_m+E_h<=E_{>z}: the latter contains their cross term. All natural weights mean before any additional incidence deletion in that class.

Every maximal LOW-only block has gain <L_z by the even-primorial barrier: at an even multiple of L_z no odd p<=z divides either neighbor. A LOW jump starting below the next such multiple cannot strictly cross it, because its positive even distance to the multiple is congruent to +/-1 modulo the selected p and thus at least p-1. Landing on the multiple prevents further LOW jumps. The full elapsed time of the block is <3L_z; its clipped cost is <=b.

Assign each maximal LOW block to the next non-LOW selected event of the same original tag, if present. Delete:
- final unassigned LOW blocks, cost <=Nb;
- LOW blocks followed by p>T, at most O(B/T) per root by gain, cost O(N B L_z/T);
- remaining LOW occupation at relative ages in [H-m,H), m=3L_z+2T+2, cost <=Nm/2 (if trim empties slab this upper bound still holds).

For any retained positive LOW block cost the next non-LOW event has selected z<p<=T and its ENTIRE natural waiting interval lies inside the original slab: its pre-time is at/after the end of the contributing LOW wait, >=s+a, and its post-time is <=the contributing LOW start time+3L_z+2T <s+H. The next event belongs to the original full prefix. Its clipped cost equals half its integer positive wait, >=1/2. Each source's distinct LOW blocks map to distinct MED events. Hence

    R_0 <= 3L_z R_m + O(N[L_z+T+B L_z/T]),
    R_0+R_m <= (1+3L_z) sqrt(S(T) E_m)
                       + O(N[L_z+T+B L_z/T]).          (2)

Here the second inequality uses r<=p<=T on MED, so Cauchy R_m^2<=S(T)E_m. No uniform mass assumption and no distribution of actual waits is needed. In particular the bound can use a much larger L_z than the previous L_y=log^{o(1)}B, provided the right side still saves the required scale.

Let E_h,J be the projected energy of any retained subset of natural HIGH incidences, and let delta_h be its removed linear cost. Since retained R_h<=sqrt(S(B) E_h,J),

    R <= (1+3L_z) sqrt(S(T) E_m)
          + sqrt(S(B) E_h,J)
          + O(N[L_z+T+B L_z/T]) + delta_h.             (3)

This is a single explicit upper bound on the total original slab cost. It does not require the energy of LOW or its cross terms.

## 3. New one-sector sufficient condition and much wider cutoff

Take a function f(B)->infinity with f(B)=B^{o(1)} (for example max(1,loglog B)^(1/4)). Choose z to be the largest prime cutoff with

    L_z <= B^(1/3)/f(B),

and T=ceil(B^(1/3)). Eventually z>=3, T>z, and z=Theta(log B). The latter follows from the classical Chebyshev bounds theta(x)=sum_{p<=x}log p asymptotic order x, together with a prime between x and 2x for large x (Bertrand); alternatively PNT gives z~(1/3)log B. The proof does not need the prime number theorem. In particular z eventually exceeds the old Z=L_y^2=log^{o(1)} B in 9bd21f8. The floor/ceiling and finite small cutoffs are immaterial.

By (1) the MED support is O(X B^(1/3)/log^3 B). If just

    E_m=O(XB log^3 B),                                 (4)

then (2) implies

    R_0+R_m=O(XB/f(B)+X B^(2/3)+X B^(1/3))
           =o(XB).                                     (5)

Indeed the square root in (2) is O(XB^(2/3)), and L_z <= B^(1/3)/f. The deletion cost B L_z/T <= O(B/f). Constants are uniform for the displayed choice of thresholds. The X B^(2/3) term is a loose bound for the factor 1 times the square root. Thus the MED energy only needs a big-O bound at the cubic-log scale, while HIGH needs the little-o:

    E_m=O(XB log^3 B),
    E_h,J=o(XB log^3 B), delta_h=o(XB).                  (6)

Along unbounded dyadic windows, after o(X) entire reference-root deletion, (3)-(6) contradict the no-twin lower R=(N-o(X))B. Each resulting twin has smaller prime >=2X-1. Hence twin infinitude follows if (6) holds.

In particular a SINGLE sufficient condition is

    E_{>z}=o(XB log^3 B),  z=Theta(log B) as above.      (7)

Here E_{>z} uses all natural selected p>z; no independent LOW or earlier SMALL energy condition is required. For the earlier cutoff z=Z=L_y^2 with y=max(3,floor sqrt(loglog B)), log L_z<=z log z=log^{o(1)}B=o(log B), so L_z=B^{o(1)}. Thus the previous joint criterion (5a),(5b) in 9bd21f8 can be replaced by (7) at that old cutoff as well, with a considerably larger margin. This improves the criterion, not the existing upper bound on E_{>z}. In particular (7) is not known.

There is a sharper general tradeoff: if L_z<=B^lambda, T=B^delta with fixed 0<lambda<delta<1, then an independent MED condition

    E_m=o(X B^(2-2lambda-delta) log^3 B)

suffices for (5), by (1)-(2). HIGH still needs E_h,J=o(XB log^3 B). Thus whenever 2lambda+delta<1, the MED estimate may be much weaker than the cubic-log scale. For z=old Z with L_z=B^{o(1)}, any fixed 0<eta<1, E_m=O(X B^(2-eta)) suffices with T=B^(eta/2). This is an alternative joint route with a polynomially weaker MED condition. These are sufficient estimates, not proved actual upper bounds.

## 4. Masking caveat and a destination-aware extension

Previous band thinning, moving marks, and other incidence deletions were proved to lose o(XB) LINEAR budget; they need not preserve enough MED destinations here. Equation (7) uses NATURAL MED weights. It cannot automatically be inferred from an o(XB log^3 B) energy estimate after arbitrary earlier o(XB) incidence deletions throughout p>z. This distinction matters because the factor L_z can amplify losses.

If the MED mask loses delta_m linear budget, one can instead replace R_m by R_m,J+delta_m in (2). Equivalently, discard the LOW blocks assigned to removed MED events: the full natural destination wait costs >=1/2, and its LOW block costs <=b. The additional LOW loss <=2b delta_m for a whole-incidence mask. For fractional masks, the inequality using R_m,J+delta_m works directly without discarding whole blocks. Thus

    R <= (1+3L_z)[sqrt(S(T)E_m,J)+delta_m]
          + sqrt(S(B)E_h,J) + O(N[L_z+T+B L_z/T]) + delta_h.

In (6), one can use E_m,J=O(XB log^3 B) if L_z delta_m=o(XB). A sharper option is to track actual assigned LOW cost lost at removed MED destinations, rather than the uniform 3L_z factor: if that actual cost is o(XB), and delta_m=o(XB), the same conclusion holds with the retained destination cost. Arbitrary HIGH masks need only lose o(XB); HIGH destinations were excluded from transfer already. No assertion that existing MED masks satisfy the amplified budget constraint.

## 5. Finite verification

Standalone research/min_clock_wide_low_transfer_audit.mjs, exact remote readback at 769ac3bf5aed610aa68d3c1b28110ca3298566e7, blob dcc9865bb7c96f67d9dded1e898295b3abf1b32d. Run:

    node research/min_clock_wide_low_transfer_audit.mjs 1024 4096 16384 65536 262144

Executed actual JS audit function in available runtime for five X windows x four modes (20 successful runs). All original odd roots, no earlier pruning or cumulative marks. Independent literal parity-GCD clock comparison at X1024 (4658 comparisons per mode). Actual full LOW-block gain/elapsed/cost bound, next MED full wait containment, exact three-class and LOW-transfer linear partitions, destination count dominance, energy Cauchy and (2), deterministic diagnostic whole-event mask and its amplified destination loss bound. Arithmetic integer counts exact; fractional energies use floating tolerances. Sieve support (1) is imported; the finite data do not prove its asymptotics.

Analytic uses f=max(1,loglog B)^.25, largest primorial under B^(1/3)/f, T=ceil(B^(1/3)); z=2 or 3 at tested sizes, so the asymptotic logarithmic cutoff is NOT numerically reached. Fixed diagnostics z=3,5,7 and T=ceil(sqrt B); these are not the asymptotic choice, and at the smaller X fixed7 trim can empty the LOW slab. The diagnostic mask drops roughly a fifth of events by a deterministic residue test; it is not an o(XB) deletion theorem.

At X262144,B1355,N131072: 3941922 events, R2373997.5, E184229117.19. Largest analytic z3,L6,T12: R_LOW78489,R_MED136284,R_HIGH2159224.5; LOW transfer33172, trailing4694.5, followed HIGH40422, trim200.5. 20425 positive destinations, total natural destination cost67369, actual maximum LOW gain4. E_m9861795.99,E_h167743847.05. Fixed5 z5,L30,T37: LOW138029, MED235529, HIGH2000439.5; LOW transfer91954.5, trailing8880, high36384.5, trim810. 26619 full destination waits, max actual LOW gain14, elapsed19; E_m16619641.62,E_h156073953.53. Fixed7 z7,L210,T37: LOW186532.5, MED187025.5,HIGH2000439.5; LOW transfer92674.5, trailing13604, high72165, trim8089. 18661 full destination waits, max actual gain34, max elapsed55, max clipped block cost26.5. E_m13560552.78,E_h156073953.53. The diagnostic mask in fixed7 loses MED37372 and assigned LOW18513 (92674.5-74161.5); satisfies actual amplified loss bound. No comparison to previously pruned families or numerical o(XB) inference.

## 6. Consequence for next research step

Previously the natural small non-LOW energy and retained large energy were separate open conditions. The new criterion can remove the small condition entirely if the natural >z energy is bounded, and extend z to logarithmic scale. The remaining mathematical obstacle is actual energy of selections above this wider cutoff, notably the high shared physical histories and the medium destination energy after any masks. The one-sector reduction is not a proof that small events have negligible budget without such a larger-sector assumption; it is also not a bound on near-maximal actual small-event mass. Further progress should use the expanded cutoff and track MED destination losses explicitly rather than repeatedly trying to bound the LOW energy by itself. Main untouched; no Lean compilation or proof of twin-prime infinitude.
