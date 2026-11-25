# Exact factor-clock phases, near-factor deficit obstruction, and bounded-phase local realization

Continuation of [1c93832](https://github.com/tara-sooo/A166944-Lean/commit/1c93832992123234dbfc906f1d8a08024c72666f) on the independent direct-arithmetic branch. Instead of counting prime triples alone, this note compares all actual competing clocks of a plateau. It gives a sharp local converse to the roughness obstruction, plus a restriction coupling close factors to large deficits. No global recurrence bound sufficient to contradict the previous trichotomy is obtained. Paper proofs, not Lean kernel verification; twin infinitude and A166944 remain open.

## 1. Sharp local realization theorem

Fix an even H>=8, an eligible odd prime p with p^2<=H+1 and p|H-e, where e=+1 means even side, e=-1 odd side. Each odd prime f divides at most one of H-1,H+1. Let the competitor set consist of all distinct other eligible primes f, with side e_f. Repeated prime powers introduce no extra clocks. The clock for side +1 occurs at ticks 0 mod2f; side -1 at ticks f+2 mod2f.

Fix an intended wait w in [1,2p]. Let I=(1-e)/2, q=(H-e)/p, h0 in {0,1} satisfying (q+1)/2+h0=I mod2, and
    n0=p((q+1)/2+h0)+2I.
All intended winning ticks n=n0+2p*j, j integer, are exactly the p-clock ticks on the prescribed side. Take start t=n-w, and shift n by a common period if needed to ensure t>=H/2. This changes none of the competing clocks.

For each competitor f, let ell_f be the nonnegative residue n-b_f mod2f, with b_f=0 or f+2 according to its side. On the same side ell_f is even, on the opposite side odd. Because f!=p, as j runs through residues mod f, ell_f takes each of the f residues of the required parity exactly once. The last clock before n preempts precisely when 0<ell_f<w. If ell_f=0, the clock at n is a tie, lost by p iff f<p; otherwise its preceding clock is at n-2f and is harmless provided w<=2f. For a same-side f>p this latter inequality is automatic since w<=2p. Equality at the starting tick t is allowed, since the next-event rule is strict future.

Thus the exact numbers of admissible j residues modulo f are
    A_f(w)=max(0,f-floor((w-1)/2)-1_{f<p})    same side,
    A_f(w)=max(0,f-floor(w/2))                opposite side.
In the same-side f>p formula the floor is already <f. For same-side f<p, once all residues are forbidden the formula correctly truncates at zero even for w>2f.

Let P=product of distinct competitor primes (P=1 if empty). By CRT the number of admissible phase residues j mod P is EXACTLY product_f A_f(w). Therefore the possible waits for some abstract plateau start t>=H/2 with this fixed H and winning p are exactly
    1 <= w <= W_max,
    W_max=min(2p, min_{same f<p}(2f-2),
                  min_{same f>p}2f, min_{opposite f}(2f-1)).
An empty minimum is omitted. No hidden sufficiency condition: choose one allowed residue for every f, combine them by CRT, then add positive multiples of P to j. The waiting event is actual adaptive MIN, not a relaxed horizon transition. The density among intended p-clock phases over a full period is the product of A_f(w)/f. The entire set is periodic, and each possible wait occurs for arbitrarily large abstract t. This does NOT say that any such t lies on a canonical trajectory.

For long-wait type III from the preceding notes, this theorem sharpens the necessary roughness lower bound on competitors by the exact parity/tie constants. It also explains why a stronger local exclusion of composite cofactors cannot follow from merely adding the independent clock congruences for a,b: those congruences factor by CRT when the phase is free.

## 2. Exact lag in adjusted-deficit coordinates

At the p event, put Z=H+p-1, D=2n-Z-6I. Then
    D=2p*h, n=p((q+1)/2+h)+2I,
    h=h0 mod2.
For actual p>=5 events with envelope 2n>=Z, h>=0, since D>=-6 and is a multiple of 2p. This includes canonical trajectories. For p=3 negative h can occur and the nonnegativity statements below are not asserted for that case.

For a distinct eligible competitor f, its lag residue ell_f in [0,2f) is uniquely specified by
    2ell_f = (2h+1)p                 mod f,   2ell_f=0 mod4    same side,
    2ell_f = (2h+1)p-6e              mod f,   2ell_f=2 mod4    opposite side.
Indeed double the clock residues and use H=e_f mod f. The interval for 2ell is [0,4f); the congruences modulo f and 4 determine it uniquely. Same-side lag zero is the tie case as in section1.

In particular suppose f<p on the same side and f=p mod4. Set c=p-f>0 (a positive multiple of 4). Then
    2ell_f = (2h+1)c mod4f,
with the least nonnegative residue on the right. Necessarily w<=ell_f and ell_f!=0 (a tie would lose to f). Since (2h+1)c is positive, it is at least 2ell_f. Thus
    (2h+1)c >= 2w.
For long-wait events 4w>=p-1 this implies
    h >= (p-1)/(4c)-1/2,
    D >= p(p-1)/(2c)-p.                              (1)
The ordinary deficit d=2t-H immediately before the event satisfies d=D+6I+p-1-2w, and w<=2p. Consequently
    d >= p(p-1)/(2c)-4p-1+6I.                        (2)
In particular if c=o(p) along unbounded such events then d/p tends to infinity, and if c is fixed then d=Omega(p^2). Conversely, if d<=Kp for a fixed K>=0, (2) forces c>=p(p-1)/(2((K+4)p+1-6I)), a linear-in-p lower bound. This is a pointwise obstruction, independent of prime-counting and even of the number of cofactor factors.

On the opposite side with f<p and f=p mod4, replace the integer (2h+1)c by (2h+1)c-6e. When this is positive its residue is at most itself, yielding (2h+1)c-6e>=2w. For e=-1 it is always positive. For e=+1 the special case c=4,h=0 gives -2 and the simple positive-integer bound does not apply. The exact congruence is valid in every case.

## 3. Reset restriction for maximal selected factor

Specialize to type III H-e=pab with three distinct primes and p>max(a,b), long wait 4w>=p-1. If D=0, h=0. On the even side q=ab=3 mod4, so a,b have opposite classes mod4. At least one of them shares the class of p; (1) implies that factor is <=(p+1)/2. Hence
    H-1=pab <= p^2(p+1)/2.
In particular a balanced triple with both cofactors > (p+1)/2 cannot have its maximal factor win in an even adjusted reset with the stated wait. On the odd side q=1 mod4, so both factors share a mod4 class. If they share p's class then both are <=(p+1)/2, implying H+1<=p(p+1)^2/4. If both have the opposite class, this particular obstruction does not apply. This excludes a phase-dependent near-cube configuration, not all narrow triples. No implication from finite twins alone that the maximal factor is the winner or that D=0.

## 4. Many local realizations even within quadratic adjusted deficit

The full-period CRT converse could in principle require phases with enormous absolute t. A separate short-interval result shows this need not happen in an important class.

Suppose p is the least eligible prime of H-1,H+1 and the total number of other distinct eligible primes is at most five. Put w=ceil((p-1)/4). Then among the 4p consecutive phase indices j=0,..,4p-1 in section1, at least p/2 give actual winning p at this exact wait. All starts satisfy t>=H/2 and winning adjusted deficits obey
    0<=D<16p^2.
For p>=5, each f>p satisfies f>=p+2. Its number of forbidden j residues is b_f<=floor(w/2)<=(p+2)/8, so b_f/f<=1/8. In a consecutive interval of length 4p, it forbids at most 4p*b_f/f+b_f indices: partition into complete cycles and a remainder. A union bound for at most five f therefore leaves at least
    4p-5*(4p/8+(p+2)/8)=7p/8-5/4 >= p/2
for p>=5. For p=3, w=1, no residue is forbidden because p is least. The start n0-w>=H/2 follows directly from the formula for n0 and w; h=h0+2j<=8p-1 gives the asserted D range.

For a type-III arithmetic plateau with p least prime factor of both neighbors, H-e=pab, and (p-1)^4>4096(Y+1) where H<=Y, the number of competitors is automatically <=5 because all factors exceed the fourth root and each neighbor has at most 3 factors. Thus it has many actual fourth-root qualified abstract starts with D=O(p^2)=O(H^(2/3)) since p^3<=H+1. Their ordinary pre-deficits are at most 16p^2+p+5. The short-interval bound does not assert that any of these starts is a canonical ancestor. It shows a purely pointwise clock obstruction cannot rule out this whole composite branch even with a sublinear upper bound on ordinary deficit. The open constraint is the evolution and joint realizability of those phases along one path. No upper bound on repeated selected-label multiplicity follows from counting admissible phases at different H independently.

## 5. Exact diagnostics

[Full phase audit a295eb9](https://github.com/tara-sooo/A166944-Lean/blob/a295eb9daef3a4c0377fe55ba66bd467b18b8988/research/min_direct_factor_clock_phase_audit.mjs), blob f24f66e999ff3f3a660ff8419f26360291353e7e. Run node research/min_direct_factor_clock_phase_audit.mjs 2000. Actual ECMAScript function execution in tool runtime, not separate Node process. All even H=8..2000: 938 with eligible clocks, 2015 eligible labels, 35966 intended waits; 14987 possible and 20979 impossible. Exhaustively checked all 98,322,030 phase instances across each complete competitor-product period for each intended wait, 589020 individual factor-residue checks, 14987 constructive CRT examples, 2015 exact maximum checks, 11251 literal GCD ticks (including the large example below). 442 close-factor positive representative checks, 68 preemption instances for w=ceil((p-1)/4), 374 with lag>=w. This last count does not certify actual wins against all competitors.

Large all-distinct type III example from prior note: H125876515620, p5003, e=-1, a5009,b5023, w1251. Eligible competitors f3457 on opposite side and f5009,f5023 on same side. Allowed residue counts 2832,4384,4398 respectively; product 54,603,316,224 among P=86,978,835,599 intended-clock phases. Constructed exact CRT n62938265317,t62938264066, verified literal ticks using BigInt clock arithmetic.

[Short-phase audit 04d73ee](https://github.com/tara-sooo/A166944-Lean/blob/04d73eeb68ef8cc88e401e1a094bf4fe086f9541/research/min_direct_factor_clock_short_phase_audit.mjs), blob 36b17dfd9bcac49c17aa8e72f1172f0a060631e4. Run node research/min_direct_factor_clock_short_phase_audit.mjs. 940 least-label plateau checks (938 small plus 2 large cube examples), 58120 phase indices; all meet p/2 lower bound. At H=5003^3+1, 18922 of 20012 phase indices realize w1251, one opposite competitor11483. At H=5039^3+1, all 20156 indices realize w1260, no other eligible factor. First valid starts independently checked by 2511 literal GCD ticks. These are abstract starts, not canonical trajectories. No new canonical trajectory scan, no empirical extrapolation of global recurrence, no Lean kernel verification. Both audit files exact remote readback. Main and sibling branches unchanged.

Next mathematical target: use the exact lag restrictions (1)-(2) on the evolving adjusted deficit, rather than only enumerate admissible plateau phases. The local converse rules out an unconditional exclusion based solely on local clock availability. To disprove the large composite branch requires coupling many different horizons, or an independent stopping principle. Small-label concentration and prime-cofactor branch also remain open.
