# Low-scale localized deficit-coordinate sieve and macroscopic band supply obstruction

Continuation of [47a1442](https://github.com/tara-sooo/A166944-Lean/blob/47a14426499afbaacaadb11114dac7caccdb4fdf/research/2026-11-26-min-direct-variable-order-sieve-and-uniform-pinned-gaps.md). Return to actual dynamics. The earlier deficit-coordinate sieve required square-root-scale labels (or a fixed power of the absolute horizon) and used the global deficit range. Here rescale its prime-line sieve in the label threshold T itself and localize the horizon in bins of length T^2. Summing the local ranges by disjoint actual variation budgets eliminates the global range hypothesis. The resulting necessary condition applies even for polylogarithmic or more slowly growing label scales, if the selected gain is macroscopic and deficit coordinates have a suitable cap in T. This is a conditional upper supply result, not an exclusion of the full small/middle crossing branch.

## 1. Setup

Fix lambda>1, Y=lambda X, C=floor sqrt(Y+1), an actual contiguous event block with pre-horizons in [X,Y], and total gain G=O_lambda(X). Let T>=7 be an integer tending to infinity with X, T<=C. No fixed power lower bound T>=X^a is required. Select an arbitrary subset of nonresets with label p in [T,2T), p<=C. At each selected event write g=p-1, ordinary post d', side I, x=(d'-6I)/2=hp>0. Write F for selected gain, U_out=G-F, and V_d for total absolute ordinary deficit variation on the full physical block. Consecutive selected events have pre-horizons H,H2, labels p,r, relay E=H2-H-(p-1), ordinary post difference v=d2'-d1', and c=x2-x=v/2-3(J-I)=kr-hp. For integer cutoffs A,B>=0, call a pair close if |v|<=A and E<=B. Assume B<T-1, Q=floor(A/2)+3<=T/2. Then |c|<=Q and p!=r because repeated p requires relay at least p-1.

In the first theorem restrict all selected x to x<=K T^beta, fixed K>0 and 1<=beta<2. For large T this is below T^2, so each x determines its unique selected large prime factor. Thus c!=0 for a close pair. There is no long-clock, prime-cofactor, twin-finitude, crossing or bounded support hypothesis. In particular a subpopulation of actual low-scale cut crossers can be selected, but complement gain always includes every omitted physical event.

## 2. A label-scale prime-line count in one horizon bin

Partition the physical pre-horizon axis into half-open bins [j T^2,(j+1)T^2). Group the selected list by the bin of its pre-horizon. Let R_b=max x-min x within a nonempty group b and W_b=max(T,R_b+1). Count close consecutive selected pairs both in that group. For fixed first x, signed c, relay E, and sides I,J, the two distinct labels p,r are uniquely determined by x,x+c. Their horizon congruences H=e mod p, H+p-1+E=f mod r determine one residue modulo pr>=T^2. In a bin of length T^2 there is at most one integer H in that residue. It determines at most one actual starting event, and its successor in the selected list is unique. Count necessary arithmetic candidates; no assumption of their reachability or independence. Weight each by ending gain <=2T.

Fix a nonzero signed c. Suppose the minimum x=L>=W_b. All x lie in [L,L+W_b-1], so h=x/p and k=(x+c)/r lie in a common bounded-ratio interval [L/(4T),3L/T], positive integers, and both <=K T^(beta-1). Fix h,k, g0=gcd(h,k)|c, a=h/g0,b=k/g0,c0=c/g0. The deficit congruences x=0 mod h, x=-c mod k give one class x=x0+(hk/g0)z, and the two prime forms are p=x0/h+bz, r=(x0+c)/k+az. Their determinant has absolute value |c0|. The earlier dimension-two Selberg argument gives a translated-interval upper bound
    O(N J(a)J(b)J(|c0|)/log^2(2N)),
where J(n)=prod_(odd prime f|n) f/(f-2), after omitting exceptional slope and determinant primes. Here pad the parameter interval to N=ceil(W_b*g0/(hk))+1. For fixed beta<3/2, W_b*g0/(hk)>>T^(3-2beta); hence log N>>_beta log T. Also W_b=O_K(T^beta), so the cutoff floor N^(1/12) is below the labels. Thus the fixed h,k contribution is
    O_(K,beta)(W_b*g0/(hk) * J(a)J(b)J(|c0|)/log^2 T).
At fixed g0, the sums of J(a)/a,J(b)/b over their bounded-ratio ranges are O(1) by the earlier bounded mean J; drop coprimality in the positive sum. The total count for fixed c is
    O(W_b/log^2 T * sum_(g0|abs(c)) J(abs(c)/g0)/g0).
Summing signed c costs O(A+1) since
    sum_(c<=Q) sum_(g0|c) J(c/g0)/g0
       =sum_(g0<=Q) (1/g0) sum_(n<=Q/g0) J(n)=O(Q).
For L<W_b, use dyadic shells [D,2D) from D=T covering x<2W_b, padded if necessary. Their widths sum O(W_b), and h,k have the same bounded-ratio restriction and global cap. Since D>=T, all parameter intervals can still be padded to polynomial length in T and the same argument applies. No extra logarithmic loss.

For 1<=beta<2 use only the first prime condition x=hp, but keep the uniqueness of the second label from x+c. For fixed h, the padded interval length N=ceil(W_b/h)+1 is polynomial in T (W_b/h>>T^(2-beta)); the one-dimensional upper sieve gives O((W_b/h)/log T), then sum 1/h over the bounded-ratio interval. Near-origin shells work the same way. Thus for nu=2 when beta<3/2, or nu=1 when beta<2, the close ending gain in bin b obeys
    F_close,b << T W_b (A+1)(B+1)/log^nu T.              (1)
The constants depend only on fixed K,beta and the sieve dimension. This is a rescaling of the earlier deficit-coordinate prime-line theorem to a genuinely small label scale, with the horizon modulus matched to the bin width rather than requiring pr=Theta(X).

## 3. Sum localized ranges; no global tube assumption

There are at most N_b=O_lambda(1+X/T^2)=O_lambda(X/T^2) nonempty bins, since T^2<=Y+1. The first selected vertex of each bin costs <=2T, and all cross-bin edges can be discarded at total endpoint cost O(X/T). For each bin let V_b be the sum of physical ordinary variations from its first selected post state through its last selected post state (zero for singleton). These post-to-post intervals are disjoint across bins. In particular sum V_b<=V_d. Since x=(d'-6I)/2, R_b<=V_b/2+3, W_b<=T+V_b/2+4. Therefore
    sum_b W_b <= (T+4)N_b+V_d/2 = O_lambda(X/T+V_d).
There is no assumption that the whole population stays in a common narrow deficit interval. Applying (1) and summing gives
    F_close,local << (X+T V_d)(A+1)(B+1)/log^nu T.       (2)
This is the principal new aggregate supply bound. We never charge the same physical variation twice. The relay sums over all within-bin consecutive selected edges are <=U_out, because their intervening unselected events are disjoint. The post difference sum is <=V_d. Thus all ending vertices except the bin-first vertices and those in close edges have total gain at most 2T[U_out/(B+1)+V_d/(A+1)]. Combining yields
    F <= O_lambda(X/T)
      + O((X+T V_d)(A+1)(B+1)/log^nu T)
      + 2T U_out/(B+1)+2T V_d/(A+1).                    (3)
No assumption of similar deficit baselines between bins, actual crossing status, or small physical labels outside the selected band.

## 4. Low-scale macroscopic obstruction

Suppose F>=rho X for fixed rho>0. Set z=T U_out/X, y=T V_d/X. Then
    (1+z)(1+y)^2 >>_(lambda,K,beta,rho) log^nu T.        (4)
Proof: if the product already exceeds log^nu T there is nothing to prove. Otherwise A=ceil(K0 y), B=ceil(K0 z), with fixed K0 sufficiently large depending on rho, are O_rho(log^nu T), so B<T-1 and floor(A/2)+3<=T/2 eventually. The last two terms in (3) are <=4X/K0, and X/T=o(X). The close term is O(X(1+z)(1+y)^2/log^nu T). Rearrange to obtain (4). In particular
    U_out+V_d = Omega((X/T) log^(nu/3) T).
If U_out=O(X/T), then V_d=Omega((X/T) log^(nu/2) T); if V_d=O(X/T), then U_out=Omega((X/T) log^nu T). These bounds apply in every sufficiently large window satisfying the selected-gain and cap assumptions, not just infinitely often. For example T=(log X)^b at fixed b>0, beta<3/2 yields the necessary scale X/(log X)^b * (loglog X)^(2/3) for the combined budget. This is much larger than the square-root-scale bound in absolute units. It is a different population and not an unconditional improvement for all previous high labels. At T~sqrt X it recovers the earlier exponent 2/3 without a global range assumption, via local ranges instead.

## 5. Uncapped selected population: high-deficit escape

Choose the entire selected band population arbitrarily with no x cap, F>=rho X. Still take the same horizon bins, and define z,y using its full complement gain and total physical variation. Count only those within-bin close edges with BOTH endpoint coordinates <=H_cap=K T^beta. Each is consecutive in the capped sublist as well. The sum of its sublist local ranges is still bounded by (T+4)N_b+V_d/2, so (2) bounds its gain using the FULL physical V_d. Every other close ending has x>H_cap-Q, since its predecessor or itself exceeds H_cap. Hence writing F_high for selected gain at x>H_cap-Q,
    F_high >= F-O_lambda(X/T)
       -O((X+T V_d)(A+1)(B+1)/log^nu T)
       -2T U_out/(B+1)-2T V_d/(A+1).                    (5)
If (1+z)(1+y)^2=o(log^nu T), choose A=ceil(L0 y), B=ceil(L0 z), L0->infinity sufficiently slowly that L0^2 times this product is still o(log^nu T). Both cutoffs are polylogarithmic in T and Q=o(T^beta); all error terms are o(X). Thus for every fixed K and beta in the stated range,
    gain of selected events with x>(K-o(1))T^beta
         >= F-o(X).                                    (6)
With nu=1 this includes every fixed beta<2. This is a conditional large-multiplier escape in the low-scale branch: if a single band supplies macroscopic gain with very small normalized relay/variation budgets, almost all its gain must have x close to or beyond the quadratic scale in T. No full-ray deficit lower bound follows from this localized theorem, because V_d may be much larger than T^beta when T is small. The pin-only alternative of [47a1442] does not force any one band to supply macroscopic gain, and its low crossing count does not imply F>=rho X in such a band. Nor are the small budgets or cap automatic. To exclude the full small/middle alternative still requires control of gain spread across bands, high deficit escape, or a direct witness. No twin-infinitude contradiction or Lean kernel proof.

## 6. Diagnostics and preservation

[Final audit e6f8e4c](https://github.com/tara-sooo/A166944-Lean/blob/e6f8e4c67e1a70803c51662c6da564462c1d8a64/research/min_direct_low_scale_deficit_sieve_audit.mjs), blob c0d6a24105e2c22e0b9c9514da683444ead31bbf, exact remote readback. Run node research/min_direct_low_scale_deficit_sieve_audit.mjs 60000. Actual ECMAScript execution in tool runtime. 29998 odd canonical roots through60000,549085 events,0 unresolved cap180. 122787 finite selected-band controls T7/11/17/31/61 with finite caps floor(T^1.85) or floor(T^1.4),230178 selected incidences,107391 filtered pair comparisons,9885 close pairs,19770 unique divisor checks,9885 each prime-line and horizon CRT checks,42921 exact prime residue checks,9862 weighted tuple capacity checks.7198 close incidences with pre H>100 T^2. Local horizon-bin controls:159281 nonempty groups,70897 within-bin edges,36494 discarded cross-bin edges,27763 multi-bin blocks,122787 summed local range and gain budgets. Independent abstract 4288 translated congruence systems,12864 residue controls and800 synthetic local-range controls (not actual MIN rays). Example T11,p17,r11,x51->55,H390->408,E2,v2. Counts overlap across controls. The finite audit tests arithmetic, actual bin accounting and budgets, not the asymptotic sieve constant; the prior analytic Selberg proof is reused. All assertions passed. No Lean executable/kernel verification, external novelty claim or final contradiction. Main and sibling branches not modified.
