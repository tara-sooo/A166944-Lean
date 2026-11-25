# Certified-event bridges: four-residue sieve and polynomial transition diversity

Continuation of [c27a25f](https://github.com/tara-sooo/A166944-Lean/commit/c27a25fb1572f721928b17793fe47b2914426225) on the independent direct-arithmetic branch. New results couple distinct certified events along a SINGLE actual adaptive MIN trajectory, without reset or prescribed short-word hypotheses. No historical merger/cost framework. The polynomial transition-diversity theorem uses the previous local crowding lemma and elementary CRT, independently of the new dimension-four sieve. Neither theorem proves twin infinitude or A166944.

## 1. Definitions and previous input

Canonical odd root M>=5: H0=2M-2,t0=M+2. Adaptive event at earliest tick n>t and least eligible odd prime p at ties, p^2<=H+1; e=+1 even / -1 odd, H=pq+e, H'=H+p-1, w=n-t. Fix a finite contiguous event block with all pre-horizons <=Y. Set B=1+floor cbrt(512(Y+1)), C=floor sqrt(Y+1). An event is certified when p>B and 4w>=p-1. Then q>=p is prime, both H+-1 have all prime factors >(Y+1)^(1/3). The sequence of certified events in the block is obtained by deleting other events, without reordering. Call them z_i=(H_i,p_i,e_i,q_i), i=1..m. Their total gain V=sum_i(p_i-1). All statements below about pairs use actual events within this one sequence, not different roots. For each successive certified pair define
    g_i=H_(i+1)-H_i,
    s_i=g_i-(p_i-1)>=0, even.
Here s_i is the sum of all intervening noncertified gains. In particular g_i>2 for sufficiently large Y. We call (p_i,p_(i+1),s_i) its transition pattern, not a complete event transcript. The disjoint pre-horizon spans telescope: sum_i g_i<=Y (indeed <=H_m-H_1<=Y).

Previous results used below:
(a) In every sufficiently large crossed [X,16X], Y=16X, either small labels p<=B have gain >=Y/88 or V>=Y/88. Finite twins imply every canonical adaptive ray beyond last twin center crosses all these intervals.
(b) Certified q is strictly increasing on successive occurrences of fixed p>=5. In any interval of L consecutive cofactors, count <=K L/log^2(2L) for an absolute K, by the earlier two-residue upper sieve; equivalently m occurrences have cofactor span+1 >=c0 m log^2(2m), c0>0 absolute. This holds for either sign union and arbitrary interleaving, since both H+-1 are rough. The exact pre-horizon span is p(q_last-q_first)+e_last-e_first. Thus for all m above an absolute fixed threshold, span >=c1 p m log^2(2m), c1>0 absolute.

## 2. Four-residue upper sieve

Fix p in the certified range and fix an integer g>2, g<=Y. For a certified event H=pq+e and another certified event at H+g, the four integers
    pq+e-1, pq+e+1, pq+e+g-1, pq+e+g+1
have no prime factor <=(Y+1)^(1/3). For primes l>31 with l<p, the forbidden q residues are the roots of these four linear forms; rho(l)=4 except if l divides Delta=g(g-2)(g+2), when rho(l) is 2 or3 (for l>31, collisions occur precisely on those divisors). Use the same elementary quadratic-form upper sieve as c27a25f, now with squarefree d<=z supported on primes l>31 and rho(l)<=4. Its derivation is unchanged: g_s(d)=rho(d)/d, h(l)=(1-g_s(l))/g_s(l); the diagonalizing choice y_r=mu(r)/(h(r)G), G=sum 1/h, gives lambda1=1, quadratic main 1/G and |lambda_d|<=d because 1/(1-rho(l)/l)<=l. CRT count error <=rho(d); expansion error <=z^6. So survivors in length N <=N/G+z^6.

Let G4 be the reference value with rho(l)=4 at every l>31. Then G4>=sum squarefree d<=z supported on l>31 of 4^omega(d)/d. To lower bound this, take ordered quadruples of positive integers a_1..a_4<=T=floor z^(1/4), each coprime to W=product of primes<=31, weighted by 1/(a_1 a_2 a_3 a_4). Total mass H_W(T)^4, H_W(T)=sum_{a<=T,(a,W)=1}1/a. Exclude each of the 4 events l^2|a_i and the 6 events l divides both a_i,a_j, for every prime l>31. Scaling the divisible entries bounds their total excluded mass by 10 H_W(T)^4 sum_{l>31} 1/l^2 <= (10/31) H_W(T)^4. Remaining tuples have squarefree pairwise coprime entries, product d<=z; each d has at most 4^omega(d) representations. H_W(T)>=c_W log T for all large T by restricting to a=1 mod W, so
    G4 >= c2 (log z)^4
with absolute positive c2 (W fixed; no useful numerical constant claimed).

Define J4(Delta)=product_{prime l>31,l|Delta} l/(l-4). Split the reference summation by the prime factors dividing Delta, dropping their product cutoff; on the coprime part its weights coincide with G. This gives G4<=J4(Delta) G. The factor satisfies a uniform elementary bound
    J4(Delta) <= O((log log(3 Delta))^4).
Proof: log(l/(l-4))<=4/l+O(1/l^2) for l>31. For x>=3, elementary Chebyshev theta(x)=O(x) gives sum_{l<=x} (log l)/l=O(log x) by partial summation. With sigma=1+1/log x, 1/l-1/l^sigma<= (sigma-1)log l/l, so sum_{l<=x}1/l <= log zeta(sigma)+O(1) <= log log x+O(1). Here the Euler product at sigma>1 follows by expanding finite prime products and monotone convergence, and zeta(sigma)<=1+1/(sigma-1) by the integral bound. Now split prime divisors of Delta at x=max(3,log Delta). Those >x have count <=log Delta/log x and reciprocal sum <=log Delta/(x log x)<=1/log x. Thus sum_{l|Delta}1/l <=log log x+O(1), giving the stated fourth power. This is only an upper bound, not a prime-pair asymptotic.

Apply the sieve to q in [1,N], N=floor((Y+1)/p), z=floor N^(1/12). For sufficiently large Y, z<p and z<=(Y+1)^(1/3); log N comparable to log Y, Delta<=Y^3, and error <=sqrt N. For each fixed sign e this bounds the number of eligible q by O(J4(Delta) N/log^4 Y); summing signs and using distinct q on p visits proves
    total first-event gain for prescribed p,g
        <= K4 Y (log log Y)^4/(log Y)^4.                (1)
Uniform in p,g and block, whenever both pre-horizons are certified. This counts all such pairs for prescribed displacement, whether or not successive in the certified list; at fixed H and g the second pre-horizon is unique because H strictly increases. It also applies to (p,s) for g=p-1+s. If V>=delta Y for fixed delta>0, all but the last certified event have a successor, whose first-event gains sum to >=delta Y-C. Consequently at least Omega_delta(log^4 Y/(log log Y)^4) distinct (p,g), equivalently (p,s), appear. If only K distinct s values are permitted in a subset carrying >=delta' Y gain, at least Omega_delta'(log^4 Y/[K(log log Y)^4]) distinct p appear in that subset. These are coupled capacities, not a lower bound on each pattern's multiplicity.

## 3. Different-label bridges carry positive gain

This part only needs the previous two-residue local crowding, not section2. Assume V>=delta Y for an absolute delta>0. Partition the certified list into maximal runs of constant label p (unqualified events can occur between visits within such a run). Let a run have length m and gain m(p-1), and span from its first to last pre-horizon. By input (b), for m sufficiently large, span >=c1 p m log^2(2m). Run spans are disjoint as intervals (possibly singleton spans), so their sum <=Y. Pick a fixed integer L>=2 so large that 1/(c1 log^2(2L))<=delta/2 and (b) applies to m>=L. Then all runs of length>=L together have gain <=delta Y/2. The short runs (m<L) therefore have gain >=delta Y/2.

For each short run its last event has gain p-1, at least 1/L of its run's gain. Unless it is the final run, that event is followed in the certified list by an event with DIFFERENT label. Removing the final run's last gain costs at most C. Hence the gain of all first events of different-label certified successor pairs is >=delta Y/(2L)-C>=delta Y/(4L) for sufficiently large Y. Define beta=delta/(4L)>0. This is a uniform positive proportion of the horizon bound Y, not merely a logarithmic number of transitions between runs.

Further, the sum of intervening gains s_i is <=Y because the bridges are disjoint. For any fixed K0>=1, the first-event gains of bridges with s_i>K0(p_i-1) sum to <=Y/K0. Choose K0>=2/beta. The subset of DIFFERENT-label bridges with
    s_i<=K0(p_i-1)
still has gain >=beta Y/2. Thus a fixed positive proportion of total horizon scale is necessarily carried by different-label transitions with intervening gain bounded by a fixed multiple of the initial label. Constants depend only on delta and the absolute crowding constant, not on the root or window. This is not a bound on number of intervening events or a statement that s is uniformly bounded.

## 4. Polynomial transition-pattern diversity by CRT

Fix distinct certified labels p,r>B and a fixed even s>=0, and endpoint signs e,f. For a pair with pattern (p,r,s),
    H=pq+e,
    H_next=pq+e+p-1+s=rQ+f.
Thus
    p q = f-e-p+1-s mod r.
Since p,r distinct primes, q is in one residue class modulo r. It is in [p,floor((Y+1)/p)], and distinct first occurrences of p have distinct q. Therefore the number of these pairs for fixed pattern and signs is <=1+floor((Y+1)/(pr)). Sum the four sign choices. The total first-event gain for that pattern is bounded by
    4(p-1)(1+(Y+1)/(pr))
         <=4(C+(Y+1)/B)=O(Y^(2/3)).                 (2)
Without the gain weighting, the crude count bound yields Omega(Y^(1/6)) distinct patterns from Omega(sqrt Y) events, but (2) is stronger.

By section3, V>=delta Y implies at least Omega_delta(Y^(1/3)) DISTINCT triples (p,r,s), with p!=r and s<=K0(p-1), among the certified successors. This uses only CRT plus the established local crowding to guarantee different-label gain. No twin-pair distribution assumption. It is a polynomial, rather than polylogarithmic, lower bound on transition-pattern diversity.

Let A be number of distinct certified labels and T number of distinct intervening gains s among this restricted subset of pairs. At most A(A-1)T distinct patterns are possible. Hence
    A^2 T >= c3 Y^(1/3),
    max(A,T) >= c4 Y^(1/9)
for absolute positive constants once delta is fixed. In particular if A is polylogarithmic then T must grow at least as Y^(1/3) divided by the square of that polylogarithmic bound. If T is bounded, A>=Omega(Y^(1/6)). If all considered pairs are actual adjacent nonunit events then s=0, but the theorem does NOT assert a positive fraction of pairs has s=0; it requires neither adjacency nor short actual event words. More generally in a high-band subset with both labels >=Y^theta, 1/3<=theta<=1/2 and positive gain, (2) improves to O(Y^(1-theta)) per pattern, so at least Omega(Y^theta) patterns. This variant requires positive gain in that high-band subset, not guaranteed by the general argument.

For contrast, equal-label pairs p=r have no invertible CRT condition. Their intervening gain s is at least p-1 for p>=5: from the previous exact return identity q2-q1=2m, m>=1, s=(2m-1)p+1+e2-e1. The run argument is essential because (2) cannot be applied indiscriminately to equal labels.

## 5. Global theorem under finite twins

Fix an infinite adaptive canonical ray (under finite twins any canonical ray beginning beyond last twin center). In every sufficiently large crossed [X,16X], Y=16X, either:
(A) some prime p<=B occurs Omega(Y^(1/3) log Y) times (unchanged);
(B) V>=Y/88, and the following simultaneous necessities hold:
- previous Omega(log^2 Y) distinct certified labels, each Omega(log Y) certified visits, and Omega(log^2 Y) distinct cofactors;
- Omega(log^4 Y/(log log Y)^4) distinct (p,g) certified successor pairs;
- a positive fraction of horizon-scale gain on different-label certified successors with s<=K0(p-1), at least Omega(Y^(1/3)) distinct (p,r,s) patterns there, and A^2 T>=Omega(Y^(1/3)).

Use delta=1/88, so all constants absolute. The rich labels from the previous theorem need not be precisely the labels in the restricted bridge set. This does not force either A or T alone to be polynomial, or imply infinitely many twin witnesses. Neither the small-label alternative nor this large-label transition diversity has yet been contradicted. In particular the inequality on pattern count cannot be compared to a constant alphabet size if intervening gains are unrestricted.

## 6. Diagnostics

[Audit a462c97](https://github.com/tara-sooo/A166944-Lean/blob/a462c97e1f4f7fe858bbf3fe62851f49e4c100a6/research/min_direct_certified_bridge_audit.mjs), blob dfafc615d225a62edaa8155e55a33def46a4cfbc, exact remote readback. Run:
    node research/min_direct_certified_bridge_audit.mjs 200000 180
Actual ECMAScript function executed in tool runtime, not a separate Node process. Four-root sieve audit: 240 configurations (three p, eight g including colliding residues, both signs, five z values up to251), 4560 collision classifications, 4800 rational weights, 151680 quadratic summands, 120000 direct integer checks. BigInt checks of the exact diagonalization, weight/error bound, pointwise majorant, and singular-product comparison; all passed. This small z audit does not empirically estimate the asymptotic log^4 lower bound.

Actual adaptive scan all odd M=5..200000, <=180 nonunit events: 2,278,154 events, 98,065 nonempty paths, 1326 certified event incidences using final horizon as Y, 82 successive certified bridges, all different labels, 1326 same-label run partition checks (max run1), 82 progression/capacity checks (max sign-pattern multiplicity1), 666 four-neighbor roughness residue checks. No same-label certified successor found in this bounded scan, not a theorem. Representative M184187: first p601,e=-1,H368412,t184224,w285,q613; next certified r587,e=+1,H370398,t185778,w888,Q631; g1986,s1386. These are actual clock events, not claims that they are consecutive nonunit events. All numerical checks passed. No finite large-window or infinite ray claimed. No Lean kernel verification. Main and sibling branches unchanged.

The next global target is to bound the joint support of labels and intervening gains using actual clock phases, or rule out small-label concentration; pure CRT and upper-sieve capacity estimates cannot by themselves contradict polynomial diversity.
