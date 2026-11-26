# Primorial neighborhood MIN: potential, exact finite CRT reachability, and shadow lifting

2026-11-26 JST. Independent continuation from direct-arithmetic 14c6176473bd6b30599d06a02e49cc2679c227ae. The earlier certificate is in research/2026-11-26-min-direct-sieved-hybrid-twin-certificates.md. Paper deductions and finite Python experiments, not Lean verification. Twin infinitude remains open.

## 1. Coordinates and generalized certificate

S is an integer >=5, P_S is the product of odd primes <=S. Take J divisible by 4P_S, R=J/2, actual horizon H=J+u and time t=R+v. Canonical odd root M=R+3 starts at (u,v)=(4,5). The ordinary deficit d=2v-u is nonnegative. Choose J sufficiently large for all primes in any finite transcript to be eligible in the adaptive square-root MIN.

At a tick with relative time n the exact raw GCD is
- even n: gcd(R+n,2n-u+1)
- odd n: gcd(R+n-2,2n-u-5).

Parity agrees since R is even. The second argument is odd and nonzero. For a plateau with 4<=u<=S^2-2, absence of any odd prime <=S dividing H±1 is equivalent to absence of such primes dividing u±1, hence to both u±1 being prime >S. This is already a certificate at a reached plateau, without a jump or a label restriction. The same argument holds for negative offsets by exchanging neighbors. If w>2S and S is eligible then the plateau is rough; a small competitor would have fired within 2S.

## 2. Improved necessary crossing length under finite twins

If at least one of u±1 is composite, it has an odd prime factor q<=sqrt(u+1)<=S in the window. This q divides the corresponding actual neighbor, so w<=2sqrt(u+1). With Phi(v)=sqrt(2v+1) and u<=2v, Phi(v+w)^2<=Phi(v)^2+4Phi(v)<(Phi(v)+2)^2.

If twins are finite, there is a fixed offset U beyond all twin centers. For S>U+1, every plateau u<=U has a competitor <=U+1, so the number and total waiting of this initial segment are bounded solely by U (u increases by at least 2 each event). This also bounds the time at the first event leaving that segment. All subsequent events with pre-offset in [U,S^2-2] increase Phi by <2. Crossing to u>S^2-2 implies Phi>=sqrt(u+1)>=S (even offsets and integer S). Hence for all sufficiently large S every such crossing from (4,5) has m>=S/2-O_U(1) events. Stopping in the actual adaptive orbit at large H itself certifies twins H±1. A crossing family of size m<=(1/2-epsilon)S for arbitrarily large S and sufficiently large J, or an unbounded family of adaptive stops, proves twin infinitude. The earlier S/4 threshold is improved by factor 2. This result does not prove the requisite upper bound.

## 3. Deterministic small-label shadow and exact lift

Discard labels >S temporarily. At (u,v) the next event is the lexicographic minimum (w,p) over p<=S dividing u-1 (even clock n=0 mod 2p) or u+1 (odd clock n=p+2 mod 2p). This is exactly the small-prime clock system for every J divisible by 4P_S. Let A=max over its finite prefix of d+2w+1. All raw GCD prime factors up to the corresponding event are <=A, because the odd-clock defect has absolute value at most max(3,d+2w+1). If A<=S, the whole shadow prefix is forced in every sufficiently large lift, even without excluding large primes by CRT.

More generally suppose this shadow reaches a rough plateau (u,v) in the window after m events and 2(m+1)<=S. Choose a prime p>max(S^2,A,2v+1) with p=1-u mod4, possible by Dirichlet. Set R=0 mod2 and modulo all odd primes <=S; set 2R+u=1 mod p. For every other q>S up to p exclude the at most 2(m+1) residues 2R+u_i=±1 over all prefix plateaus and the final plateau. Since q>S, some residue remains. CRT gives arbitrarily large R in the resulting class. The selected p cannot intervene earlier since p>A. At the final rough plateau the first event is p, at relative time n=(u+p-1)/2, which is even, strictly greater than v, and has defect p. All other q<=p are excluded at this plateau; earlier defects have magnitude <p. At the event, u jumps by p-1, so the orbit crosses the window in m+1 events. If A<=S, prefix exclusions are unnecessary and only the final plateau needs the two exclusions per q>S; no bound on m is then needed. This is an actual adaptive lift, not merely an abstract high-label word. It relies on a reached rough offset; it does not give rough offsets without finding twin primes.

## 4. Exact finite CRT search

For a large lift, at each tick n enumerate the prime divisors of the nonzero defect h in ascending order. The candidate p fires exactly when R=-n+2*1_(n odd) mod p. For p<=S this is a known Boolean, since R=0 mod p. For p>S keep its possible residues, equivalently a required residue if selected earlier and a set of forbidden residues. A quiet tick forbids the active residue for every candidate. Selecting p requires its active residue and forbids those of every smaller candidate at that tick. A consistent finite history has an actual arbitrarily large integer lift by CRT; conversely every sufficiently large actual lift yields a consistent history. In a nonrough window state a small competitor guarantees a transition within 2S ticks. Thus BFS over (u,v,per-prime constraints) enumerates exact finite reachable event words, not independently resampled residues. A depth-m search needs only primes bounded by 4Sm+O(1) until the first rough state or crossing. The implemented BFS stops at a rough plateau and skips paths already outside the window; its minima are for reaching a rough plateau, not minimum crossing length. No asymptotic guarantee on the search size or short-word existence is obtained.

## 5. Executed finite diagnostics

Python/SymPy shadow computation through S=10^12 (25 selected thresholds). Selected rows (S,rough u,m,max deficit,max defect upper bound A):
- 30,60,7,60,87
- 100,150,13,6,67
- 1000,1320,23,36,667
- 10000,10890,48,102,5425
- 100000,176022,89,354,88009
- 1000000,1409790,157,606,704587
- 100000000,180585090,462,4894,90292519
- 10000000000,11558106798,924,496020,5778902155
- 1000000000000,1479447551580,1602,496020,739723735069.

For the last row the exact twin pair is 1479447551579 and 1479447551581. A<S, so the reached prefix is forced in sufficiently large lifts; no huge primorial was materialized. In particular these finite computations are heavily overlapping deterministic offset prefixes, not independent samples or evidence of a proved asymptotic law.

Exact residue-constraint BFS for S=5,7,10,20,30,50,70,100,150,200,300,500,1000,2000. Minimum rough-hit event counts respectively 2,2,2,5,6,6,13,13,14,15,15,22,23,26. At S=30 one large label 31 with wait12 improves the small-only count from7 to6; at S=150 large label163 with wait78 improves small-only from18 to14. At S=5 label7 with wait3 improves small-only 3 to2. These are exact BFS outcomes within the large-lift model and rough-hit target, not global minimum crossing counts.

Six actual CRT roots constructed with complete final crossing and independently replayed using literal integer GCD at every tick. Rows (S,events,rough offset,final p,ticks,J decimal digits):
10,3,12,149,75,58;
20,6,30,463,241,194;
30,8,60,1049,549,440;
50,7,60,2593,1321,1095;
70,14,150,5087,2613,2175;
100,14,150,10211,5175,4395.
All prescribed events and actual least-GCD-prime labels matched and were adaptive-eligible. This replay used the small-only shadow plus a final high jump, not the optimized BFS word. Source consolidated in min_primorial_neighborhood_audit.py from the executed experiments. Requires Python 3.11+ and sympy. No Lean execution or novelty claim.

## 6. Next arithmetic target

Prove sub-(1/2)S crossing length or forced rough hit for unbounded S by controlling the single deterministic small-offset process, or exploit exact CRT choices to shorten paths where the raw defect exceeds S before a rough plateau. The small shadow empirical behavior is striking but depends on the actual primes around the visited offsets; finite CRT consistency does not itself force a rough offset. The m>=S/2-O(1) theorem under finite twins applies to all large lifts, so a uniform short-word upper bound would suffice. Do not infer this upper bound from the finite rows or from the number of abstract residue paths.
