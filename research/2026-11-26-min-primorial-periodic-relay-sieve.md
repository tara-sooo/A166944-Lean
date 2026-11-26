# Periodic terminal maps remove the primorial relay-length loss

2026-11-26 JST. Continuation of bec04bea05f0064f1904155f546a663f778fd709 (dense source-only pair sieve), and 559544a638c8e35301170b759c714dd4be65c1d0 (growing-depth transport). Paper deductions and separately executed finite clock audit. No Lean verification, external novelty claim, or proof of twin infinitude. No formal target or canonical branch changed.

## 1. Restricted terminal map, valid for arbitrarily many low events

Use the ordinary uncut offset MIN, u even, v current time, p odd prime label, sign e=+1 for minus or e=-1 for plus, x=pk+e. A genuine event updates (u,v) -> (u+p-1,v+w). Fix an integer B>=3 and define

    Q=2 product_(3<=q<=B, q prime) q, R=2Q.

Define the restricted MIN by retaining only eligible labels <=B, minimizing the same pair (wait,label), and stopping if there is no eligible retained label. This restricted process is an auxiliary deterministic computation, not an assertion that every actual path follows it indefinitely. It depends only on u mod Q and v mod Q because 2q divides Q for every retained label.

A retained event cannot strictly cross a multiple J of Q: if its source x<J is even, J-x is positive even and congruent to +/-1 mod q, hence >=q-1; at x=J no retained label is eligible. Thus the restricted process from u in [jQ,(j+1)Q) terminates in that cell, with gain Delta_B(u,v)<=Q and at most Q/2 events. The entire relative endpoint (gain,elapsed time,event count) is periodic in (u mod Q,v mod Q).

If an actual path starts at (u,v), uses only labels <=B up to its first label p>B, and that departure has w>2B, then all the preceding events agree with the restricted MIN, since at each such event the true minimizer belongs to the restricted set. At the departure source there cannot be any eligible retained prime, since its clock would fire within 2B ticks. Thus this source is precisely the restricted terminal. In particular the first high source offset is u+Delta_B(u,v), without any hypothesis on the number of preceding events. Its time is also determined by the same map. This identity does NOT hold for every first p>B: if w<=2B, the full MIN may select a high label before the restricted terminal.

For a reset (X,X/2+3), X a positive multiple of 12, the restricted terminal gain depends only on X mod R. More generally for any fixed source deficit d, v=(u+d)/2, it depends only on u mod R. Thus on each starting residue class a the source offset at the high departure is a fixed translation of the starting offset, preserving its progression length and modulus R.

## 2. Uniform progression sieve with the small primes already fixed

Let Y tend to infinity, C>2 fixed, and take B=floor(c log Y) for a fixed sufficiently small c>0 so that Q<=Y^(1/8) for large Y; the elementary Chebyshev bound log Q=O(B) permits this. The modulus R includes every odd prime <=B. Take thresholds

    T_i=exp((log Y)^theta_i), 0<theta_i<1,
    
or T_i=Y^epsilon_i with fixed positive epsilon_i (or more generally thresholds for which log T_i/log B -> infinity). In the two-threshold estimates take T1>=T2 and p>=T1. B tends to infinity and T_i>8B+8 eventually.

Consider a first high departure with p>=T, w>=p/4, non-twin source, and source offset x<=CY. Call this a strong departure. All prime factors q of both neighbors have q>=w/2>=p/8 by the competing clock bound. At a non-twin source some neighbor is composite, so p<=8sqrt(CY+1). In particular x=pk+e with k positive, and k, pk+2e have no odd prime factor below p/8. The bound also holds for any pre-first-record departure satisfying w>=p/4, since its source cannot be twin. Here p>B is coprime to R.

Fix p,e and a residue x=a mod R. The cofactor k runs on one class modulo R in an interval of length N=O_C(Y/(pR)) (enlarge to length comparable to Y/(pR) for the upper bound). Because R<=2Y^(1/8) and p<=8sqrt(CY+1), this length is >>_C p^(3/4). On the new progression parameter the two forms have two distinct roots at every prime ell>B with ell<p/8, ell!=p. Take sieve indices <=z=floor(p^(1/12)), omitting all primes <=B. The explicit Selberg construction in the previous dense-pair and record-supply notes has weights |lambda_d|<=d, residue count error O(rho(d)), rho(d)<=d, and total error O(z^6)=O(p^(1/2)). Its reciprocal main quadratic form is >= a fixed positive fraction of the Euler product on primes B<ell<=z^eta for sufficiently small fixed eta>0: under the normalized product weights the mean log d is O(log z^eta), and Markov retains half the weight at d<=z. Mertens then gives a lower bound >> (log p/log(2B))^2 for the reciprocal main form. The error is absorbed since N>>p^(3/4). Consequently for each fixed progression, source label, and sign the two-form candidate count is

    O_C(Y/(pR) * log^2(2B)/log^2 p).                   (1)

All constants are uniform in the progression, including nonreduced offset residues. The parameter step R is invertible at every sieve prime retained; no assertion of distribution of primes in progressions modulo R is used.

For the four-form variant let y=x+D, where D=p+E-1, 0<=E<=Q, and fix E separately on each progression and for each p,e (it can vary arbitrarily between progressions). Suppose both y+-1 have no odd prime factor below T2/8. Impose the previous four forms k, pk+2e, pk+e+D-1, pk+e+D+1 at ell<T2/8 and just the first two at larger sieve primes. For ell>B the number of distinct roots for all four is 4-nu_ell with nu_ell=2*1_(ell|D)+1_(ell|D-2)+1_(ell|D+2). This is the exact local density from the preceding dense-pair note; the first two forms still have two roots. For sufficiently large Y, all three integers D,D+-2 are positive and their product is Y^O_C(1), since p<=8sqrt(CY+1), E<=Q. The contribution of prime divisors ell>B to the singular factor is bounded uniformly in p,E:

    sum_(ell>B, ell|D(D-2)(D+2)) 1/ell
      <= log(D(D-2)(D+2))/(B log B) = O_C,c(1/log B).

Thus the exceptional Euler factors cost a bounded constant; no averaging over p or E is needed. Omitting all primes <=B removes their entire singular contribution. The same truncated Selberg product gives reciprocal main form

    >>_(C,c) (log p/log(2B))^2 (log T2/log(2B))^2,

because log min(z^eta,T2/8)>>log T2 when p>=T2, and log T2/log B -> infinity. The same error O(p^(1/2)) is negligible against N/log^4 p. Hence on EACH fixed residue class, with its individually chosen E, the count is

    O_(C,c)(Y/(pR) * log^4(2B)/(log^2 p log^2 T2)).   (2)

The uniformity in E is crucial: it is not necessary to sum over E in [0,Q]. These estimates do not claim lower bounds or reachability of the sieve candidates.

## 3. Arbitrary-depth first-departure transport

Take integer reset origins X in [Y,2Y], X=0 mod12. Their first event with p>B exists by the finite-alphabet wall argument (the actual uncut offset MIN always has an eligible future clock). Consider those whose first p>B is non-twin, p>=T, w>=p/4. Since T>8B+8, w>2B and its source is the restricted terminal. For each origin residue modulo R, its high source is a fixed translate; use (1) on that one residue, summing over p and signs. By the Chebyshev upper bound on primes in dyadic intervals,

    sum_(p>=T) 1/(p log^2 p) << 1/log^2 T.

Thus the number of qualifying origins in EACH fixed residue class is at most O_(C,c)(Y/R * (log(2B)/log T)^2), uniformly in the residue; here x<=2Y+Q<=CY eventually. Sum over at most R classes to obtain

    # origins <<_(C,c) Y (log(2B)/log T)^2.           (3)

There is NO bound on the number of small events, and no fixed-deficit strip assumption. The key improvement over a crude terminal-basin estimate is the factor 1/R in the progression sieve, which cancels the number of initial residue classes. It replaces a potentially enormous primorial factor by a log^2 B cost.

In particular for fixed epsilon>0 choose c sufficiently small that Q<=Y^min(1/8,epsilon/2), and T=Y^epsilon. Up to the first label >B the total gain is <=Q, and the deficit is <=6+5Q by w<=2p and delta d<=3p+1<=5(p-1). For a p>=T departure the postdeficit is nonnegative, hence w>=(p-1-d)/2>=p/4 for large Y. Thus the strong-departure hypothesis is automatic. We conclude

    # seeds with non-twin first p>B and p>=Y^epsilon
       <<_(epsilon,c) Y (log log Y/log Y)^2.          (4)

This is unconditional over arbitrary integer resets, not just the distinguished ray. It does not count a twin-derived departure as bad. It also does not assert that the first label >B is the first label >r_seed. In a hypothetical finite-twin universe, (4) means most of these small-label prefixes must exit via intermediate labels below Y^epsilon; this is not a contradiction. For subexponential T one may instead assume the strong wait or a deficit bound d<=T/2-1 at the departure (or choose B smaller, with a corresponding revised uniform singular factor for pairs).

## 4. Two high departures separated by arbitrarily many small events

Consider a strong first event at source x=pk+e in [12,CY] with p>=T1, and suppose its arrival is singular: d'=0 at an even tick or d'=6 at an odd tick. Thus its arrival is (U,V)=(x+p-1,(x+p-1+c_e)/2), where c_e=0 for e=+1 and 6 for e=-1. Suppose the next event with label >B, after any number of <=B events, has label r>=T2 and wait >=r/4. It need not be immediately adjacent to the first event or the next singular return: the intervening small events may themselves return to singular states many times. The second event has wait >2B, so its source is the restricted terminal from (U,V). Therefore

    E=Delta_B(x+p-1,(x+p-1+c_e)/2)
    y=x+p-1+E.

For fixed x mod R, p,e this E is fixed. Its range may be as large as Q, and we do not sum over it. The second departure's clock competition gives both y neighbors rough at primes below r/8>=T2/8. It may even be twin-derived: only its roughness is needed, while the first event must have non-twin source to obtain p<=8sqrt(CY+1).

Apply (2) for every source residue class, with the E determined by that class and p,e. Sum over at most R residues, signs and p>=T1. This bounds the number of distinct triples (x,p,e) with such a genuine pair by

    O_(C,c)(Y log^4(2B)/(log^2 T1 log^2 T2)).         (5)

This counts source-offset/first-label/sign triples, not all source times or physical gain. Compared with the preceding four-form estimate for a relay of arbitrary gain E<=Q, its factor Q+1 is gone, at the cost log^4(2B). The actual length in events of the relay is unrestricted. We allow intermediate labels <=B only; events with label in (B,T2) are not covered.

In particular, count reset origins whose FIRST TWO labels above B satisfy the pair hypotheses, with p>=T1, r>=T2. Before the first event all actual labels are <=B, and its source is itself the restricted terminal of the initial reset (section 1). For each starting residue modulo R this is a fixed translate; we use (2) directly on that translated class, with E again fixed for every p,e. Sum over origin residue classes rather than source classes. Even if different classes map to the same high-source class, each contributes only its own origin count bounded by the same Y/(pR) estimate. Therefore (5) holds for the number of such reset origins as well, without needing a separate bound on merger multiplicities or depth. For starting states on either singular row the same argument counts origins on that row, since their times are fixed affine functions of the offset.

With T1=T2=Y^epsilon and c chosen as in (4), both departures automatically have strong waits if they originate in a low-label prefix from a singular state: the initial deficit is 0 or 6 and the prefix gain <=Q. For the first departure assume non-twin; for the second no non-twin hypothesis is needed. Thus the number of integer reset origins in [Y,2Y] whose first two labels >B are both >=Y^epsilon, with first departure non-twin and its arrival singular, is

    O_(epsilon,c)(Y (log log Y/log Y)^4).             (6)

For this assertion take C fixed sufficiently large, since the first high gain <=8sqrt(CY+1) and the intervening small gain <=Q imply both source offsets are <=CY. More generally for arbitrary low-label prefixes with bounded starting deficit the strong-wait condition may be checked directly. Equation (6) removes any bound on the number of intervening singular returns as long as their labels remain <=B. It is a seed-count upper bound, not a bound on the total physical gain or on the number of all high events in a path.

## 5. Executed finite arithmetic audit

Source research/min_primorial_periodic_relay_audit.py, commit 4c8770c11eab9c629beb13808deaed87f90a90dd; remote blob 1d2d7f608a9847423db7f430a571ed3a8e689191 equals the locally executed git hash-object. Requires SymPy and sibling min_primorial_record_supply_audit.py. Run:

    python research/min_primorial_periodic_relay_audit.py 100000

All 16,666 integer reset seeds r=7,13,...,99997, stopping before their first label >r, were scanned at each B=3,5,7,11,19. The finite diagnostic uses T=max(17,8B+8), not the asymptotic parameter choice.

    B     Q         terminal matches   strong pairs   max relay gain   max first strong prefix gain
    3     6         111419             1435           2                0
    5     30         69132             1052          14                6
    7     210        50767             1092          26               24
    11    2310       35641              571          42               66
    19    9699690    23043              376          84              132

Total 290002 exact comparisons of restricted terminal gain, elapsed time and event count with actual small-label prefixes whose next wait is >2B. All passed, including translations by a multiple of the period. 4526 strong ordered pairs with singular first arrival and all relay labels <=B passed the exact relay reconstruction. 12882 rough-form exclusion checks passed. The thresholds and seeds overlap; these are not counts of independent samples.

Example at B=19 from seed r=51565: source x=103320, first label 277, next >B source y=103680, second label 521. The intervening relay has physical gain 84 over 16 small events; the endpoint is determined by the residue of x+276 and the singular arrival phase. The maximum first strong prefix gain at B=19 was 132 over 16 events, at r=96325, first high source 192780 and label 733. This audit verifies the deterministic reconstruction and arithmetic exclusions, not the asymptotic upper bounds or a general first-record displacement estimate.

## 6. Remaining mathematical issue

The primorial-length loss has been removed for complete low-label runs ending in strong high departures, including two such departures separated by arbitrarily many low-label singular returns. The estimates count origins in a macroscopic slab without controlling their full ancestor depth. They leave open paths with repeated intermediate-label departures, non-singular arrivals of high labels, or high labels selected with small wait at high deficit. In particular, no upper bound on the full pre-record displacement G(r) or proof that unboundedly many resets meet the earlier short-displacement certificate has been obtained. No Lean kernel verification performed.
