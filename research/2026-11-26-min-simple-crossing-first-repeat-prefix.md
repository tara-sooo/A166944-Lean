# First-repeat prefixes and harmonic coefficient averaging

2026-11-26 JST. Continuation of 19303acfa4eaa01717d319fa995aaf6626ee2919.
This improves the mixed-window theorem in two ways: interior waits are
unrestricted, and the lower end of the label band is T/log^2 T rather
than T/log T. Uses only the anchor's roughness and the primorial bound
on low-label relays, not complete deterministic relay reconstruction.
Paper deductions and finite audit; no Lean verification or twin proof.

## 1. Parameters and statement

Use the previous common-boundary system of M=R/12+O(1) reset origins,
X in [R,3R/2], 6|X, state (X,X/2+3), exit at U>=2R. Count non-twin
waits only. On each path w<=2 min(p,q(u)), and total gain <3R.

For dyadic T tending to infinity put
    l=log T, m=log log T,
    A=T/l^2, U=T l^2, K=U/A=l^4,
    h=ceil(8l/m), W0=T/l^2.
Choose z as the largest prime with Q=2 product_(3<=p<=z) p<=l^(1/4).
For sufficiently large T this exists and z->infinity. Assume
    2 U^h <= sqrt R.
The preceding mixed-window product condition implies this one;
T<=exp((log R)^(1/3)) is one sufficient range for large R.

For an anchor p in [T,2T), w>=W0, consider the next h events
including itself in the sequence of ALL non-twin events p>z.
Call the window admissible if it exists and all h labels are in
[A,U]. There is NO lower bound on any interior wait and no phase
restriction. Consecutive high events are separated by a possibly
preempted small-label run. The primorial wall implies its physical
gain E_i is an even integer in [0,Q] even if the next high event
fires before the restricted run terminates.

Theorem. Uniformly on each actual path,
    W_admissible(T) << R (log log T)^4/log^(3/2) T.        (1)
Here W counts only the waits of anchors with admissible windows.
The bound requires neither small mass, a bounded number of distinct
labels, nor long interior waits.

## 2. Harmonic weighted pair sieve, summed over the coefficient

Write H=ceil(C h K) with any sufficiently large fixed C. For a
fixed nonzero integer c with |c|<=C h(U+Q), consider distinct primes
p,q in [A,U] satisfying q=a p+c, 1<=a<=H. Then uniformly in c,

    sum_(1<=a<=H) sum_(p,q as above) 1/(p q)
         << m^4/(A l^2).                                  (2)

Proof. Split p and q separately into dyadic intervals [s,2s),
[t,2t), intersected with [A,U]. Each has lower endpoint >=A/2,
and the number of intervals is O(m). For fixed a, the condition
on q confines p to an interval of length <=t/a, so the joint
interval of possible p has length <=min(s,t/a). Enlarge it to
an interval of comparable length min(s,t/a) if necessary.
This length is >= A/(2H) >= T/polylog(T), even for the largest
coefficient, since H=O(l^5). Use the explicit two-form Selberg
upper sieve of the inherited record-displacement-and-supply note
on p and ap+c in that interval. Omit primes dividing ac and
the prime 2, with cutoff floor(T^(1/40)). Remaining primes
exclude two distinct residues. Both actual prime values exceed
the cutoff. The remainder O(T^(3/20)) is absorbed. As in the
preceding mixed-window proof, |ac|<=T^C' with fixed C', so the
omitted Euler product costs at most O(m^2). Hence the count is
    << min(s,t/a) m^2/l^2.
The weighted count is at most
    << m^2/l^2 * min(1/t,1/(as))
    <= m^2/(as l^2).
Sum over a, using sum_(a<=H) 1/a=O(m); sum over t (O(m)
intervals), and over s using the geometric sum sum 1/s=O(1/A).
This proves (2). Crucially the coefficient loss is logarithmic,
not H or K. It works even when c is negative and q is much
smaller than p. No assumption of uniform prime distribution
beyond an upper sieve for two forms is used.

## 3. Count from the anchor, stopping at the first repeat

For any specified ordered high labels, orientations e_i in
{-1,1} and relay gains E_i in [0,Q], the source offsets are
x_i=x_0+sum_(r<i)(p_r-1+E_r). Eligibility imposes
x_i=e_i mod p_i. The distinct labels fix x_0 to at most one
residue class mod 2P, where P is their product. Since
2P<=2U^h<=sqrt R, the parameter interval has length
comparable to R/P>=sqrt R. The anchor wait >=W0 implies both
x_0+-1 avoid all odd primes below W0/2. On this source
progression sieve those two forms, cutoff floor(T^(1/40)).
All labels are >=A and hence coprime to the sieve primes.
The same explicit two-form upper sieve gives
    # sources per fixed compatible tuple << R/(P l^2).     (3)
Unlike the previous six-form sieve, this only needs the anchor
to be rough. It therefore tolerates arbitrary interior waits.
The relay enumeration costs at most (Q+1) per relay; no
phase variables are needed for this upper bound.

If all h labels differ, sum (3) over orientations, relay
gains and ordered prime tuples, using sum_(A<=p<=U)1/p
<< m/l. The anchor count is
    << R/l^2 * (C(Q+1)m/l)^h.
Since Q<=l^(1/4), the power is T^(-6+o(1)); multiplying
by 4T bounds this part of W by O(R/T^2).

Otherwise let k<h be the FIRST index of a repeated label
(zero-based). The prefix p_0,...,p_(k-1) contains k distinct
primes, and p_k=p_i for some i<k. Consecutive equal labels
are impossible: p_i would divide the nonzero odd integer
1+e_k-e_i-E_i of absolute value <=Q+3<A. Thus k>=2,
i<=k-2. Count ONLY this prefix, including its first repeat,
and not the rest of the word. This retains the original
anchor even if i>0 and the entire return has short waits.
By the congruences at the two equal labels,
    p_(k-1) = a p_i+c,
    c=k-i+e_k-e_i-sum_(r=i)^(k-1) E_r
                       -sum_(r=i+1)^(k-2) p_r.
Here a is a positive integer <=C k K. Indeed the interior
prime sum plus relay gains minus (k-i)+e_k-e_i is positive
for large T, and is an integer multiple of p_i. If c=0,
distinct primes p_i,p_(k-1) cannot satisfy the relation.
Fix i, all orientations, the k relay gains, and the other
k-2 distinct prime values. Then c is fixed, independent of
a and the pair. Its magnitude is O(h(U+Q)). Sum over the
two prime labels and a via (2); sum the remaining reciprocal
primes using the harmonic sum above. The source estimate
(3) is valid for each fixed compatible tuple. Combining
these nested counts (not multiplying independent probabilities)
gives an upper bound on the number of original anchor offsets
with first repeat at k:
    N_k << (R/A) k C^k (Q+1)^k m^(k+2)/l^(k+2).
The factor k counts possible i; the absolute C^k includes
orientation choices. The j-dependent coefficient range is
already absorbed in (2) using H. Sum the geometric tail from
k=2 because C(Q+1)m/l->0:
    sum N_k << (R/A)(Q+1)^2 m^4/l^4.
Every actual anchor occurs at a distinct source offset on
its path. There is NO need to charge a return occurrence to
h overlapping windows: the source counted is the original
anchor, with its own roughness and its entire distinct prefix.
Multiply by the anchor wait <=4T:
    W_repeat << R (T/A)(Q+1)^2 m^4/l^4
             << R m^4/l^(3/2).
This and the all-distinct part prove (1).

## 4. Global removal and residual lower interruptions

For all eligible dyadic T>=T0(R)->infinity, the sum of (1)
over bands and M origins is
    O(R^2/(log T0)^(1/4)) = o(R^2)
using m^4<=l^(1/4) eventually. The upper-interruption
charge from the preceding mixed-window note is unchanged:
a label p'>T log^2 T can be charged by at most h preceding
anchors at fixed T; dyadic summation pays O(p'/(log T0
log log T0)) for that occurrence, and the total gain
budget yields O(R^2/(log T0 log log T0)). Missing windows
cost O(R^(5/4) log R) over all origins, and short OWN
anchor waits cost O(R^2/log^2 T0). These are all o(R^2).
Thus the only obstruction at eligible scales not removed
by this result is a label z(T)<p'<T/log^2 T in the forward
window (after assigning upper obstructions first).
Short interior waits NO LONGER constitute a separate
obstruction; a low-interrupted window may of course still
contain short interior waits. Compared to the previous
mixed-window theorem the allowed interval is wider on
the lower side by a factor log T. Low relays with gains
<=Q are covered even when the small-prime path is
preempted. No bound on the total wait of lower-obstructed
anchors, or polynomial-scale anchors outside product room,
or anchors below T0, has been proved. Consequently this
does not establish the desired full W=o(R^2).

## 5. Executed finite audit

Source research/min_simple_first_repeat_audit.py at
7acdc48f9e9d8f1268fb6105ea7a76fa2a6fe18b,
blob c45ef525d7db41b86b51ff169302cff0616b3fa4.
Remote readback exact and local executed git hash matches.
Run:
    python research/min_simple_first_repeat_audit.py 1000 10000 100000 1000000
Stdlib plus inherited min_simple_crossing_audit.py.
Diagnostic z=3, h=4, A=T/4, U=8T, anchor wait>=max(7,T//8)
and A>Q+3, not the asymptotic parameters. Interior waits
unrestricted. All actual origin paths replayed; checked
the gain bound for every intervening small run, the first
repeat's original-anchor CRT, prefix linear relation,
dyadic pair interval constraints, and tuple source counts.
At R=10^6 the graph totals agree with earlier audits:
83334 origins, 2564511 non-twin visits, total wait 66822800.
For the diagnostic anchor population:
    anchors                  233398
    anchor wait             49479900
    own short wait            337601
    missing window           6812438
    upper interruption        600669
    lower interruption      41509212
    admissible window         219980
    admissible windows          2465
    all distinct               2388
    first repeat at index 3       77
    repeats with i>0              77
    windows with short interior 1106
    their anchor wait          71036
117 distinct prefix tuples. At R=10000 there were 5
admissible windows, all with short interiors; at R=100000,
26 windows, 9 with short interiors. R=1000 had no anchors
under the diagnostic cutoff. All checks passed. The
audit tests necessary arithmetic and the charging classes;
it does not numerically verify the asymptotic sieve or the
growing-h product condition. The diagnostics differ from
the preceding audit also in band width and eligible bands,
so the absolute populations cannot be compared directly.

Next: the lower-interruption class remains the main obstacle
within the covered scales. A bound on long relays or a new
mixed-scale counting mechanism that tolerates truly small
intervening labels is needed. No twin-infinitude proof
or Lean kernel verification.
