# Compressed reverse ancestry and a local scale barrier

2026-11-26 JST. Continuation of 0ae7f24a31bf9647559db95c5e5a8a72bf27a65a.
Focus: control high-deficit transport across actual roots, rather than
adding further local macro classifications. Paper estimates using the
inherited two-form upper sieve, plus an executed finite diagnostic.
No Lean kernel verification, novelty claim, or twin-infinitude proof.

## 1. Offset-only inverse edges

For an ordinary MIN event x -> U=x+p-1, write e=+1 on
the minus-neighbor/even side and e=-1 on the plus-neighbor/odd
side. Since p divides x-e,

    p | U     if e=+1,
    p | U+2   if e=-1.

Given U and a candidate odd prime from either factorization,
the predecessor offset is exactly x=U-p+1. The phase is not
specified, so this is an upper graph, not a claim that all
candidate edges occur. Counting this graph bounds every actual
history, regardless of clock phases or merger multiplicity.

For a finite small alphabet of all odd primes <=y, put
Q=2 product_(3<=p<=y) p. The inherited primorial wall shows
that any consecutive low run has gain <=Q and wait <=3Q.
Indeed within an even cell no eligible step of gain p-1
can cross its next multiple of Q, and at that multiple no
such prime is eligible. Chebyshev gives log Q=O(y).
For y=11 the previous exact table improves these constants
to gain 104 and wait 133. Use the general Q bound below.

Suppose an endpoint offset lies in [R,3R) and the entire
prefix from its starting offset is there too. If there are
at most k non-low events, compress every intervening low run
to one displacement in [0,Q]. Starting at the endpoint,
choose a backward low displacement (at most Q+1 options),
then a prime factor of the resulting offset or its value
plus 2. Repeat at most k times, ending with one low run.
If all encountered offsets have inverse degree at most B,
the number of possible starting offsets is bounded by

    A_k(B)=(k+1)(Q+1)^(k+1) max(1,B)^k.             (1)

This includes arbitrary numbers of low events and all
initial phases. If only a subset of paths has low degree,
apply (1) to that subset; do not assume all paths from a
given offset are good. Each compressed low displacement
need not be realizable, which is harmless for an upper bound.
There is no assumption of independent successive clocks or
of small actual basin mass.

## 2. Exceptional inverse degrees

Let z=log log R and B=ceil(z^2), for sufficiently large R.
For an even offset U define deg(U) as the number of inverse
candidate side/prime pairs, at most omega(U)+omega(U+2).
Uniformly deg(U)=O(log R) in [R,3R).

By 2^omega(n)<=tau(n) and sum_(n<=4R) tau(n)=O(R log R),
the number of offsets in [R,3R) with deg(U)>B is

    O(R log R * 2^(-B/2)).                          (2)

If a prefix with at most k non-low events hits any such
offset, its starting offset is counted by reverse ancestry
from that offset using A_k(C log R). This counts offsets,
not just state groups, so covers every possible starting phase.

Take y=floor(z^(1/8)), m=floor(z^(1/2)), and k=O(z^(3/4)).
Then log A_k(B)=O(z^(7/8)+z^(3/4) log z)=o(z), whereas
log A_k(C log R)=O(z^(7/4))=o(z^2). Combining (1)-(2),
the number of starting offsets from which any such prefix
can reach a large inverse degree is

    O(R exp(-c z^2))                                (3)

for some c>0. All other prefixes with these budgets use
only small inverse degrees, and any endpoint has at most
exp(o(z))=(log R)^o(1) possible origins among those prefixes.
This is an actual compressed-ancestry bound for local
histories, rather than a bound on long stable cohorts
entering the interval from arbitrary distant origins.

## 3. Uniform early high-wait scarcity at multiple scales

Fix 0<epsilon<1 and let a scale T satisfy

    exp((log R)^epsilon) <= T <= sqrt R.

Take D=ceil(T z^(3/4)); low labels p<=y, medium labels y<p<T,
and high labels p>=T. On any prefix with pre-offset
u<X+D starting at X in [R,2R), the number of HIGH events
strictly before u is <=D/(T-1), by gain telescoping.
If at most m medium events precede u, the total number
of non-low predecessors is <=k=m+ceil(D/(T-1))=O(z^(3/4)).
Thus section 2 applies, uniformly in T. Note that it does
not bound the label of the last event that exits the window.

Call a high event significant if w >= (p-1)/log T.
Every odd prime factor q of either neighbor has clock
wait <=2q, so significance forces q >= (T-1)/(2 log T).
The number of even offsets in [R,3R) with this roughness
is O(R/log^2 T). For example apply the inherited two-form
Selberg upper sieve to u-1,u+1 with cutoff floor(T^(1/20)),
two distinct roots at every odd sieve prime, error O(T^(3/10))
absorbed by the main upper bound. The inherited local
label-diversity note uses the same explicit weights and
Mertens/Chebyshev truncation; this simpler application
sieves u itself, not a cofactor. Twin offsets also satisfy
roughness; they may be included in this upper count.

Let E(R,T) be the set of starting offsets X in [R,2R)
for which ANY envelope-valid starting phase has an actual
prefix containing a significant high event at u<X+D,
with at most m prior medium events. We can even include
non-envelope phases in the upper graph. For paths passing
through a large-degree offset use (3). For remaining paths,
reverse from each rough source using (1) with B. Therefore

    |E(R,T)| << R exp(-c z^2)
             + (R/log^2 T) exp(o(z))
             <= R exp(-(2 epsilon-o(1)) z).         (4)

This is uniform over the displayed scale interval. The
little-o in the exponent is bounded explicitly by
O(z^(7/8)+z^(3/4) log z); constants can depend on epsilon.
For T=ceil(sqrt R/z^(1/2)), (4) strengthens to

    |E(R,T)| <= R/(log R)^(2-o(1)).                  (5)

The upper bound covers ALL actual origins/initial phases
of the specified prefix type, with no independence or
no-merger assumption. It is not restricted to paths staying
in the core d=0,6 or following macros. It covers arbitrary
high-deficit excursions within the prefix budget.

Moreover choose any O(z^A) deterministic scales in the
displayed interval, for fixed A. A union bound still
gives o(R) exceptional starting offsets. In particular
one may take polynomially many in log log R logarithmic
scales. At every remaining start the same exclusion holds
simultaneously, with the medium count defined separately
for each scale. These counts cannot be added across scales:
the same events may pay more than one scale requirement.

## 4. Actual path consequence: high-band persistence is not enough

Consider an ordinary path from X outside E(R,T), starting
with 0<=d0<=C T for fixed C (canonical resets d0=6 included),
and satisfying the envelope along its history. Stop at the
first arrival >=X+D or just before the (m+1)-st medium
event, whichever comes first. Before that stop every high
event is insignificant. Its wait is <g/log T where g=p-1.

Low events occur in at most k+2 runs, including a possible
final low event; their total wait <=3Q(k+2)=o(D).
Medium wait <=2Tm=o(D), since m/z^(3/4)->0.
For a final exiting event, prior gain <D and
d_pre<=d0+5D (because w<=2p<=3g).
If the final event is high, d_post>=0 and insignificance
give (1-2/log T)g<=d_pre, so g=O(D), even when its
label is much larger than sqrt R. If the final event
is low/medium its gain is <=T. In either case the total
gain up to this stop is O(D). Consequently total high
wait is O(D/log T)=o(D). Thus ALL waits before this stop
sum to o(D).

If this stop were a full local crossing, the envelope
would force W >= (D-d0)/2=(1/2-o(1))D, a contradiction.
Therefore, outside the exceptional set, any full local
crossing from such a phase must contain at least m+1
medium events. If the path is stopped at a twin source
instead, that is a separate permitted terminal outcome.
In particular no non-twin path can transport an initial
high deficit O(T) through distance D using only low and
high bands at a typical starting offset. This conclusion
does not require eventual return to the core or short
individual high excursions.

For T near sqrt R, D is sqrt R times z^(1/4), and
an initial long departure with label comparable to T
has d0=O(T) at arrival. Thus the estimate applies to such
arrivals if their positions are outside E. HOWEVER these
arrival positions are an arithmetically selected set,
possibly concentrated in E. The typical-offset result
does NOT yet control their distribution. Nor does it
bound the number of medium events on the full trajectory.

For canonical reset roots, (4) also gives a limited
origin-weighted flux estimate. At the near-sqrt scale,
stop each path before the first twin event, the
(m+1)-st medium event, or the local exit. For good
roots the full wait is o(D) as above. At exceptional
roots, all non-twin waits except the last cost <=3D
by telescoping, and the last wait <=2 sqrt(3R+1)=O(D).
Hence the sum of all waits up to these stops over
ALL roots X=0 mod 6 in [R,2R) is o(RD).
This is an unconditional removal of early-prefix traffic,
including high-deficit traffic and arbitrary mergers.
It does not bound the remaining traffic after the medium
budget is exhausted. At much smaller T the last-event
sqrt R bound need not be O(D); do not claim the same
untruncated aggregate flux estimate for those scales.

## 5. What this changes, and what it does not

The earlier studies tried to bound high-deficit persistence
uniformly on a single path. The reverse method instead
bounds the starting offsets of high-wait prefixes, allowing
arbitrarily many repetitions of low labels, arbitrary
phases and a growing number of medium/high events.
It does not assume an upper bound on excursion duration.

The result isolates a residual population: either many
medium events have already occurred, or the origin is
in a thin, explicitly defined exceptional set. In
particular, a strategy demanding few medium events for
a positive density of roots at these scales is not
compatible with the typical-offset theorem (unless the
paths are stopped before crossing, e.g. at twins).
This is a genuine obstruction as well as a reduction.

To prove twin infinitude one needs another argument:
either bound the remaining medium-dense traffic, establish
a mechanism to repeatedly restart the compressed-ancestry
budget while controlling the distribution of arrival offsets,
or construct unbounded favorable exceptional roots without
assuming twin labels. Equations (4)-(5) are UPPER bounds
and do not provide that existence. It would be circular
to treat a small exceptional set as an abundant source.
No control of all long stable mergers has been established.

## 6. Executed diagnostic

Source research/min_local_reverse_ancestry_audit.mjs,
commit 27edfeb6e1558a654cb615b0d04c0133615d45bf,
blob 092d201b49463b2c6b14b9b40e6d964f56b8cf72.
Run node research/min_local_reverse_ancestry_audit.mjs 1000000.
Actual ECMAScript execution in research runtime; fetched by
exact commit and re-executed with identical output.
No Node process or Lean process invoked here.

For finite diagnostic parameters y=11, m=4,
D=ceil(4 sqrt R), T=ceil(sqrt R/2), significance
8w>=p-1, all multiples of 6 in [R,2R), ordinary
MIN stopped before the first twin event or local exit:

    R         roots   events    non-twin exits   early significant roots
    10000      1667     20276       315                 669
    100000    16667    325650      1532                5130
    1000000  166667   4986626     10928               32435

Early significant source offset counts: 128,643,3628.
Largest observed multiplicity of distinct roots at one
early significant OFFSET (not necessarily same phase):
47,76,84. For the two largest carriers in each slab,
independent compressed reverse enumeration with low
displacements <=104, high budget ceil(D/(T-1)) and
medium budget 4, ignoring phase, includes every actual
root. Example R=1000000,u=1605168: 84 actual roots,
667 reverse-candidate roots, 18703 compressed search
states. These relaxed bounds can be loose.

Low/medium-capped non-twin exits: 101,118,186;
of them 95,118,186 had an early significant high event.
These finite parameters are NOT the asymptotic
choices in sections 2--4, so these observations are not
counterexamples to the theorem or tests of its rates.
Early high wait 57532,1289075,23980482; total high
wait 66140,1924748,52410909. In particular later
medium-dense traffic is material in the diagnostic.
All 5,332,552 actual reverse identities, 3,786,451
small-relay controls, 14,361 literal GCD ticks and
six independent reverse-ancestor carrier controls passed.
The initial script attempt used an SPF array too short
for final overshooting offsets; it was corrected before
the successful commit, with explicit domain checks.
All counts overlap by shared trajectories, not
independent samples. No measured asymptotic constant.

No canonical Lean target or sibling branch changed.
