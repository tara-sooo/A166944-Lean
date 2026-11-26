# Negative MIN: relay packing energy and bandwise capacity

2026-11-26 JST. Continuation of 755b0ce765ea1ba03f3c168d2b26e8d3680e07ec.
Eliminate the uniform short-relay cutoff from the consecutive-high
pair bound. Obtain a quadratic lower bound on accumulated relay gain
using actual ordered pair keys, and extend it to bands interrupted by
larger labels. These are deterministic paper deductions and executed
finite controls, not a general extinction theorem or Lean proof.

## 1. Fixed-key packing cost

Consider a contiguous block of actual completed negative-MIN events
read in forward orientation, decreasing positive even distance.
Sources lie in an integer interval of length D contained in [R,2R).
As before assume non-twin sources, so w<=2 min(p,S) with
S=sqrt(2R+1). Mark labels >=T>=5 (or the band [T,U) in section 4).
For consecutive marked sources a,c and labels p,r, let the
intervening gain be E>=0 even. With source signs e,f in {-1,1},

    c=a-p+1-E,
    a=e mod p,
    a=p-1+E+f mod r.

When p=r, necessarily E>=p-1 (755b0ce). Therefore the total
wait W_= charged to the first event of same-label pairs satisfies

    W_= <= (5/2) G_=,

where G_= is their total relay gain; use 2p/(p-1)<=5/2.
This handles all such pairs without discarding long relays.

For p!=r group the pairs by the ordered key g=(p,r,e,f),
NOT by E. Every fixed E contributes at most

    c_g=floor((D-1)/(2pr))+1

occurrences to that key. This follows from the spatial CRT
modulo 2pr and monotonicity, as in the preceding note.
The same bound holds for a fixed E modulo r, though only
the fixed-E bound is needed below.

Let n_g be the number of occurrences, G_g the sum of their
relay gains. Write n_g=c_g m+l, 0<=l<c_g. Filling the available
slots with the cheapest even relay gains first gives exactly
the packing lower bound

    G_g >= c_g m(m-1)+2ml >= n_g^2/c_g-n_g.         (1)

The first inequality does not assert that this packing is
realizable by MIN; it relaxes all other constraints. The
difference between the two right sides is l(1-l/c_g)>=0.
The bound holds also when E is arbitrarily large.
In particular G_g>= (n_g-c_g)_+^2/c_g.
Here x_+=max(0,x). If a particular key has smaller spatial
span d_g=max(a)-min(a), one can instead use the smaller
capacity floor(d_g/(2pr))+1. This uses only that key's
actual source positions, and does not require their
intervals to be disjoint for different keys.

## 2. Weighted relay energy and observed transition graph

Let s_g=min(p,S), and let W_g be the sum of first-event
waits for that key. Since W_g<=2s_g n_g, (1) implies

    G_g >= (W_g-2s_g c_g)_+^2/(4s_g^2 c_g).       (2)

One can also use any smaller independently valid uniform
wait cap for the group. Equivalently

    W_g <= 2s_g c_g+2s_g sqrt(c_g G_g).

Only keys that actually occur need be included. Put

    A_* = sum_g s_g c_g,
    B_* = sum_g s_g^2 c_g,
    G_ne = sum_g G_g,
    W_ne = sum_g W_g.

The inter-mark relays are disjoint, so there is no
double charging of their gain among keys. Summing (2)
and using Cauchy-Schwarz gives both

    sum_g (W_g-2s_g c_g)_+^2/(4s_g^2 c_g) <= G_ne,
    W_ne <= 2 A_* + 2 sqrt(B_* G_ne).              (3)

If B_*>0, equivalently

    G_ne >= (W_ne-2 A_*)_+^2/(4 B_*).

When no distinct pair occurs, both W_ne and B_* are zero,
and the non-divided inequality is used. These bounds charge
actual ordered transitions and signs, not all L(L-1) pairs
in the support. They give a quantitative necessary cost of
recycling a sparse transition graph.

For all marks >=T, let G_low be total unmarked gain in the
block, W_low the corresponding wait, G_relay=G_=+G_ne.
Then G_relay<=G_low and W_low<=3G_low. The last marked wait
is <=2S. Consequently total completed-event time satisfies

    W <= 3G_low + (5/2)G_= + 2A_*
                  +2 sqrt(B_* G_ne)+2S
      <= (11/2)G_low+2A_*+2 sqrt(B_* G_low)+2S.     (4)

The first line is sharper when initial/final low runs
are large. Unlike 755b0ce this estimate has no relay
cutoff B<T-1 and no separated-alphabet hypothesis.
It does not assert that G_low is small.

If J is the number of occurring ordered distinct keys,
uniformly

    A_* <= J (D/(2T)+S),
    B_* <= J (DS/(2T)+S^2),

using s_g<=p,S and r>=T. Also J<=4L(L-1), where L counts
distinct marked labels. Keeping the exact observed J and
actual p,r yields potentially stronger estimates.

## 3. A conditional top-scale obstruction without a support gap

Take D=R, T comparable to sqrt R, with constants fixed.
Then A_*=O(J sqrt R), B_*=O(J R). If W>=eta R for
fixed eta>0, and J=o(sqrt R), (4) implies that either
G_low is already a fixed positive fraction of R, or
J G_low is at least a positive constant times R.
In detail, for large R the A_* and S terms are o(R).
If G_low<eta R/22, the (11/2)G_low term is <eta R/4;
the square-root term must then be at least eta R/2.
This gives J G_low >>_eta R. If J=0, the first alternative
is necessary. Thus for J>=1 the necessary bound is

    G_low >>_eta R/J,                              (5)

under the stated J=o(sqrt R) and macro-time assumptions.

In particular a sparse-support path with
L=o(R^(1/4)) and G_low=o(R/(1+L^2)) cannot
carry W>=eta R. This replaces a uniform primorial
gap condition with a total lower-label gain condition.
It is not automatically stronger numerically than
optimizing the earlier short/long split in every regime;
the exact per-key packing and weighted energy are new,
and need no bound on individual relay length. If the
actual transition graph has much fewer edges than L^2,
the graph version is more useful.

## 4. Bandwise version, with higher events as separators

Choose 5<=T<U<=2T. Break the block at every event with
label >=U, then within each remaining component mark
only [T,U). Between marks there are only labels <T.
Let N_hi be the number of separating higher events,
G_<T total gain of labels <T in the original block.
All within-component inter-mark relays are disjoint
even when combined across components. Group all their
distinct ordered keys together across the entire slab.
The CRT bound c_g is still valid because the first
sources remain distinct. Do not count the separating
higher-event time as band time.

Write W_band for the total waits of labels in [T,U).
Every component has at most one last mark; each such
wait is <=2 min(U,S). The same packing argument gives

    W_band <= (5/2)G_=+2A_*+2 sqrt(B_* G_ne)
                          +2 min(U,S)(N_hi+1),     (6)

with G_=+G_ne<=G_<T. For this band,

    A_* <= J(D/(2T)+2T),
    B_* <= J(D+4T^2),

since s_g^2/(2pr)<=p/(2r)<1.
Thus for D=R, T<=sqrt R, A_*=O(J R/T),
B_*=O(J R). If W_band>=eta R, J=o(T), and
T(N_hi+1)=o(R), then (6) forces
G_<T >>_eta R/J when J>=1. If J=0, G_<T must
itself be macroscopic. The condition on separators
follows, for example, from o(R) total gain of labels
>=U since N_hi(U-1) is at most their total gain.
The statement requires T=o(R), already true here.

This gives a hierarchy of local inequalities without
a fixed gap between selected bands and all smaller
labels. For one band all its relay charges are disjoint.
For DIFFERENT bands they can overlap, so summing the
G_<T or G_ne across bands as if disjoint would be wrong.
A bound on the actual sparse graph sizes, or an
assignment of relay charges preventing this overlap,
is still needed for a general multi-scale argument.
Neither the top-scale time fraction nor small lower
gain is implied by finite twins.

## 5. Executed diagnostic and persistence

Source research/min_local_negative_relay_packing_energy_audit.mjs,
final commit c9698914b201a6243ce3c2dbf083eb5243de058d,
blob e21b399671e33486c24d18ce5b3a8ba3b407ec0e.
Executed as ECMAScript in research runtime, fetched at
exact commit and re-executed with identical output.
Reproduce:
node research/min_local_negative_relay_packing_energy_audit.mjs
No separate Node or Lean invocation.

Test 400 initial-distance/phase controls in R=10000,40000,
120000,250000. Per slab 25 canonical negative seeds and
75 noncanonical initial phases (0,17,floor(A/5)).
Positive-time noncanonical controls deliberately exercise
different clocks and are not negative canonical samples.
Stop canonical prefixes before tick zero, split at twin
sources, retain actual contiguous non-twin blocks.
For each block use five thresholds (5,11,23,floor(sqrt R/4)
with minimum 5, floor(sqrt R)), both all labels >=T
and band [T,2T). Some identical thresholds are allowed
as repeated controls.

    actual event evaluations              7558
    contiguous non-twin blocks             376
    canonical-negative blocks               94
    noncanonical phase blocks              282
    threshold/band controls               3760
    ordered distinct-key incidences       8510
    keys with multiple occurrences         267
    distinct-label pair incidences        8847
    same-label pair incidences             136
    fixed-E capacity checks               8613
    group energy and weighted checks      8510 each
    whole-control decomposition checks    3760
    local-span strengthened checks        8510

All assertions passed. Global full-slab capacities were
loose in these samples: no group had positive minimal
packing cost with D=R, and no aggregate W_ne>2A_*.
The local-span capacities yield 18 keys with positive
packing cost, including 10 with strictly positive weighted
energy using s_g=min(p,S). Using the actual maximum
wait/2 as a diagnostic cap gives 18 positive weighted
energies; that cap is not an independent prediction of
unseen paths. This limitation is explicitly retained.

Independent combinatorial controls: c=1..40, n=0..240,
9640 exact cheapest-packing checks (8780 n>c).
Also 36 positive-excess CRT controls constructing
distinct admissible sources for p,r in {(11,13),(17,19),
(23,29)}, c=1,2,5 and both signs. Populate E=0,2,4,6,8
up to capacity, check distinct source congruences,
packing equality and (2). These are arithmetic
configurations, NOT asserted to be actual clock paths.
All passed. No finite experiment demonstrates the
asymptotic support or gain assumptions in sections 3-4.

## 6. Remaining target

The relay cutoff can now be eliminated exactly by
charging repeated ordered pairs with a quadratic
gain cost. The missing estimate is a sparse enough
transition graph and sufficiently small accumulated
relay gain on a genuinely long inverse branch, or
a multi-band charge bound that does not double-count
lower events. The present identities do not force
unrestricted inverse extinction or unbounded zero-phase
last labels. No twin-infinitude proof or Lean
verification; no changes to canonical Lean targets
or sibling branches.
