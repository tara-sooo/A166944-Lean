# Fast-transition marked ancestry and the untruncated energy alternative

2026-11-26 JST. Continuation of 86d425ed81fa62d9682eef40bfde6364c12406b7.
Combine the weighted marked-arrival inverse kernel with the inherited
odd-shift identity in research/2026-11-26-min-direct-fast-pair-odd-shift-and-quadratic-escape.md.
The new purpose is to count all short-fast transitions in a bounded
deficit corridor over arbitrary phases, transfer the bound to origin
mass using MARKED rather than offset ancestry, and obtain a separate
energy alternative without stopping at the cumulative lower-gain cutoff.
Paper deductions and finite diagnostic, not Lean kernel verification,
a novelty claim, or twin-infinitude proof.

## 1. Definition and exact odd shift

Use the ordinary uncut MIN model, with even offset x, time v,
label p, gain p-1, wait w, d=2v-x, and orientation e=+1
(minus/even) or -1 (plus/odd). Put s=0 or 6 respectively.
The envelope is u/2<=v<=u+1; every event has w<=2p<=3(p-1).
At the arrival of a label p>=5,

    d'=2ap+s, a>=0 an integer,
    U=0 or -2 mod 2p, v'=0 or p+2 mod 2p.

Use T>=5, and mark every arrival of a label >=T by its
state, label and side, as in 86d425e. A first high pair
has prior mark (u,v,r,f), and the next event of label
p>=T has source x, firing n, and arrival U=x+p-1.
All intervening labels are <T. Write E=x-u, V=pretime-v,
w=n-pretime, and d_r=2ar+s_r, d_p=2bp+s_p.
Then the inherited odd-shift identity reads

    (2b+1)p-2ar=c,
    c=1+s_r-s_p+2(V+w)-E.                          (1)

Since V<=3E and E is even, c is odd nonzero.
Given nonnegative integer cutoffs E<=B,w<=S,
put Q=5B+2S+7. If Q<T, then |c|<=Q, a>=1
(since otherwise (2b+1)p>=T), and p!=r.
For the latter, a repeated high label r requires
intervening gain E>=r-1, by the same-label spacing
in 86d425e. It also follows directly from the arrival
offset u=0 or -2 mod 2r and source x=r+1 or r-1
mod 2r: E is a nonnegative even integer in one of
the classes r-1,r+1,r+3 mod 2r.

Call such a transition short-fast. It necessarily
decreases deficit across the pair:

    d_p-d_r<=5B+2S-(T-1)<-6.                      (2)

This includes the possible reset target b=0; no
prime-cofactor assumption or source roughness is made.
If the prior post-deficit is <=2KT, then both
endpoints are in this corridor, and r<=KT,
p<=2ar+Q<=(2K+1)T. The coefficient b is determined
by r,a,c,p, not a separate free phase.

## 2. Global count of short-fast PRIOR MARKS

Fix K>=1 and R>=T^2, T tending to infinity.
Count all allowed prior high marks with u in [R,3R),
positive multiplier, d_r<=2KT, whose actual next
high event has E<=B,w<=S,Q<T. These marks may be
any envelope-valid states with exact arrival phase;
no reset ancestry or actual incoming high event is
required. This relaxes the set of ordinary histories.

For each choice of r,a,c, (1) requires p to be a
prime divisor >=T of N=2ar+c, with 0<N<=(2K+1)T.
For fixed K and sufficiently large T, N<T^2,
so there is at most ONE such prime. In general the
number is <=log((2K+1)T)/log T. The target multiplier
b is then determined. No count of arbitrary waiting
times or relay words is needed.

There are O_K(T/log T) possible pairs (r,a):
r lies among primes in [T,KT], a<=K, and the
prime upper bound suffices. More uniformly one can
sum KT/r over these primes to get
O(KT log(2K)/log T) for K fixed or moderately growing.
There are O(B+S+1) choices of c, O(B+1) of E,
and four side choices. At the target source x,

    x=e_p mod p,
    x=E+e_r_arr mod r, e_r_arr in {0,-2}.

The CRT with p!=r fixes one class modulo pr.
In [R,3R+B) there are O(R/T^2) offsets per tuple:
B<T and T^2<=R. Given x and the tuple, u=x-E
and v=(u+2ar+s_r)/2 are fixed. Thus this counts
prior marked states themselves, not just offsets,
and ordinary forward determinism allows at most
one actual next high event per such mark.

Denote this set by F_marks. The result is

    |F_marks| <<_K R(B+1)(B+S+1)/(T log T).        (3)

The same bound applies to distinct source offsets
of these transitions. Unlike the earlier close-phase
collision count, it refers to actual forward
transitions from relaxed high marks, not two
different hypothetical histories at one endpoint.
The extra factor 1/log T uses only a prime upper
bound, not a two-linear-form sieve. We did not
need the phase-fiber exceptional set.

For B=S=floor(T^theta), fixed 0<theta<1/2,
(3) is O_K(R/(T^(1-2theta) log T)).
It is a polynomially thin set, even if the
clock gap at the current source is very large.
It includes arbitrary intervening medium
events of total gain <=B.

## 3. Marked ancestry enlarges the lower-gain budget

Use canonical roots X=0 mod6 in [R,2R), and
consider local pre-offsets x<X+D with D<=C0 T
for fixed C0>0, R^epsilon<=T<=sqrt R.
An initial deficit is 6 and every event contributes
at most 5g to deficit, so all pre-offsets in the
window have d<=6+5D. Choose fixed integer K
large enough that 2KT>=6+5D for all large T.

Suppose some high event has wait <=S, and all
preceding lower events (labels <T) have cumulative
gain <=M. Assume 5M+2S+7<T. If this is the
FIRST high event, then

    0<=d_post<=6+5M+2S-(p-1)<0,

a contradiction. Thus there is a preceding high
mark. Its offset lies in the local window,
its deficit is within the K corridor, and the
relay to the current high source has E<=M.
It belongs to F_marks of (3), with B=M.

Let H0 be any fixed integer upper bound for
floor((D-1)/(T-1)). The preceding high mark is
reached after h high events, 1<=h<=H0. We can
use the stronger MARKED endpoint estimate
from 86d425e, section 3 equation (2), instead
of its offset-traffic estimate (5).
Choose its gain scale L=max(1,M). Its inverse
kernel is C=(4/3)J(L+2) with J=O_epsilon(1).
The accumulated floor-cost for a canonical root
reaching the marked endpoint is at most

    (arrival time-root time)/T + M/L
        <= 3D/T+1 = O_C0(1).

Consequently the number of distinct canonical
origins per specified preceding high mark is

    <= const (L+2) sum_(h=1..H0) C^(h-1)
    <<_(epsilon,C0,H0) (M+1)^H0.                  (4)

This saves one factor M+1 relative to using
the offset bound with the same h budget. The
label and firing phase of the endpoint mark
are already specified, so no final fictitious
inverse step is necessary.

Multiply (4) by (3) with B=M. The number of
canonical roots that visit ANY high event with
w<=S in the local window before exceeding the
cumulative lower-gain budget M is

    << R (M+1)^(H0+1)(M+S+1)/(T log T).           (5)

This includes mergers and all clock phases,
and does not require the first high event to
be significant in the sense of earlier notes.
All constants depend on the fixed scale ratios,
epsilon and H0, not the size of T or M.

In particular take M=S=floor(T^theta),
0<theta<1/(H0+2). Then (5) is o(R).
For example D=2T, T=floor(sqrt R), H0=2,
any fixed theta<1/4 is permitted. Thus for
density-one canonical roots, EVERY high event
within this local window and before the cumulative
lower-gain budget is exhausted has w>T^theta
(up to integer rounding). This polynomial budget
is much larger than the polylogarithmic budget
in the preceding aggregate wait theorem, but
the conclusion is different: it excludes
very fast high events, not significant slow
high events. In particular it is not an
extension of the o(RD) total-wait estimate.

For these short-fast events each gain is O(T)
by d_pre<=6+5D, d_post>=0 and w<=S.
The number per local root is at most H0+1
(including a possible exiting overshoot).
Hence their total origin-weighted gain before
the M cutoff is o(RT) under the same parameters.

## 4. An energy alternative without a lower-gain stop

Retain the whole local paths from the canonical
ensemble, stopping before first twin event or
on local exit, but NOT at any lower-gain cutoff.
Let G_low be the sum over all origins of the
gains of every event with p<T, including the
last executed event if lower. Let F_fast be the
total gain of all events with p>=T and w<=S.
Use Q=5B+2S+7<T with arbitrary B,S as above.

For every such fast event, the gain is O_K(T)
even if it exits the window: d_post>=0 gives
p-1<=d_pre+2S. Consider three cases.

* If it is the first high event, its preceding
  lower gain must exceed B, by the same
  nonnegative-deficit argument in section 3.
* If there is a preceding high mark but
  intervening lower gain E>B, the relay
  contains at least B+1 gain.
* Otherwise it is a short-fast transition
  from one of the marked states of (3).

The lower-event segments charged in the first
two cases are disjoint along a given origin.
Therefore the number of fast event incidences
in those cases is <=G_low/(B+1).

For the third case, let m(z) be the number of
distinct canonical origins that visit a high
mark z within their local windows, and define
the high-mark visit energy

    E_high=sum_z m(z)^2.

We count actual marked arrivals, not all
hypothetical phases at a given offset.
Each origin visits a mark at most once.
A mark can generate at most one next high
event, so its cohort is charged at most once
in this third case. The total number of these
incidences is <=sum_(z in F_marks) m(z).
Cauchy-Schwarz and (3) give the untruncated
fast-gain inequality

    F_fast <<_K T [ G_low/(B+1)
          + sqrt(E_high * R(B+1)(B+S+1)/(T log T)) ].   (6)

No bound on the number of medium events,
their cumulative gain, or the amount of
earlier coalescence is assumed for (6).
It applies to actual roots through all
their local events, with the stop before
twins to separate the non-twin transport.
The arithmetic supply bound itself also
allows twin events.

Thus if F_fast>=rho RT for fixed rho>0,
at least one of the following must hold,
with constants depending on rho,K:

    G_low >> R(B+1),
    E_high >> R T log T/[(B+1)(B+S+1)].            (7)

For B=S=floor(T^theta), 0<theta<1/2,
either lower gain is Omega(R T^theta),
or high-mark energy is Omega(R T^(1-2theta) log T).
This is a conditional population-level
alternative, not an assertion that F_fast
is itself macroscopic under finite twins.

The full window gain per origin is O(T)
except for a possibly very large final
nonfast high overshoot; the latter is
irrelevant to the bound on fast gain
because its gain is O_K(T) as checked
above. No unsupported cap on all high
labels is used in deriving (6).

## 5. Limits and the remaining entry problem

The exact odd-shift argument supplies a
different type of arithmetic sparsity from
the earlier ambiguity sets. Combining it
with marked ancestry yields polynomial
budget (5). Combining it with visit energy
yields (6) for the untruncated ensemble.
However very fast events consume deficit,
rather than supplying large waits. Excluding
them does not imply a twin-free time demand
contradiction. A path can generate and
consume deficit using clocks of order T,
or through lower-scale events.

There is also a structural limitation of
iterating the old relaxed weighted kernel.
Its direct root-entry term ignores every
clock inside a lower-only history. At a
fixed even offset x in the interior of
the root slab, the relaxed zero-high inverse
graph admits all multiples-of-six roots in
[x-M,x] (when M<D), simply by permitting
the total gain as a single displacement.
This is Theta(M) relaxed entries, even
though very few may actually reach that
offset. Thus an upper bound based ONLY on
unweighting this particular relaxed root
entry count cannot show polylogarithmic
mass for polynomial M. Repeatedly changing
the gain scale of the geometric weights
does not remove these fictitious entries.
This is an obstruction to that relaxation,
not a counterexample to a bound on actual
MIN basin masses, nor an impossibility
theorem for all weighted methods.

The next substantive target is an actual
lower-only entrance estimate, retaining
first-clock selection or a cancellation
identity, and/or a bound on E_high strong
enough to use (6) along with a separate
upper bound for the slower waits. No
unbounded favorable reset supply or total
wait o(RD) has been derived for the
untruncated ensemble. No twin-infinitude
contradiction or Lean verification.

## 6. Executed finite audit

Source research/min_local_fast_transition_ancestry_audit.mjs,
commit 00138927f54a9e21925098efda622323e6d8b16b,
blob a0a9e9027abbab6eebaa1c11dd7608bf7d30a3c3.
Run node research/min_local_fast_transition_ancestry_audit.mjs.
Actual ECMAScript execution in the research tool runtime,
remote exact-commit readback and re-execution with
identical counts. No Node process or Lean process invoked.

Four finite controls, K=8, all canonical multiples
of 6 in [R,2R), D=2T, before twin/local exit,
without a lower-gain stop.

    R        T    B  S   roots   high pairs  short-fast  before-budget fast
    10000    53   4  5    1667       77           0           0
    100000  157  12 12   16667      476          14           6
    1000000 503  20 24  166667     3513          29          10
    1000000 997  32 40  166667      934           0           0

Total 351668 root/parameter incidences, 7522976
ordinary events, 87877 high incidences, 5000 first
high pairs, 1543 short-relay pairs, 43 short-fast
pairs. 2649 high fast events in the full local
windows, of which 2416 were first high events.
The deterministic first-fast lower-gain bound
passed in every case. 16 fast events before
cumulative lower gain exceeded B, each on a
different root/parameter incidence. These are
finite controls, not a claim that (5) has
vanishing exceptions at the tested values.

Independently enumerate the necessary equation
(1) via factoring 2ar+c, followed by the
horizon CRT and both orientations. This yields
3,619,671 tuple/offset incidences, 749,225
distinct candidate offsets summed over controls.
The relaxed offset sets are extremely loose
at these finite sizes. All actual capped
short-fast transitions are contained.

Separate relaxed high-arrival controls: 44,518
arrival states satisfying exact firing phases
and envelope, 101,761 unrestricted lower
relay events, 357 short-fast transitions
inside the deficit corridor. 5,357 odd-shift
checks, 400 candidate-set containment checks
(43 actual and 357 relaxed), 10,196 literal
GCD tick checks. Example actual root X=1019658:
prior arrival (1020498,510850), r=601,
next high source 1020498, p=1231, wait17,
zero relay, prior total lower gain240.
Example relaxed mark (1000540,503511),
r=1619, followed by lower gain2 and p=2161,
wait1. Its earlier reset ancestry is not
asserted. All assertions passed.
The audit verifies arithmetic and finite
containment, not the asymptotic constants,
the Cauchy-Schwarz energy alternative as a
numerical bound, or the finite-twins premise.
Counts overlap across parameter choices and
shared trajectories.

No canonical Lean target or sibling branch changed.
