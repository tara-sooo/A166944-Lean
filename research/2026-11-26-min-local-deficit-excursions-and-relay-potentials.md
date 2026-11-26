# Deficit excursions, signed relay potentials and return amplification

2026-11-26 JST. Continuation of d64d656f1d0870f614b5cfc2dbcb93e2082e37e1.
Exact ordinary uncut MIN. Paper deductions, reproducible finite
certificates and finite diagnostics, not Lean-verified theorems,
a novelty claim, or a proof of twin infinitude.

## 1. Exact short/long departure dichotomy

Use the preceding note's deficit d=2v-u, and write s=0 for a
minus-side (even) event, s=6 for a plus-side (odd) event. The
selected odd prime p satisfies p | (d'-s) at the arrival.
Since d',s are even, d' lies in s+2p Z. For any event from
d in {0,6} with p>=13, the envelope gives d'>=0 and the
clock bound w<=2p gives d'<=3p+7<4p. Thus

    d' = s             or             d' = 2p+s.

The first is the short-clock case of the preceding macro note;
the second is a long departure, with

    2w=3p-1+s-d,  w >= (3p-7)/2.

As w>6, neither neighbor is divisible by 3, so 6|u.
Here the core refers to d in {0,6}, even if the offset is not
divisible by 6. Using this broader core only strengthens the
necessary conditions for returning to the two-state macro domain.

**Long-departure cap.** If the source is not a twin center then

    p^2 <= u+1.                                      (1)

Suppose p>sqrt(u+1), and let the selected neighbor be pm,
with m<p. If m=1, the other neighbor is composite, so
w<=2 sqrt(u+1)<=2 sqrt(p+2)<(3p-7)/2.
If m is composite, an odd prime factor q<=sqrt(m)<sqrt(p)
has a competing clock within 2q ticks, again too early.
If m is prime <=7, its clock is within 14 ticks.
Otherwise m>=11. For the same orientation and starting d,
the first clock for m has wait (k m-1+s-d)/2 with k=1 or 3:
the residue of the quotient modulo 4 determines k, and
both expressions are positive for m>=11. It therefore
fires no later than (3m-1+s-d)/2, strictly earlier than
the chosen long clock for p. All cases contradict first
selection. The proof uses neither a sieve nor the short
macro label cap.

## 2. Exact excursion accounting

After a long departure with label p let the first later
state with d in {0,6} be the return, if it exists. Count
the N events after the departure through this return,
with total gain G and wait W. If the terminal deficit is
d_f, then telescoping gives exactly

    G = 2W + 2p+s-d_f
      >= 2p+s-6+2N.                                 (2)

Thus the first departure and subsequent completed excursion
consume at least 3p+s-7+2N physical gain. This does not
assert that every departure eventually returns.

In particular, if only a small set of labels is allowed
during the relay preceding the next large event, it is
useful to bound the *net deficit reduction*, rather than
its physical gain. That is the purpose of the following
finite-state bounds.

## 3. Restricted relay bounds, independent of ancestry

Fix a finite alphabet A of odd primes, Q=2 product_(p in A) p.
Any consecutive run of actual ordinary events with labels in A
is a prefix of the restricted first-clock trajectory using only
A. No event in A can strictly cross the next multiple of Q,
and at a multiple of Q none is eligible. Therefore translate
the source into the even half-open cell [0,Q), take v mod Q,
and use an acyclic table on 0<=u<=Q even, 0<=v<Q.

For an offset-only upper bound, allow ANY eligible A-label
at each step, ignoring the phase. Set F(u)=0 when none exists,
otherwise F(u)=max_(p in A, p|u+-1)(p-1+F(u+p-1)).
This overbounds actual restricted gains. For exact restricted
trajectories, choose the least (w,p) over A-clocks, and put

    G(u,v) = p-1 + G(u+p-1,(v+w) mod Q),
    W(u,v) = w + W(u+p-1,(v+w) mod Q).

Both terminal values are zero; gains and waits are nonnegative
so the complete run bounds every prefix.

For signed deficit potentials instead use

    D_down(u,v)=max(0,p-1-2w + D_down(next)),
    D_up(u,v)=max(0,2w-p+1 + D_up(next)).

Both terminal values are zero. By backwards induction these
are exact maximum prefix deficit decrease and increase,
including the empty prefix. Their global maxima bound every
actual consecutive A-run, even if an outside label interrupts it.
The recurrence covers all phase residues, not just reset-origin
or envelope-valid representatives; periodic lifting preserves
the first A-clock. Thus the constants apply to arbitrary actual
ordinary histories.

For A the odd primes <=T, finite tables yield

    T    Q     offset-only max gain   exact max gain   max wait   max down   max up
    3      6           4                    4             7          0        10
    5     30          16                   14            19          2        28
    7    210          46                   34            56          8        84
    11  2310         148                  104           133         16       192
    13 30030         436                   -             -          -         -
    17 510510       1186                   -             -          -         -

In particular for ANY run of labels in {3,5,7,11},

    -16 <= d_end-d_start <= 192,    gain <=104.        (3)

The signed bounds are substantially stronger for a possible
return than the unsigned gain bound 104. The two scripts
below compute these tables; the signed script independently
checks every Bellman cell against literal restricted GCD ticks.
The maximum down witness modulo 2310 begins (u,v)=(1986,209)
and has labels 5,11,3,3,5,7,11 with waits 1,1,4,1,1,2,1.
Its gain is 38 and wait 11, hence decrease 16. This is a
restricted phase witness, not a claim of an actual canonical
root realizing the maximum.

## 4. First-return amplification and persistent bands

Consider a long departure p>=13, followed by a consecutive
relay of labels <=11. By (3), every state of this relay has

    2p+s-16 <= d <= 2p+s+192.

The lower bound exceeds 6 even for p=13. Hence no return
to the core is possible via the low relay alone, regardless
of its length or the surrounding history.

Suppose the next event, with label r>=13, returns to the core.
From d_f=d_pre+2w-(r-1), w>=1, d_f<=6, we obtain

    r >= d_pre-3 >= 2p+s-19.                         (4)

If the return is minus-side (d_f=0), the sharper bound
r>=2p+s-13 holds. This is a deterministic near-doubling
requirement, conditional on the first subsequent large
event being a return, not a claim that every next label
must double. For example the label can be smaller and
preserve a positive multiple of its own deficit instead.

A stronger persistent-band statement applies through arbitrarily
many high events. Fix 0<epsilon<1 and P>=13 with epsilon P>19.
Starting immediately after a long departure with label in
[P,(2-epsilon)P], consider any consecutive path of labels
in {3,5,7,11} union [P,(2-epsilon)P]. Then every high event
has post-deficit >=2P, and every intervening low state has
deficit >=2P-16. In particular no return to the core occurs
anywhere in this path. Induct on high events: after a high
post-deficit >=2P, the low relay can reduce it by at most 16.
A high return would need r>=2P-19, contrary to its band.
For r>=13 the even congruence d'=s mod 2r and d'>=0 then
forces d'>=2r>=2P, proving the induction.

This gives an actual all-depth obstruction, without a
prime-gap estimate, bound on support size, or assumption on
number of repeated high labels. For epsilon=1/2 it holds
for P>38. It isolates the necessary intermediate labels or
a band escape in any future return. It does NOT rule out a
persistent high-deficit path that leaves the band, or one
that never returns. Those are real remaining cases.

## 5. Local crossing implications

For disjoint completed excursions within a local path,
sum (2) with the initial departures included. If there are
J such long departures and their labels are p_i, the union
consumes at least sum_i (3p_i-5), since N>=1 and s>=0.
Consequently the sum of their departure gains is at most
(G_exc+2J)/3, where G_exc includes the full completed
excursions. An unfinished final excursion must be handled
separately, so this is not a total departure upper bound
without an endpoint term.

The signed relay bound also controls the entire low-label
part of any path: if there are H events with p>11 then
all runs of labels <=11 contribute at most 104(H+1) gain,
and their total signed deficit contribution lies between
-16(H+1) and 192(H+1). For H high events all with
p>=T, the low gain is <=104(G_high/(T-1)+1). This is
an unconditional finite-constant compression of low
transport. In a crossing with no medium events and T growing,
the low gain is o(D) provided the total crossing gain is
O(D). For a non-twin local crossing with D>>sqrt(X),
the latter follows from d<=6+5G before the last event,
w<=2sqrt(X+D+1), and d'>=0, giving final gain <=
6+5D+4sqrt(X+D+1). The same reasoning gives O(D) for
D=C sqrt(X), fixed C>0.

These statements complement the preceding mixed macro gain
certificate: a long departure cannot be repaired by a bounded
small-alphabet segment, so controlling the main-event support
alone will not automatically keep the trajectory in the
two-deficit domain. A new argument must control high-deficit
transport, medium labels, or exits to larger labels. No
unbounded favorable-reset supply has been proved.

## 6. Executed finite diagnostics

Source 1: research/min_local_deficit_excursion_audit.mjs,
commit 92f9270ad7843b7f9f565a7381defb46ad25ea0a,
blob ae1d5feb505321a7caf760b6c6d95dbb84304fa0.
Run node research/min_local_deficit_excursion_audit.mjs 500000.
Computed all tables in section 3 except signed potentials.
43,562 literal restricted clock checks.
Canonical reset scan: all 83,332 multiples of 6 in
[12,500000], stopping before first twin event or at doubling,
1,891,694 actual event incidences. 145,955 departures from
the broad deficit core, including 47,172 long departures
p>=13, of which 21,569 returned within the observed prefix
and 25,603 were censored by the stopping rule.
38,427 return-bound checks; 150,300 restricted relay gain
checks across overlapping cutoffs; 1,817 literal full GCD
tick checks. No forbidden low return among eligible relays.
A first non-twin large departure example: X=204,u=222,d=6,
p=13,w=16,post-deficit 26.
Largest observed completed after-departure gain 4,838,
from X=482556,u=482622,p=113,return offset 487572,
96 subsequent events. This is an observed example, not a
uniform excursion-size bound. Censored excursions are not
asserted to be infinite or nonreturning.

Source 2: research/min_local_relay_potential_audit.mjs,
commit 1a56764921bb752bf56e022ede5abd92ed25e1f5,
blob d53ab21938fd16263e192c49c8a8406a6ba3dafa.
Run node research/min_local_relay_potential_audit.mjs 500000.
2,693,124 table cells independently checked by literal
restricted GCD ticks and both signed Bellman identities
(including terminal cells). The full signed table maxima
are exactly those in section 3.

Separate intermediate-state controls: all 166,664 states
6|u, 12<=u<=500000, d=0 or 6; 19,028 non-twin long
departures, not all canonical-root reachable.
Following only <=11 relay labels until first high event or
twin source: 38,646 low incidences, maximum observed net
drop 12, 4,012 first-high returns, 12,518 first-high
nonreturns, 2,498 twin stops. All signed bounds and (4)
passed. Closest observed slack in (4) is 6: u=464502,
d=0,p=13,post-deficit 32, subsequent high source
u=464530,d=22,r=19,w=1,post-deficit 6.
For persistent-band controls with P=p>38 and epsilon=1/2:
7,956 launch states, 330 subsequent in-band high incidences,
17,870 low incidences, 6,894 outside-band stops and
1,062 twin stops. Maximum observed consecutive accepted
high count including launch is 3, at u=50442,d=0,P=73.
All checks passed; no claim of a universal high-count bound.

Both programs were executed as ECMAScript in the research
runtime, committed, fetched by exact commit and re-executed
from the returned source, with identical outputs. No Node
process or Lean process invoked here. The finite phase
table checks do not replace the paper proof of applicability
to arbitrary actual paths or formal verification.

## 7. Next research target

Study the first event after a long departure and a compressed
low relay, distinguishing return by a nearly doubled label,
continued high-deficit transport in a comparable band, and
interruption by medium labels. For an ordinary trajectory,
the persistent-band lemma allows the high-deficit component
to be studied without repeatedly analyzing its <=11 relays.
A bound on its gain or an independently constructed
unbounded supply of favorable resets is still required
to close the twin-infinitude route. Main and sibling
branches remain untouched.
