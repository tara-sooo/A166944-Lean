# Quiet-tick coarea and failed-query cancellation of label three

2026-11-26 JST. Continuation of 562b8890d1ae2aaeaabc888cf8458c9cf1e64245.
Improve the high-height small-label charge by removing every selected
firing tick from the query cost when the height is O(y). Replace all
distinct queries by distinct FAILED queries. Exact finite probability
law and level identity, conditional estimates on actual mixed paths,
finite diagnostics. No Lean verification or twin-infinitude proof.

## 1. Failed-query rank law

Use the actual adaptive CRT process of 562b8890, with a finite admitted
alphabet A containing 3, canonical roots X=0 mod 6 and v=X/2+3,
and full seed period P=4 product_(p in A) p. Stop at a restricted
terminal or the first arrival with gain >=D. A terminal scan makes no
actual time or displacement contribution. For each admitted p>=5,
let I_p indicate its first positive query and F_p count distinct
negative residue queries made before this first positive or the stop.
No queries to this p after its first positive are counted.

Fix all root residues except the one modulo p, equivalently fix
X mod P/p. On the deterministic all-negative branch, let q be the
number of distinct p-residues queried, in their first-occurrence order.
Exactly q of the p lifts select p. On the i-th hit F_p=i-1; for the
remaining p-q lifts F_p=q. Thus

    E I_p = q/p,
    E F_p = [q(q-1)/2+(p-q)q]/p
          = q-q(q+1)/(2p).

In particular

    E F_p/(p-1) <= E I_p <= 2 E F_p/(p-1).       (1)

The case q=0 is immediate; otherwise divide by q/p, obtaining
E F_p/E I_p=p-(q+1)/2 in [(p-1)/2,p-1].
Average over the other residues. This applies to transcript-adapted
stops as well as a displacement stop, for the same reason as the
earlier query-rank identity. It involves no independence assumption
between actual event choices.

## 2. Remove selected firing ticks

Take y>=5 and A consisting of admitted odd primes <=2y, with
B=A intersect [y,2y]. Let h=v-u/2, initially 3, and at a tick n
the candidate defect is 2h_tick+1 for even n or 2h_tick-5 for odd n.
The potential band weights remain

    a_y(h)=sum_(p in B) [1_(p|2h+1)+1_(p|2h-5)]/p,
    Phi_y(t)=sum_(1<=h<=t) a_y(h).

Every failed query is charged at its actual tick once; counting
possible defect divisors and repeated queries only enlarges the cost.

At a firing tick with selected label r<y, the least-label tie
rule means NO band prime is queried. If r>=y, any failed band
query preceding the winning prime r would require a second
distinct prime p>=y dividing the same nonzero defect. This is
impossible if its absolute value is <y^2. In particular for
a fixed height corridor Hmax<=Cy and sufficiently large y,
there are NO failed band queries at any selected firing tick.
The successful query itself is not counted in F_p. This second
observation is why the failed-query law, rather than counting
all queries, permits removal even of high firing ticks.

For a terminal, retain the earlier charge of at most two distinct
negative residues per prime from the virtual terminal scan.
At a fixed source and sign there is just one residue to query.

## 3. Exact quiet coarea, including individual levels

Write h_i for pre-event height, k_i=h_i+w_i for firing height,
and h_(i+1)=k_i-(r_i-1)/2 for arrival height. Define the
residual down interval by removing its TOP level:

    I_i^o = {h_(i+1)+1,...,k_i-1},
    D^o(h)=sum_i 1_(h in I_i^o).

These are empty for r_i=3, irrespective of the phase or height.
The interval has length (r_i-3)/2, so exactly

    sum_h D^o(h)=G/2-N,                           (2)

where G is total gain and N is total event count. For every
positive integer h, the number U_quiet(h) of actual waiting ticks
at height h, EXCLUDING the selected firing tick of every event,
satisfies the exact integer identity

    U_quiet(h)=1_(h<=h_end)-1_(h<=3)+D^o(h).     (3)

Indeed ordinary upward minus downward crossings telescope to
the endpoint indicators, and the removed firing tick coincides
with the removed top of its down interval. This is an identity
even when the height domain is not bounded. Multiplying by
a_y(h) and summing gives

    sum_h a_y(h) U_quiet(h)
       = Phi_y(h_end)-Phi_y(3)+sum_h a_y(h)D^o(h). (4)

For the OLD path of 7021cc1, with all labels <y, the same
quiet formula is valid for bounding possible preemption
residues, without any y^2 defect restriction, because no
new prime can win at the old firing tick.

For the actual MIXED path, under 2Hmax+5<y^2, section 2 gives

    C_fail=sum_(p in B) F_p/p
      <= 2 sum_(p in B)1/p
         + Phi_y(h_end)-Phi_y(3)+sum_h a_y(h)D^o(h).          (5)

If the defect restriction fails, add the nonnegative cost of
failed band queries at firing ticks. Without a height restriction,
one can still remove the top of every interval whose label r<y,
and retain all other tops, by the least-label tie rule.
These variants clarify the exact domain of (5).

The label 3 contributes NOTHING to the residual interval sum
even when its firing height is arbitrarily large. In contrast
the earlier untrimmed potential counted its single downward level.
It is not asserted that deleting actual label-3 events leaves
the trajectory or its endpoint height unchanged. The cancellation
is in the accounting identity, not a modification of dynamics.

## 4. Improved actual band-gain estimate

Take D=ceil(C y), C>=1 fixed, and admit only primes <=2y.
Stop as above. The overshoot is <2y, so G<= (C+2)y+1.
All waits satisfy w<=3(r-1), so Hmax<=3+3G=O_C(y)
and the defect restriction holds for sufficiently large y.
Define residual high-height occupation energy

    L^o_y=sum_(h>=ceil((y-1)/2)) D^o(h)^2.

The defect weights vanish below that high region; as in
26166e7 their sum is O_C(1/log y) and squared sum
O_C(1/(y log y)). Equation (5) and Cauchy-Schwarz give
the pointwise bound

    C_fail <<_C 1/log y + sqrt(L^o_y/(y log y)).

Using (1) and summing over p>=y, the expected number
K_B of distinct band labels is <= [2y/(y-1)] E C_fail
(the function p/(p-1) decreases for p>=y).
The repeat-spacing argument of 562b8890 shows each
such label occurs O_C(1) times. Thus

    E G_B <<_C y/log y + sqrt(y E L^o_y/log y).   (6)

In particular L^o_y<=L_y pointwise, often strictly.
This is a sufficient occupation criterion strictly in
terms of the residual intervals and omits all label-3
contributions, not just those at low height. It still
does not prove that E L^o_y=o(y log y).

A probability variant uses an auxiliary transcript stop:
stop immediately AFTER the first distinct failed query
that would make C_fail>epsilon, so the stopped cost is
at most epsilon+1/y. On paths with original cost
<=epsilon this stop never intervenes. The failed rank
law (1) applies to the auxiliary process even if it
stops mid-scan. By the union bound on its positive
queries,

    Pr(K_B>0) <= Pr(C_fail>epsilon)
                         + [2y/(y-1)](epsilon+1/y).

Hence L^o_y/(y log y)->0 in probability suffices for
E G_B=o(y), since the stopped gain is O_C(y).
The extra 1/y is needed for this AFTER-query stop.

For any fixed integer z0>=5 let

    S^o_z0=sum_(i:5<=r_i<=z0)
                    |I_i^o intersect [ceil((y-1)/2),infty)|.

The translated-interval prime upper bound in 7021cc1
applied to intervals for r>z0 and max a_y<=2/y applied
to the smaller intervals give

    E G_B/y <<_C 1/log y + 1/log(2+z0) + E S^o_z0/y.  (7)

Consequently only the residual high occupation of labels
5 and above needs to be bounded in this criterion.
The earlier open condition S_z=o(y) for the untrimmed
intervals has not been established. Equation (7) replaces
it with a different, weaker sufficient condition.
For r=5 the residual interval is a single level and
can have positive charge; one cannot simply extend
the exact label-3 cancellation to all small labels.

## 5. Executed audit

Source research/min_local_restricted_quiet_coarea_audit.mjs
commit 7a96e7006c2e477caf8a4c244835ec1bd70b5014,
blob adb30dddb2251780f2afa1e2a28ad0c2936f98c1.
Reproduce: node research/min_local_restricted_quiet_coarea_audit.mjs.
Executed as ECMAScript in research runtime, fetched at exact commit,
re-executed with identical output. No separate Node or Lean invocation.

Same four full-period and three local samples as 562b8890:
D=4y, z is the inclusive maximum allowed prime cutoff;
period (y,z)=(5,7),(6,11),(7,13),(9,17).
Local y=127,503,997, z=2y, 2000 roots each.
Each path independently computes actual neighbor-factor clocks,
then scans defect candidates and records distinct negative queries.
Integer checks of (3) at every level, (2), and exact failed rank
law in every full-period conditional p-lift group.
Use floating point for weighted coarea and Cauchy-Schwarz.
Small-y controls may lie outside the defect restriction: explicitly
record firing-query failures and their cost, and include that cost
in (5) when necessary. All large local samples lie inside the domain.

    kind    y    roots   mean old L_y    mean residual L^o_y
    period  5       70          3.829           1.500
    period  6      770          6.578           2.679
    period  7    10010          8.845           4.104
    period  9   170170         12.135           5.617
    local 127     2000        137.730         112.944
    local 503     2000        380.279         337.859
    local 997     2000        161.331         148.837

Mean weighted charge of down intervals for labels <=11,
before and after top removal (local samples):
y=127: .01390973 -> .00775728
y=503: .00354518 -> .00261520
y=997: .00044408 -> .00035185

Total 187020 root/cutoff incidences, 669735 actual events,
247251 label-3 events, 113994 band first hits, 2248222
distinct failed queries (661870 quiet,1586346 virtual terminal,
6 firing in small y=7 control outside the unique-divisor
domain). All 41884 conditional failed-rank integer checks,
4301541 exact quiet-level identities, 187020 weighted coarea
checks, 247251 empty label-3 residual checks, 110077
unique-band-divisor firing checks passed. 174186 trajectories
satisfied 2Hmax+5<y^2; no failed firing query on these paths.
All assertions passed. The local samples test only pointwise
identities, not full-period expectation inequalities.

Residual charge for label 5 need not vanish. Example actual
local y=127, X=100002: at u=100366,v=50407, p=5,w=3,
k=227 and h_next=225. The residual level is 226; its two
defects 453=3*151 and 447=3*149 both have a band prime.
This is a nonzero charge in the exact residual potential,
not necessarily a successful query at that event.
336,500,73 local roots at y=127,503,997 respectively
had positive residual label-5 charge.

## 6. Remaining work

The improvement removes a fixed small alphabet member
exactly, rather than bounding its repeated high occupation
by a run cap. The residual occupation from label 5 and
larger labels, especially repeated intermediate labels at
high height, remains uncontrolled asymptotically.
Neither the untrimmed nor the trimmed energy hypothesis
has been proved. The probability statements are on complete
CRT periods, not on local slabs of length O(y^2).
No restricted-termination upper bound sufficient for
twin infinitude has been obtained. No canonical Lean
target or sibling branch changed.
