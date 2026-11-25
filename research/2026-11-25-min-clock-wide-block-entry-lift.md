# Direct wide-primorial block-entry lift with high-birth exception

2026-11-25 JST. Continues 032b6589dd168d59512b96d15c2a9f779e9a1dd2. New paper deduction: map the adaptive capacity-two unit allocation directly to the preceding boundary of a much wider primorial block, without requiring a strip to contain a boundary or repeating a transfer at each scale. A partial initial block is the sole exception; for large anchor deficit it transports to the recorded birth stock with a vanishing coefficient. Small anchor deficit transfers to positive target occupation with another vanishing coefficient. The remaining high-deficit boundary keys have the same absolute quotas as before even for a polynomial-width grid, and all selected primes below a logarithmic cutoff are eliminated from their support. Heavy residual remains open; no Lean compilation or twin infinitude claim.

## 1. Setup

Retain original dyadic X, odd sources M in [X,2X), B=ceil(sqrt(7X)), u=log B, H=4B, starts (M+2,2M-2), original fixed-cap MIN through completed crossing event or earlier twin. Clock <=6B, total gain <=12B+6, actual d=2t-C in [0,12B+6]; selected p>=r, actual wait w<=2r<=3(p-1). Actual long LOW nonreset donor anchors g, LOW-tail primorial L<=u^1/16, anchor post horizon C_g, d_g>6, target C with C-C_g<L and actual positive net drift. Pair charge c=(r/B)xD, D=d_g-6<=12B, x=x_i(g)x_j(g)<=1. Each unordered pair/target occurs once; O(XB) supporting pairs; per pair sum r/B<=27. All estimates concern the normalized offdiagonal donor moment, not original W_g. No new occupation.

Use first common RECORDED state (t_*,J_*), d_*=2t_*-J_*. For OLD targets G=C-J_*>=h=ceil(min(r/2,D/10)), use d8117ba capacity-two integer allocation of c/h<=24 in [C-h,C), within actual shared prior edge gain units. At most 48 total weight per integer gain unit per pair over all targets. For RECENT G<h retain d8117ba inequality; not included in OLD lift. These are alternative transport routes, not additive on overlapping weights.

## 2. NEW direct block-entry map without a minimum strip length

Choose an even primorial Q=product_{p<=Y}p, Q<=B. For each allocated unit [k,k+1) put K=Q floor(k/Q). In the common recorded suffix:

* If J_*<=K, take the unique actual shared edge with pre-horizon A<=K<post-horizon J'=A+q-1. Because K<=k<C, this edge is strictly before the target and J'<=C. It need not be before the particular edge covering k: it may be that same crossing edge. It strictly crosses the boundary, so q>Y by the primorial barrier. Each assigned pair shares its actual recorded arrival as well as departure.
* If K<J_*, the boundary precedes the common recorded path. Assign to that pair's initial partial-block birth exception, not a fictitious shared entry. Since k>=J_*, necessarily K=Q floor(J_*/Q). There is only one such block across ALL allocated targets of this pair, even if some later target strips do not meet it.

The capacity-two density 48 gives total weight <=48Q per pair and block, both the entry and the initial exception. No condition h>=4Q is required; no new Hall matching or scale-by-scale allocation. The entry may be outside the original backward strip, which is the reason for the extra deficit error below. This is a direct alternative to the previous capacity-three grid restriction. Its elementary bound follows from the original allocation on the same set of actual units. For a fixed pair, all target suffixes are consistent where they overlap; the latest witness covers earlier allocated units.

## 3. High-deficit transfer with explicit birth exception

Suppose D>=2L. At an actual entry with J'<=C_g, using k>=C-h, K>=k-Q+1 and J'>K, gives
    C_g-J' <= C-J' <= h+Q-2 <= D/10+Q-1.
Thus d_g-d_entry<=5(C_g-J')<=D/2+5Q. When J'>C_g it is in the original LOW tail and d_g-d_entry<L<=D/2. Hence for every assigned entry
    d_entry >= 6+D/2-5Q.                         (1)
If K<J_* instead, J_*>K and J_*<=C_g, so the same distance estimate and elapsed-clock bound apply to d_*. In particular if D>=f Q with f>=20,
    d_entry>=6+D/4, or d_*>=6+D/4 in birth exception. This is a post-state bound, not a bound for every earlier pre-state. With f>=20 all retained entries are nonRESET, with d_post>=2q from the exact event phase, and the birth has high deficit. No high-deficit claim for arbitrary unfiltered wide lift.

For the initial exception, each distinct pair's total weight <=48Q and d_*-6>=fQ/4 if any assigned target passes the high filter. Thus
    M_partial <= (192/f) F_partial,               (2)
where F_partial=sum (d_*-6)_+ ONCE per actual supporting pair with any such exception. There is no factor for target count or coarse block size. This does not bound F_partial.

For small anchor D<max(2L,fQ)=D0, the actual positive target natural pair contribution e=w²/(2r)>=r/18 (p>=3, positive drift w>(p-1)/2>=r/3). Hence
    M_pos,small <=18 D0/B E_target,pos
                 <=18 D0/B E_+^full.             (3)
Each pair/target counted once, normalized x<=1; (3) covers small-D recent as well if used before the OLD/RECENT split. If retaining prior absolute O(XBL) separately, disjointly assign D<2L there. No assertion that the controlling moments themselves are bounded. In particular (3) is a conditional small-coefficient transport, not absolute deletion.

Choose Q largest even primorial <=B/u^4 and f=u (eventually >=20). Chebyshev theta bounds and Bertrand imply Y=Theta(u), since the next prime is O(Y) and the primorial gap costs at most O(log Y) in logarithm. Then D0/B=O(u^-3), and 1/f=u^-1. The high-filtered OLD mass either maps to a shared nonRESET actual q>Y boundary, or to (2), while small D uses (3). This removes all labels q<=Theta(log B) from the boundary support with no inverse strip-length factor. It is not the natural slab MED criterion: these are full actual common predecessor edges with boundary-weighted charge.

## 4. Absolute quotas remain valid on the wide grid

Each actual source crosses at most O(B/Q+1)=O(B/Q) boundaries, because Q<=B and total gain O(B). The coarse physical key (K,A,v,q) omits recorded arrival. Each pair's weight there <=48Q. Actual total vertex memberships O(XB/Q); bilateral degree cap Q m, m=u^11/4, pays O(XBm). Each remaining active vertex needs >m/48 actual charged partners. At fixed q>Y, there are O(X/Q) possible boundaries, at most one even pre-horizon A in [K-q+2,K] per parity satisfying A+2s-1=0 mod q, and O(B/q) phase times v in the actual deficit strip. Thus O(XB/(Qq)) relaxed keys. Key quota Qm pays O(XBm log u). These absolute budgets are uniform for Q<=B and do not require Q to be polylogarithmic. The use of Q in both capacities and key/membership counts cancels. A key after the quota can still carry very large weight; no uniform multiplicity bound.

For example after disjoint vertex and key payments on high-filtered lifted OLD mass, with f=u and Q as above:
    M_pos <= O(u^-3) E_+^full
             + O(u^-1) F_partial
             + M_recent,highD + M_wide,res
             + O(XB u^11/4 (1+log u)).
For recent highD use earlier sub-top T/B bound and near-top residual separately. M_wide,res is actual thick high-deficit shared recorded crossing charge with q>Y, not a new independent energy assumed small. This improves the previous grid transfer's short-strip restriction, not a general upper bound on heavy crossings. No direct W_g payment or self-absorption; E_+^full, birth and wide residual remain.

## 5. Finite audit

Standalone research/min_clock_wide_block_entry_lift_audit.mjs, source commit 45ff156d954668b80475c98c413c39c7fce2e784, exact remote blob 6ec279aa1844b8da23132b5fd7456092cfef6a81. Extends previous source and retains original sampled rough slots/levels, masks, literal MIN, pair aggregation and prior allocations. New blockLift checks actual pair birth, allocated gain units, direct boundary inverse search in actual shared prefix, strict nonLOW crossing, entry/birth floor (1), filtered high-deficit inequality, per-pair boundary and initial partial-block caps, actual per-source boundary memberships, complete charge partitions, key quotas and bilateral peeling with independent batch oracle. Tests (3) on weighted actual positive target contributions. The code tests the finite birth coefficient inequality when factor>=20; no positive high-filtered birth-exception case occurs, so (2) remains paper-only in that respect. Actual JS function executed in available runtime, not Node or Lean.

Run:
    node research/min_clock_wide_block_entry_lift_audit.mjs 4096 16384 65536

12 original modes, each Q6/Y3 factor20, Q30/Y5 factor20, Q210/Y7 factor0 (no fQ filter, still D>=2L) =36 new ledgers. Same 12 selected origin/levels per X and two old occupations, independent original LOW L30/y5 and L6/y3. Only X65536 full positive have positive target charge. Fixed diagnostic key and vertex cap8Q; the comparisons are independent, not cumulative. All assertions passed.

Largest cohort at C203040,r=p277,w353, 92 donors, 4186 pairs, M_pos=1156101.58112, D=676, h=68. Q6 filtered transfers all to 7 coarse keys (not previous 4 grid keys because different allocation). Q30 filtered transfers all to two keys, both q7:
    (K,A,v,q)=(202950,202950,101747,7), post deficit538, weight272023.90144;
    (202980,202978,101789,7), post deficit594, weight884077.67968.
Each key has all 4186 pairs/92 sources. Q210 unfiltered maps all to a SINGLE actual earlier key
    (202860,202818,101729,127), post horizon202944, post deficit514,
    weight1156101.58112, all 4186 pairs/92 sources.
No initial exception. This Q210 example does NOT satisfy f>=20; the observed high post is real, not ensured by high-filter theorem. Key caps8Q pay336/480/1680 respectively; vertex peel pays zero in all three. At Q30 max pair boundary weight211.19868 vs cap1440, Q210 276.18289 vs10080. Actual 142324 allocated-part checks each. No numerical contraction; coarse entry counts do not bound ancestor pair count.

At X65536 L6 positive total1496831.75811. Filtered Q6/Q30 move smaller D sector340730.17699 to weighted target occupation1379492.14768; remaining large cohort as above, no recent/birth. Q210 without fQ filter has OLD1449696.53687 and RECENT47135.22124. OLD lifts1368188.74927 to four keys and initial exception81507.78761, birth stock142114, min birth deficit0. Besides q127 cohort, q149 carries212015.23894 at post d=6, q31 carries53.94690 at post d=0 and q13 carries17.98230 at post d=26, all K165270. This demonstrates why the large-D filter matters: a wider boundary can reach RESET for smaller D, and birth exception need not have positive stock. 247147 allocated-part checks, max lag198, vertex quota pays93.71681, key quota3431.92920 on separate ledgers. The unfiltered diagnostic is not the asymptotic parameter choice. Main and independent prime-root branch unchanged.

## 6. Next

At the largest sample the q5/7 fine-boundary cohort traces to the same actual q127 block entry, still carrying 92 donors. Next inspect its incoming cohort formation and high recorded deficit, and the q149 RESET entry of the smaller cohort as a separate birth/ascent case. For the theorem, use q>Y and high phase at wide entry, improve heavy actual ancestry bounds without a Q/q factor or circular energy comparison. The full positive, birth, wide key, recent and original cross-to-donor/recipient reuse sectors remain open.
