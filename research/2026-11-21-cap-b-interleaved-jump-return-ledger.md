# Cap B continuation: an interleaving-robust jump/return offset ledger

Date: 2026-11-21 JST. **Status: rigorous paper inequalities plus exact replay checks; NOT a new Lean kernel proof and NOT a proof of unconditional Cap B or twin-prime infinitude.**

Companion independently executed Python 3 standard-library audit: [`cap_b_interleaved_return_audit.py`](cap_b_interleaved_return_audit.py). The committed source was fetched and compared with the created content. It checks exact gcd equality at *every hit* and unit gcd at *every intervening index* in two existing record-shaped control trajectories, totaling 63 hits, and verifies the inequalities below. The actual recurrence/first-hit definitions were reopened in the supplied `workspace.zip`: `mission_scan/twin_proof/cap_bound/WeightReal.lean`, `AllIndices.lean`, `canonical_toll.md`, and the public `A166944/RebalancedCrossingGrowth210.lean` / `ReplayOffset210.lean`.

## 1. Four-way normal form for a long-prime H event starting at low offset

A moving-horizon event \((s,C)\to(r,C')\) has gap \(g=r-s\), odd increment \(e=d(r)>1\), \(C'=C+e-1\), pre-offset \(X=2s-C\ge0\), post-offset \(X'=2r-C'=X+2g-(e-1)\).

By the **exact gcd divisibility**:

- on an **even** hit, \(e\mid r\) and \(e\mid C-1\), hence \(\boxed{X'\equiv0\bmod 2e}\);
- on an **odd** hit, \(e\mid r-2\) and \(e\mid C+1\), hence \(\boxed{X'\equiv6\bmod2e}\).

Suppose \(0\le X\le10\), \(e=p\ge13\) is prime, and \(g>10\) is in selective growth H (indeed the established `large_relative_gap_cases` forces a prime increment in such long-H events). The already proved first-hit bound \(g\le2p\) gives

\[
0\le X'\le X+3p+1\le 3p+11<4p.
\]

Consequently

\[
\boxed{X'\in\{0,6,2p,2p+6\}.}\tag{1}
\]

The exact event gaps for the four cases are:

| hit parity | post offset | required gap \(g\) |
| --- | --- | --- |
| even | 0 | \((p-1-X)/2\) |
| odd | 6 | \((p+5-X)/2\) |
| even | \(2p\) | \((3p-1-X)/2\) |
| odd | \(2p+6\) | \((3p+5-X)/2\) |

This is a general **symbolic** lemma, not a graph-search result. We call the first two cases **direct low returns** and the latter two **up-jumps**.

## 2. An unconditional drift cost for every H event

The selective-growth classification is by the inequality \(h=e-1<3(g+1)\). Since \(h\) is even, this implies \(h\le4g\): for \(g=1\), \(h\le4\); for \(g\ge2\), \(h\le3g+2\le4g\).

Therefore every H event has offset change

\[
\Delta X=2g-h\ge-\tfrac12h. \tag{2}
\]

Every **fast/non-H** event has \(h\ge3(g+1)\), hence \(\Delta X=2g-h\ge-h\), and also \(\Delta X\le-g-3<0\). In other words, H events can reduce X by at most half of their horizon growth; fast events consume offset while never reducing it by more than their whole growth.

For any arbitrary interval of events, let \(H_I=\sum_{\rm H}h\), \(F_I=\sum_{\rm fast}h\). We obtain the **interleaving-robust ledger**

\[
\boxed{X_{\rm end}\ge X_{\rm start}-F_I-\tfrac12 H_I.}\tag{3}
\]

All event types and orders, including composites, are allowed.

## 3. A completed low-up-jump-to-low return costs at least \(2p-10\)

Suppose a long H prime \(p\ge13\) starts with \(X\le10\) and lands at \(X'\in\{2p,2p+6\}\). Follow any later events (in *any* order) up to the first return to \(X\le10\). If the subsequent interval has fast growth F and H growth H_after, (3) implies

\[
\boxed{F+\tfrac12H_{\rm after}\ge2p-10.}\tag{4}
\]

In the special case of a nonempty **fast-only tail**, with \(n\ge1\) fast events, the terminal low offset must be 0 or 6, and \(G_F=2T_F+\Delta X\) gives the sharper \(G_F\ge2p-4\). Unlike (4), the bound (4) works with arbitrary short-H/long-H/fast interleaving.

Select **disjoint completed** intervals of the form (up-jump followed by its first low return). Let N be the interval count and let \(J=\sum(p_j-1)\) be the H growth contributed by just the initiating prime events. Let G,H denote **whole-path** horizon growth and selective growth. Because the following event intervals are disjoint and exclude all the initiating events, summing (4) yields

\[
2J-8N=\sum_j(2p_j-10)\le(G-H)+\tfrac12(H-J).
\]

Thus

\[
\boxed{5J\le2G-H+16N.}\tag{5}
\]

Since \(p_j-1\ge12\), also \(N\le J/12\), giving the alphabet-free corollary

\[
\boxed{J\le\tfrac3{11}(2G-H).}\tag{6}
\]

These are inequalities for a **subcollection of completed up-jumps**, not a bound on all H events.

## 4. One unfinished terminal excursion can be included by charging terminal offset

There may be one *last* up-jump without a later return to \(X\le10\) before the path ends. Let J now sum **all** selected up-jump initiating H events, including this at-most-one unfinished event, and let N count all selected up-jumps. For an unfinished excursion, (3) plus the remaining endpoint offset gives

\[
F_{\rm after}+\tfrac12 H_{\rm after}+
\max(0,X_f-10)\ge2p-10.
\]

Summing disjoint excursions exactly as before yields the **unified completed-or-unfinished ledger**

\[
\boxed{5J\le2G-H+16N+2\max(0,X_f-10).}\tag{7}
\]

The extra endpoint term represents offset acquired but not yet spent on returning low. This closes a *bookkeeping* gap in prior reset analyses, not the global Cap B proof. A giant final offset is in fact useful for avoiding the crossing in the fixed-sample offset approach, so the extra term need not be small.

## 5. Full-gcd replays and a nearly tight unfinished example

The companion script replays exactly 37 hits from the certified \(M=45895573\) record and 26 hits from the previously studied \(M=5875882249\) record-shaped start. It verifies each full gcd and all earlier unit positions. The results are:

| M | hits | whole G | whole H | completed up-jump groups | unfinished up-jump |
| ---: | ---: | ---: | ---: | --- | --- |
| 45,895,573 | 37 | 1,914 | 766 | event 3, p=73 -> low return at event 36 | none |
| 5,875,882,249 | 26 | 30,564 | 30,370 | event 8, p=73 -> low return at event 15 | event 18, p=30,097 -> X=60,200 |

For the second trajectory the terminal offset is \(X_f=60,276\), \(J=(73-1)+(30097-1)=30168\), \(N=2\). Thus (7) becomes

\[
\underbrace{5J}_{150840}\le
\underbrace{2G-H+16N+2(X_f-10)}_{151322}.
\]

The slack is **only 482**, showing that the unfinished-tail accounting is quantitatively relevant to real local trajectories. No conclusion about universal capped record behavior is claimed.

For a *hypothetical* first crossing at \(M=45895573\) with exact \(G=15393654\), the earlier analysis requires \(H\ge13509117\). Then the completed-only estimate (6) forces

\[
\boxed{J_{\rm completed}\le4712233,\quad
H-J_{\rm completed}\ge8796884.}
\]

So completed low-offset up-jump/recovery cycles alone cannot explain the extremely high H needed at that near-minimal-G crossing; other H contributions would have to dominate. This is a **conditional** diagnostic, not the exclusion of a crossing.

## 6. Quantitative bound on the jump primes at the official cutoff

For an event at a predecessor index \(s\le K=\lfloor(7M-1)/4\rfloor\), the existing Lean first-hit estimate is

\[
g\,p\le2(C+1),\qquad C=D(s)\le2K.
\]

At low pre-offset \(X\le10\), the **up-jump** branch in the table has \(g\ge(3p-11)/2\); therefore \(p(3p-11)\le4(2K+1)\). The **direct low** branch has \(g\ge(p-11)/2\), hence \(p(p-11)\le4(2K+1)\).

For the official threshold \(M=45895573,\ K=80317252\), arithmetic gives the conservative odd-integer bounds

\[
\boxed{p_{\rm up}\le14635,\qquad p_{\rm direct}\le25353.}\tag{8}
\]

They apply only to **long H primes whose event begins at X≤10** and before the fixed cutoff. Long H events beginning at high offset are not subject to these narrower limits.

## 7. Remaining arithmetic obstruction

The interleaving-robust completed ledger (5) and unfinished ledger (7) are **new paper inequalities requiring no fixed exceptional-prime alphabet**. They do not bound total H, because (i) direct-low long H hits may carry large H without a high jump, (ii) H at already-high-offset states is not charged as an initiating jump, and (iii) even completed low-up-jump returns may occur many times. All are compatible with the synthetic non-record first-hit constructions in the existing `canonical_toll.md`.

The remaining genuinely global requirement is to bound these uncharged classes **on actual attained canonical record histories** (or derive a slow interval/twin-prime horizon another way). No universal Cap B or twin-prime theorem follows from the current ledger.
