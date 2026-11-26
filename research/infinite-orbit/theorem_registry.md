# Initial constraint registry — hypothesis and semantic scope

Pinned baseline main bd180e3de0fe6e12cc3c3ea25d65a985445344eb; direct 3e19d7e945788d39b12a17744c2139970e90da8d; unified 6ec6ce3cc11afb8efa86611cc8c6eabf0aa872fa. This is a first-pass registry, not an exhaustive declaration inventory. "Paper" is not Lean verification; computational evidence is not promoted to universal constraints.

| ID | Result / constraint | Domain and required hypothesis | Status in source | Virtual model I |
|---|---|---|---|---|
| L01 | parity gcd, first hit and horizon update | canonical odd root; uncut or adaptive with eligibility | main recurrence gcd Lean; MIN transfer paper | finite exact lift |
| L02 | C<=2t; ordinary deficit d>=0; d'=d+2w-g | canonical MIN; g=p-1 | direct paper | relative proof |
| L03 | w<=2p; -g<=delta d<=5g | actual MIN event on unchanged plateau | direct paper | relative proof |
| L04 | adaptive pool p^2<=C+1; stops iff C±1 prime | standard integer C>=4 | direct paper | finite lift only; no absolute order |
| L05 | under finite twins above last center every adaptive trajectory infinite | standard integer; finite twins | direct paper conditional | virtual infinite events proved independently, not standard arithmetic |
| L06 | bounded label set cannot cross common even multiple; labels unbounded | unbounded gain, selected divisibility | direct paper | translated barrier proof |
| L07 | finite transcript CRT with composite neighbors | uncut, adaptive transfer requires eligibility | direct 425a4b9 paper + audit | generalized compatible ensemble construction |
| D01 | single-band deficit-chain sieve and product lower bound | actual standard window, selected nonresets in factor-two sqrt band, deficit cap, appropriate polylog closeness and witness-free hypothesis | direct 3793617 paper; actual higher-window finite coverage absent in source | not imposed |
| D02 | limsup (U+V)/(sqrt X log^gamma X)=infinity, 0<gamma<5/6 | hypothetical actual fixed canonical infinite ray, finite twins, arbitrary chosen factor-two near-sqrt band populations; geometric blocks | direct 3793617 paper conditional | not imposed |
| D03 | low-label gain / outside positive variation supply on disjoint pinned corridors | actual block, designated completed corridors, no offset witness; K>2V, S^2<=H+1, L>4S; see exact inequalities (3)-(6) | direct 3e19d7e paper + finite audit | not imposed; standard offset witnesses retained |
| U01 | A_mu=int alpha dmu=o(NT); int(1-phi)dmu=o(NT) | original dense source ensemble, actual forward assignment, finite twins | unified 6ec6ce3 cites prior paper | not imposed |
| U02 | F_late^mu(S)<=sqrt(2 k_S c_a N(H+Pmax) A_mu) | actual assigned missing focal mass, stable classes, k_S=1+floor(4H/S) | unified 6ec6ce3 paper | not imposed |
| U03 | bounded quotient mutual sample S_quot<=2d sqrt(M A_mu) | exact original two missing draws; high discovery graph, d=2 floor(Q) K | unified 6ec6ce3 paper | not imposed |
| U04 | homogeneous fan/comb necessary bounds | stable actual same-code trie, exact radical/lag hypotheses | unified 6ec6ce3 paper | not imposed |
| U05 | local lifetime deficit sieve forces macro missing in specified medium-band bounded-budget regime | actual source block with all specified gain, size and variation hypotheses | unified 6ec6ce3 paper conditional | not imposed |
| X01 | universal macro missing lower bound; remaining early large-quotient/small-label supply; final contraction | unified target | OPEN, not constraints | not imposed |
| R01 | actual A166944 record-index/twin classification and travel target | full original GCD recurrence, canonical record ancestry and specific target hypotheses | main partial Lean, final open | separate semantic domain; no blanket transfer |

Primary sources: [direct basic](https://github.com/tara-sooo/A166944-Lean/blob/425a4b9a32e8a4a808582eb75d06cfecb7c56f0a/research/2026-11-25-min-direct-arithmetic.md), [direct chains](https://github.com/tara-sooo/A166944-Lean/blob/3793617fd82ac3fa0b68679a57529fce233b3660/research/2026-11-26-min-direct-deficit-chain-sieve-and-global-log-obstruction.md), [direct corridors](https://github.com/tara-sooo/A166944-Lean/blob/3e19d7e945788d39b12a17744c2139970e90da8d/research/2026-11-26-min-direct-thickened-cut-recovery-and-local-supply.md), [unified XIX](https://github.com/tara-sooo/A166944-Lean/blob/6ec6ce3cc11afb8efa86611cc8c6eabf0aa872fa/research/2026-11-26-min-unified-radical-fan-lifetime-sieve.md), [main README](https://github.com/tara-sooo/A166944-Lean/blob/bd180e3de0fe6e12cc3c3ea25d65a985445344eb/README.md).

Next registry expansion: extract exact statements and dependency graph from all applicable MIN research notes and formal modules; identify fixed cutoff vs adaptive transfer conditions; separate actual source density from arbitrary finite ensemble. No constraint may be promoted just because a finite audit passed.

## Checkpoint II — scope separation

[Scale and tomography note](https://github.com/tara-sooo/A166944-Lean/blob/3343213ef21d2d4fc5836283e0b9664cd92f6fce/research/infinite-orbit/scale_and_tomography.md). Latest direct cut source [2a47be1](https://github.com/tara-sooo/A166944-Lean/blob/2a47be177db12d7fdcdc99daf9dfe7be0403da34/research/2026-11-26-min-direct-grouped-cut-sieve-and-all-label-corridors.md).

| ID | Constraint | Residue ensemble I | Scalar clock model II-B |
|---|---|---|---|
| L08 | common-root positive event congruence / finite CRT bound; all-prime tomography | exact; proves bare indexed ensemble has no standard common base | not imposed on multiple roots |
| L09 | absolute adaptive magnitude p²<=H+1 | finite lift only | exact |
| L10 | selected side time congruence | exact | exact |
| L11 | selected side neighbor divisibility; earliest competition | exact relative rule | not imposed; finite audit reports failures |
| D02 | global U+TV logarithmic lower bound (aggregate numerical condition) | not transferable | satisfied numerically with TV=Theta(X), not an application of actual-ray theorem |
| D04 | all-label endpoint corridor demand, exact anchor negligible mass, eroded deep-bypass bound (source (5),(7),(8)) | not transferable | all endpoints safe, zero anchor/endpoint demand, bypass mass G+o(X) by arithmetic cut distribution |
| D01 | high-band sublinear deficit-cap chain theorem | not imposed | hypotheses not met |
| U01–U05 | dense actual source allocation / collision and missing supply | not imposed | not imposed |

These columns refer to DIFFERENT structures; their intersection remains open. The finite common-root obstruction uses only positive event congruences, not artificial factors. The scalar construction does not license an inference from selected time clocks to actual first-hit recurrence. No full theorem inventory or Lean verification yet.
