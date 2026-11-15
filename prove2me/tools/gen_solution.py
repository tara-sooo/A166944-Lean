"""Generate a self-contained solution, ordered topologically.

Two earlier attempts failed for reasons worth recording:

  1. A single reachability pass from the target missed helpers that the inlined
     proofs reference.
  2. Sorting the inlined declarations by (module, startLine) put a user before
     its definition -- `record_index_and_twin_prime_of_twin_travel_bound_from_45895573`
     at line 28 refers to the `22933441` version defined at line 55 -- and Lean
     does not allow forward references, so the file did not compile even though
     every name was present.

The fix is to order by the dependency graph rather than by source position:
emit a declaration only after everything in its typeDeps and valueDeps has been
emitted. Restricting to project declarations that are actually inlined keeps the
graph acyclic (the extractor records project-internal edges only).
"""
import json, os, re, sys

GRAPH = '/data/data/com.termux/files/home/tmp-a166check/decl_graph_tt.jsonl'
REPO  = '/data/data/com.termux/files/home/A166944-Lean'
OUT   = '/data/data/com.termux/files/home/A166944-Lean/prove2me/solutions/Sol_target_of_travel.lean'
TARGET = 'A166944Research.record_index_and_twin_prime_of_twin_travel_bound_from_45895573'

rows = {}
for l in open(GRAPH):
    d = json.loads(l); rows[d['name']] = d

DEF_NAMES = {
 'A166944Research.a','A166944Research.d','A166944Research.D',
 'A166944Research.IsDifferenceRecord','A166944Research.IsGreaterTwinPrime',
 'A166944Research.Target','A166944Research.IsMovingHorizonState',
 'A166944Research.IsMovingHorizonStep','A166944Research.HasMovingHorizonPathTo',
 'A166944Research.IsAttainedPreviousMaximum',
}

src = {}
def lines_of(mod):
    if mod not in src:
        src[mod] = open(os.path.join(REPO, 'A166944', mod.split('.')[-1] + '.lean'),
                        encoding='utf-8', errors='replace').read().split('\n')
    return src[mod]

def span(mod, s, e):
    L = lines_of(mod); s -= 1; e -= 1
    while s-1 >= 0:
        p = L[s-1].strip()
        if p.startswith('@['): s -= 1; continue
        if p.endswith('-/'):
            j = s-1
            while j >= 0 and not L[j].strip().startswith('/--'): j -= 1
            s = j; continue
        break
    return '\n'.join(L[s:e+1])

# --- 1. closure over the graph, iterated to a fixed point -------------------
wanted = {TARGET}
changed = True
while changed:
    changed = False
    for n in list(wanted):
        r = rows.get(n)
        if not r: continue
        for f in ('typeDeps', 'valueDeps'):
            for dep in r.get(f) or []:
                if dep in rows and dep not in wanted and dep not in DEF_NAMES:
                    wanted.add(dep); changed = True

# --- 2. topological order over the inlined set ------------------------------
inlined = {n for n in wanted if n not in DEF_NAMES and rows.get(n)
           and int(rows[n]['startLine'] or 0)}
deps_of = {}
for n in inlined:
    r = rows[n]
    deps_of[n] = {d for f in ('typeDeps','valueDeps') for d in (r.get(f) or []) if d in inlined and d != n}

order, state = [], {}
def visit(n, stack):
    st = state.get(n)
    if st == 2: return
    if st == 1:
        # a cycle among inlined declarations; break it by emitting in place
        return
    state[n] = 1
    for d in sorted(deps_of.get(n, ())):
        visit(d, stack + [n])
    state[n] = 2
    order.append(n)

for n in sorted(inlined):
    visit(n, [])
joined = [n for n in order if n in inlined]

body = '\n\n'.join(span(rows[n]['module'], int(rows[n]['startLine']), int(rows[n]['endLine'])) for n in joined)

# --- 3. sanity: no forward reference ---------------------------------------
defined_so_far = set()
problems = []
for n in joined:
    short = n.split('.')[-1]
    for d in deps_of.get(n, ()):
        ds = d.split('.')[-1]
        if d in joined and joined.index(d) > joined.index(n):
            problems.append(f'{short} uses {ds} defined later')
    defined_so_far.add(short)
print('inlined:', len(joined))
print('forward references:', problems[:5] if problems else 'NONE')
print('body:', body.count(chr(10))+1, 'lines')

sol = f'''import Definitions.Def_a166944_record_core
import Definitions.Def_a166944_moving_horizon

/-!
Self-contained solution for the platform target
`A166944Research.a166944_target_of_travel`.

`TwinPrimeTravelBoundFrom 45895573` unfolds to the hypothesis the target states,
and the proof is `record_index_and_twin_prime_of_twin_travel_bound_from_45895573`
applied to the record, taking the second component. Helper lemmas from the source
project are inlined below in dependency order -- not source order, which matters
because Lean rejects forward references.
-/

open A166944Research

namespace A166944Research

{body}

end A166944Research

open A166944Research in
theorem solution
    (htravel : ∀ {{M sf Cf p : Nat}}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 2 * (sf - (M + 2)) ≤ M) :
    ∀ R : Nat, 5 < R → IsDifferenceRecord R → IsGreaterTwinPrime R := by
  intro R hR hrec
  obtain ⟨n, hn, hd, hprior⟩ := hrec
  exact (record_index_and_twin_prime_of_twin_travel_bound_from_45895573
    htravel hR hn hd hprior).2
'''
open(OUT, 'w').write(sol)
print('wrote', OUT, len(sol), 'bytes')
