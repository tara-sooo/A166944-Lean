#!/usr/bin/env python3
"""Exact controlled LOW7 automaton, Bellman minimization and additive potential tests."""
from heapq import heappop, heappush

PRIMES = (3, 5, 7)
P = 105
N = 2 * P * P


def detail(t, h):
    C = 2 * h
    active = []
    for p in PRIMES:
        if (C - 1) % p == 0:
            r = 0
        elif (C + 1) % p == 0:
            r = p + 2
        else:
            continue
        g = (r - t) % (2 * p) or 2 * p
        active.append((g, p))
    if not active:
        return 0, (), (), ()
    gap = min(g for g, p in active)
    tied = tuple(p for g, p in active if g == gap)
    choices = []
    for mask in range(1, 1 << len(tied)):
        d = 1
        for j, p in enumerate(tied):
            if mask & (1 << j):
                d *= p
        choices.append(d)
    return gap, tied, tuple(sorted(choices)), tuple(active)


def main():
    clock = [0] * N
    activity = [0] * N
    edges = [[] for _ in range(N)]
    rev = [[] for _ in range(N)]
    heap = []
    first_bad = {}
    for t in range(2 * P):
        for h in range(P):
            idx = t * P + h
            gap, tied, choices, active = detail(t, h)
            clock[idx] = sum(g for g, p in active)
            activity[idx] = sum(2 * p for _, p in active)
            if not choices:
                heappush(heap, (0, idx))
                continue
            nt = (t + gap) % (2 * P)
            for d in choices:
                nh = (h + (d - 1) // 2) % P
                to = nt * P + nh
                edges[idx].append((to, d, gap))
                rev[to].append((idx, gap))

    for weights in ((1, 1, 1), (1, 2, 3), (3, 5, 7), (1, 3, 9)):
        for model in ('gap', 'active'):
            bad = 0
            for t in range(2 * P):
                for h in range(P):
                    idx = t * P + h
                    if not edges[idx]:
                        continue
                    gap, tied, choices, ac = detail(t, h)
                    def potential(s):
                        st, sh = divmod(s, P)
                        _, _, _, active = detail(st, sh)
                        if model == 'gap':
                            return sum(weights[PRIMES.index(p)] * g for g, p in active)
                        return sum(2 * p * weights[PRIMES.index(p)] for _, p in active)
                    lhs = potential(idx)
                    rhs = min(gap + potential(nxt) for nxt, d, _ in edges[idx])
                    if lhs < rhs:
                        bad += 1
                        first_bad.setdefault((model, weights), (t, h, gap, tied, choices, lhs, rhs))
            print('LOW7_CONTROL_SEPARABLE_TEST', model, weights, 'badStates=', bad, 'example=', first_bad.get((model, weights)))

    INF = 10 ** 10
    optimal = [INF] * N
    for d, state in heap:
        optimal[state] = 0
    while heap:
        d, state = heappop(heap)
        if d != optimal[state]:
            continue
        for before, gap in rev[state]:
            nd = d + gap
            if nd < optimal[before]:
                optimal[before] = nd
                heappush(heap, (nd, before))
    assert all(v < INF for v in optimal)
    assert all(optimal[s] <= gap + optimal[nxt] for s in range(N) for nxt, _, gap in edges[s])
    assert all(not edges[s] or optimal[s] == min(gap + optimal[to] for to, _, gap in edges[s]) for s in range(N))
    winners = sum(any(optimal[s] < gap + optimal[to] for to, _, gap in edges[s]) for s in range(N) if edges[s])
    print('CONTROLLED_LOW7_OPTIMAL_PASS states=', N, 'max_optimal_time=', max(optimal), 'original_product_max_time=56', 'strictly_inferior_branches=', winners)

    # Deterministic policy graphs on *all* LOW7 residues, no canonical or time cutoff.
    for policy in ('PRODUCT','MIN','MAX','MIN_ACTIVE','MAX_WAIT'):
        nxt=[-1]*N;cost=[0]*N;inc=[0]*N
        for t in range(2*P):
            for h in range(P):
                v=t*P+h
                g,tied,choices,ac=detail(t,h)
                if not choices:continue
                nt=(t+g)%(2*P)
                if policy=='PRODUCT':choice=max(choices)
                elif policy=='MIN':choice=min(choices)
                elif policy=='MAX':choice=max(tied)
                elif policy=='MIN_ACTIVE':
                    choice=min(choices,key=lambda d:(len(detail(nt,(h+(d-1)//2)%P)[3]),d))
                elif policy=='MAX_WAIT':
                    choice=min(choices,key=lambda d:(-detail(nt,(h+(d-1)//2)%P)[0] if detail(nt,(h+(d-1)//2)%P)[2] else -100000000,d))
                nxt[v]=nt*P+(h+(choice-1)//2)%P
                cost[v]=g;inc[v]=choice-1
        status=bytearray(N);travel=[0]*N;growth=[0]*N;events=[0]*N;cycle=None
        for start in range(N):
            if status[start]==2:continue
            chain=[];v=start
            while v>=0 and status[v]==0:
                status[v]=1;chain.append(v);v=nxt[v]
            if v>=0 and status[v]==1:
                cycle=(v,len(chain));break
            for w in reversed(chain):
                z=nxt[w];travel[w]=cost[w]+(travel[z] if z>=0 else 0)
                growth[w]=inc[w]+(growth[z] if z>=0 else 0)
                events[w]=(1+events[z]) if z>=0 else 0
                status[w]=2
        if cycle:
            print('LOW7_POLICY_CYCLE',policy,'witness=',cycle)
        else:
            print('LOW7_POLICY_FINITE_PASS',policy,'maxTime=',max(travel),'maxGrowth=',max(growth),'maxEvents=',max(events))

if __name__ == '__main__':
    main()
