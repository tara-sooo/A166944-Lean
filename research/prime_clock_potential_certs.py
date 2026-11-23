#!/usr/bin/env python3
"""Integer-only certificates for LOW7 nonseparability and pairwise clock potential.

Reproduce: python3 research/prime_clock_potential_certs.py
The exact packed certificate data are beside this script in two .b85 files.
No LP solver or third-party Python packages are needed to VERIFY these claims.
"""
import base64
import json
import zlib
from collections import defaultdict
from pathlib import Path

PAIRWISE_PACKED = Path(__file__).with_name("low7_pairwise_potential.b85").read_text().strip()
LOCAL_DUAL_PACKED = Path(__file__).with_name("low7_local_dual.b85").read_text().strip()

def unpack(s):
    return json.loads(zlib.decompress(base64.b85decode(s)).decode("utf8"))

def edges():
    P = 105
    for t in range(2 * P):
        for h in range(P):
            C = 2 * h
            best = 10**9
            d = 1
            for p in (3, 5, 7):
                if (C - 1) % p == 0:
                    r = 0
                elif (C + 1) % p == 0:
                    r = p + 2
                else:
                    continue
                g = (r - t) % (2 * p) or 2 * p
                if g < best:
                    best, d = g, p
                elif g == best:
                    d *= p
            if d == 1:
                continue
            nt = (t + best) % (2 * P)
            nh = (h + (d - 1) // 2) % P
            yield (t, h, nt, nh, best, d)

def main():
    P = 105
    es = list(edges())
    assert len(es) == 18900
    v = unpack(PAIRWISE_PACKED)
    z = unpack(LOCAL_DUAL_PACKED)
    sizes = (15, 21, 35)
    offset = (0, 450, 1332)
    assert len(v) == 3782 and len(z) == 133
    assert all(isinstance(w, int) and w >= 0 for w in v)

    # Positive certificate: V = f_35 + f_37 + f_57 on CRT-local states.
    def pot(t, h):
        return sum(v[o + (t % (2 * b)) * b + (h % b)]
                   for o, b in zip(offset, sizes))
    for t, h, nt, nh, gap, d in es:
        assert pot(t, h) >= gap + pot(nt, nh)
    largest = max(pot(t, h) for t in range(210) for h in range(105))
    assert largest == 268

    # Negative certificate: a nonzero integer circulation after projection to
    # EACH separate prime-coordinate. Any V=f_3+f_5+f_7 would have zero
    # weighted total drop, but total weighted elapsed clock time is positive.
    balance = defaultdict(int)
    last = -1
    weighted_gap = 0
    for idx, w in z:
        assert isinstance(idx, int) and isinstance(w, int) and w > 0
        assert last < idx < len(es)
        last = idx
        t, h, nt, nh, gap, d = es[idx]
        weighted_gap += w * gap
        for p in (3, 5, 7):
            balance[(p, t % (2 * p), h % p)] -= w
            balance[(p, nt % (2 * p), nh % p)] += w
    assert all(b == 0 for b in balance.values())
    assert weighted_gap == 1240352399315487570

    # Independent dynamic-programming replay on the complete functional graph.
    nxt = [-1] * (2 * P * P)
    step = [0] * len(nxt)
    growth = [0] * len(nxt)
    for t, h, nt, nh, gap, d in es:
        idx = t * P + h
        nxt[idx] = nt * P + nh
        step[idx] = gap
        growth[idx] = d - 1
    status = bytearray(len(nxt))
    time_budget = [0] * len(nxt)
    gain_budget = [0] * len(nxt)
    event_budget = [0] * len(nxt)
    for first in range(len(nxt)):
        if status[first] == 2:
            continue
        stack = []
        x = first
        while x != -1 and status[x] == 0:
            status[x] = 1
            stack.append(x)
            x = nxt[x]
        assert x == -1 or status[x] == 2, "Unexpected LOW7 cycle"
        while stack:
            y = stack.pop()
            znext = nxt[y]
            if znext == -1:
                time_budget[y] = gain_budget[y] = event_budget[y] = 0
            else:
                time_budget[y] = step[y] + time_budget[znext]
                gain_budget[y] = growth[y] + gain_budget[znext]
                event_budget[y] = 1 + event_budget[znext]
            status[y] = 2
    assert max(time_budget) == 56
    assert max(gain_budget) == 106
    assert max(event_budget) == 9
    print("CLOCK_POTENTIAL_CERT_PASS states=22050 transitions=18900 "
          "max_time=56 max_growth=106 max_events=9 "
          "pairwise_max=268 negative_local_dual_edges=133 "
          f"negative_local_weighted_gap={weighted_gap}")

if __name__ == "__main__":
    main()
