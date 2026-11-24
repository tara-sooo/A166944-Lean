#!/usr/bin/env python3
from math import isqrt
import sys


def audit(X):
    B = isqrt(7*X-1)+1
    spf = list(range(7*X+4))
    for p in range(2, isqrt(len(spf)-1)+1):
        if spf[p] == p:
            for j in range(p*p, len(spf), p):
                if spf[j] == j:
                    spf[j] = p
    def hit(t, C, K):
        best = (K+1, 0)
        for sig in (-1, 1):
            v = C+sig
            while v > 1:
                p = spf[v]
                if p > B:
                    break
                if p > 2:
                    r = 0 if sig == -1 else p+2
                    n = t+1+(r-t-1)%(2*p)
                    best = min(best, (n,p))
                while v%p == 0:
                    v //= p
        return best
    events = tests = squares = maxlen = 0
    example = None
    for M in range(X+1, 2*X, 2):
        t, C, K = M+2, 2*M-2, (7*M-1)//4
        labels, signs = [], []
        while True:
            n,p = hit(t,C,K)
            if n > K:
                break
            labels.append(p)
            signs.append(-1 if (C-1)%p == 0 else 1)
            t,C = n,C+p-1
        events += len(labels)
        maxlen = max(maxlen, len(labels))
        for i in range(len(labels)):
            for k in range(1,(len(labels)-i)//2+1):
                if labels[i:i+k] != labels[i+k:i+2*k]:
                    continue
                squares += 1
                assert signs[i:i+k] != signs[i+k:i+2*k]
                if example is None:
                    example = (M,i,labels[i:i+k],signs[i:i+k],signs[i+k:i+2*k])
                if i+3*k <= len(labels):
                    tests += 1
                    assert labels[i:i+k] != labels[i+2*k:i+3*k]
    print(f'X={X} B={B} events={events} maxlen={maxlen} squares={squares} third_copy_checks={tests} example={example}',flush=True)


if __name__ == '__main__':
    for x in map(int,sys.argv[1:]):
        audit(x)
