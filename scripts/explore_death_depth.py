#!/usr/bin/env python3
"""Static order, uniformly random values sigma, no domination.  Pruning clauses
are created on the non-preferred side (N3); the node dies when a single clause
is violated or when the sum of the live clauses is violated (N4).  Reported:
the depth (fraction of n) at which a random sigma dies, for single-clause
checks alone and with the sum check.  By Knuth's identity the search has
2^t * P[sigma survives t steps] nodes at depth t, so this is the quantity a
running-time proof has to control.
  python3 explore_death_depth.py 400,1600      (about 15 seconds)"""
import random, statistics, sys

def formula(n, d, rng):
    p = d / (n - 1)
    adj = [[] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                si, sj = rng.choice((1, -1)), rng.choice((1, -1))
                adj[i].append((j, si, sj)); adj[j].append((i, sj, si))
    return adj

def lit_true(val, s):
    return val == (1 if s == 1 else 0)

def death(adj, sigma, use_sum):
    n = len(adj)
    P = [[0, 0] for _ in range(n)]
    for x in range(n):
        for (v, sx, sv) in adj[x]:
            P[x][0 if sx == -1 else 1] += 1
    A = [None] * n
    clauses = []            # [support dict {w: bad}, slack k, R, alive]
    occ = [[] for _ in range(n)]
    m = [[0, 0] for _ in range(n)]
    total_min = 0           # sum over free w of min(m0, m1), live clauses only
    total_slack = 0
    def add_w(w, bad, sgn):
        nonlocal total_min
        old = min(m[w])
        m[w][bad] += sgn
        total_min += min(m[w]) - old
    for t in range(n):
        x = t
        pos = P[x][0] <= P[x][1]
        val = sigma[t]
        if (val == 1) != pos and sum(P[x]) > 0:          # non-preferred: new clause
            lsign = 1 if pos else -1
            sup = {}
            for (v, sx, sv) in adj[x]:
                if A[v] is None:
                    sup[v] = (0 if sv == 1 else 1) if sx == lsign else (1 if sv == 1 else 0)
            k = P[x][0 if pos else 1] - 1
            c = [sup, k, len(sup), True]
            if k < len(sup):
                clauses.append(c)
                for w, bad in sup.items():
                    occ[w].append(c); add_w(w, bad, +1)
                total_slack += k
            else:
                c[3] = False
        # assign x
        A[x] = val
        total_min -= min(m[x])
        for (v, sx, sv) in adj[x]:
            if A[v] is None:
                if not lit_true(val, sx): P[v][0 if sv == 1 else 1] -= 1
                else: P[v][1 if sv == 1 else 0] -= 1
        for c in occ[x]:
            if not c[3]:
                continue
            bad = c[0][x]
            c[2] -= 1
            if val == bad:
                c[1] -= 1; total_slack -= 1
                if c[1] < 0:
                    return t + 1, "clause"
            if c[2] <= c[1]:                                 # vacuous: drop from the sum
                c[3] = False
                total_slack -= c[1]
                for w, b in c[0].items():
                    if A[w] is None:
                        add_w(w, b, -1)
        if use_sum and total_min > total_slack:
            return t + 1, "sum"
    return n, "leaf"

rng = random.Random(5)
n_list = [int(a) for a in sys.argv[1].split(",")]
for n in n_list:
    for d in (16, 64, 256, (n - 1) / 2):
        if d >= n: continue
        adj = formula(n, d, rng)
        res1, res2 = [], []
        for _ in range(30):
            sigma = [rng.randrange(2) for _ in range(n)]
            res1.append(death(adj, sigma, False)[0] / n)
            res2.append(death(adj, sigma, True)[0] / n)
        print(f"n={n:4d} d={d:6.1f}: median death depth  single clauses {statistics.median(res1):.3f}"
              f"   with the sum {statistics.median(res2):.3f}  (quartiles {sorted(res2)[7]:.3f}-{sorted(res2)[22]:.3f})", flush=True)
