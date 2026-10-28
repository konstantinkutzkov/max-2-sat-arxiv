#!/usr/bin/env python3
"""Branching strategies, and the sum of the active pruning clauses.

DPLL + domination + pruning clauses on random balanced formulas (every pair of
variables carries one clause with probability p, signs uniform).

Variable selection
  random order     a fixed random order
  inside clauses   branch on a variable of the active pruning clause that is
                   most likely to be violated, P[Bin(R, 1/2) >= slack] maximal
                   (R = unassigned support, slack = true literals still allowed)

Checks
  per-clause       cut when one pruning clause is violated
  sum              also cut when the sum of the active clauses is violated:
                       sum_{w unassigned} min(m0_w, m1_w)  >  sum_i slack_i,
                   where w is a pruning literal of m1_w active clauses as w
                   and of m0_w as ~w; whatever value w gets, min(m0_w, m1_w)
                   of these literals are true.  Clauses that can no longer be
                   violated are left out (they would only add slack).  Sound,
                   since the sum is implied by the clauses.

Tree sizes are estimated by population splitting: keep M random live nodes of
each branching depth, expand all their children, estimate the number of live
nodes of the next depth, resample.  The estimate is unbiased.

  python3 explore_sum_rule.py check      soundness against brute force, and the
                                         estimator against exact tree sizes
  python3 explore_sum_rule.py density    n = 400, average degree 16 .. 200
  python3 explore_sum_rule.py dense      dense formulas, n = 50 .. 400
The last two take tens of minutes each.  Reported: the saving n - log2(tree).
"""
import itertools
import math
import random
import sys

import numpy as np

sys.setrecursionlimit(10000)
TAIL = {}


def tail(R, s):
    """P[Bin(R, 1/2) >= s]."""
    if s <= 0:
        return 1.0
    if s > R:
        return 0.0
    if (R, s) not in TAIL:
        TAIL[(R, s)] = sum(math.comb(R, k) for k in range(s, R + 1)) / 2 ** R
    return TAIL[(R, s)]


def formula(n, p, rng):
    """adj[x] = list of (other variable, sign of x, sign of other)."""
    adj = [[] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                si, sj = rng.choice((1, -1)), rng.choice((1, -1))
                adj[i].append((j, si, sj))
                adj[j].append((i, sj, si))
    return adj


def lit_true(val, s):
    return val == (1 if s == 1 else 0)


class State:
    """P[v] = [deficit of v, deficit of ~v]; A = assignment; free = #unassigned;
    cl = pruning clauses [bad values {w: (value, weight)}, threshold, count,
    unassigned support R, weight vector for bad value 0, for bad value 1]."""
    __slots__ = ("P", "A", "cl", "free")

    def copy(self):
        s = State()
        s.P = [r[:] for r in self.P]
        s.A = self.A[:]
        s.cl = [c[:] for c in self.cl]          # dicts and vectors are shared
        s.free = self.free
        return s


def root(adj):
    s = State()
    s.P = [[0, 0] for _ in adj]
    for x in range(len(adj)):
        for (v, sx, sv) in adj[x]:
            s.P[x][0 if sx == -1 else 1] += 1
    s.A = [None] * len(adj)
    s.cl = []
    s.free = len(adj)
    return s


def assign(adj, s, x, val):
    """Assign x, update deficits and clause counts; False if a clause is violated."""
    s.A[x] = val
    s.free -= 1
    for (v, sx, sv) in adj[x]:
        if s.A[v] is None:
            if not lit_true(val, sx):
                s.P[v][0 if sv == 1 else 1] -= 1
            else:
                s.P[v][1 if sv == 1 else 0] -= 1
    ok = True
    for c in s.cl:
        e = c[0].get(x)
        if e is not None:
            c[3] -= e[1]
            if val == e[0]:
                c[2] += e[1]
                if c[2] >= c[1]:
                    ok = False
    return ok


def closure(adj, s):
    """Domination until nothing changes; False if a clause gets violated."""
    changed = True
    while changed:
        changed = False
        for v in range(len(adj)):
            if s.A[v] is None and (s.P[v][0] <= 0 or s.P[v][1] <= 0):
                if not assign(adj, s, v, 1 if s.P[v][0] <= 0 else 0):
                    return False
                changed = True
    return True


def sum_violated(s):
    rows0, rows1, slack = [], [], 0
    for c in s.cl:
        sl = c[1] - 1 - c[2]
        if sl < 0 or c[3] <= sl:
            continue
        rows0.append(c[4])
        rows1.append(c[5])
        slack += sl
    if not rows0:
        return False
    free = np.array([a is None for a in s.A])
    m0 = np.sum(rows0, axis=0)[free]
    m1 = np.sum(rows1, axis=0)[free]
    return int(np.minimum(m0, m1).sum()) > slack


def choose(s, strategy, order):
    if strategy == "inside clauses":
        live = [c for c in s.cl if c[2] < c[1] and c[3] >= c[1] - c[2]]
        if live:
            c = max(live, key=lambda c: (tail(c[3], c[1] - c[2]), -c[3]))
            return max((w, y) for y, (g, w) in c[0].items() if s.A[y] is None)[1]
    return next(v for v in order if s.A[v] is None)


def children(adj, s, strategy, use_sum, order):
    """The two children of s, as pairs (kind, state) with kind 'dead' (cut),
    'leaf' (all variables assigned) or 'live'."""
    n = len(adj)
    x = choose(s, strategy, order)
    pos = s.P[x][0] <= s.P[x][1]               # preferred literal: x if pos, else ~x
    out = []
    for val in (0, 1):
        t = s.copy()
        if (val == 1) != pos:                   # non-preferred side: new pruning clause
            lsign = 1 if pos else -1
            fav = {}
            w0, w1 = np.zeros(n, dtype=np.int32), np.zeros(n, dtype=np.int32)
            for (v, sx, sv) in adj[x]:
                if t.A[v] is None:
                    bad = (0 if sv == 1 else 1) if sx == lsign else (1 if sv == 1 else 0)
                    g, w = fav.get(v, (bad, 0))
                    fav[v] = (bad, w + 1)
                    (w1 if bad == 1 else w0)[v] += 1
            t.cl.append([fav, t.P[x][0 if pos else 1], 0,
                         sum(w for g, w in fav.values()), w0, w1])
        if not assign(adj, t, x, val) or not closure(adj, t) or (use_sum and sum_violated(t)):
            out.append(("dead", t))
        elif t.free == 0:
            out.append(("leaf", t))
        else:
            out.append(("live", t))
    return out


def estimate_log2(adj, strategy, use_sum, M, rng, order=None):
    """Population-splitting estimate of log2(number of tree nodes)."""
    if order is None:
        order = list(range(len(adj)))
        rng.shuffle(order)
    s = root(adj)
    if not closure(adj, s) or s.free == 0:
        return 0.0
    pop, N, total = [s], 1.0, 1.0
    while pop:
        kids = [k for st in pop for k in children(adj, st, strategy, use_sum, order)]
        total += N * len(kids) / len(pop)
        live = [t for kind, t in kids if kind == "live"]
        if not live:
            break
        N = N * len(live) / len(pop)
        pop = [live[rng.randrange(len(live))] for _ in range(M)] if len(live) > M else live
    return math.log2(total)


def score(adj, A):
    return sum(1 for a in range(len(adj)) for (b, sa, sb) in adj[a]
               if a < b and (lit_true(A[a], sa) or lit_true(A[b], sb)))


def solve(adj, strategy, use_sum, order):
    """Exact search: (number of nodes, best score among the leaves)."""
    s = root(adj)
    if not closure(adj, s):
        return 1, -1
    if s.free == 0:
        return 1, score(adj, s.A)
    nodes, best = 1, -1
    stack = [s]
    while stack:
        for kind, t in children(adj, stack.pop(), strategy, use_sum, order):
            nodes += 1
            if kind == "leaf":
                best = max(best, score(adj, t.A))
            elif kind == "live":
                stack.append(t)
    return nodes, best


def brute(adj):
    n = len(adj)
    return max(sum(1 for a in range(n) for (b, sa, sb) in adj[a]
                   if a < b and (lit_true(A[a], sa) or lit_true(A[b], sb)))
               for A in itertools.product((0, 1), repeat=n))


VARIANTS = [("random order", False), ("inside clauses", False), ("random order", True)]
NAMES = ["random order", "inside clauses", "random order + sum"]


def check():
    rng = random.Random(3)
    changed = 0
    for trial in range(150):
        n = rng.choice((8, 10, 12))
        adj = formula(n, rng.uniform(0.3, 0.9), rng)
        opt = brute(adj)
        order = list(range(n))
        sizes = {}
        for strategy in ("random order", "inside clauses"):
            for use_sum in (False, True):
                nodes, best = solve(adj, strategy, use_sum, order)
                assert best == opt, (trial, strategy, use_sum, best, opt)
                sizes[(strategy, use_sum)] = nodes
        changed += sizes[("random order", False)] != sizes[("random order", True)]
    print(f"150 formulas, n <= 12: optimum always found; the sum changed the tree in {changed}")
    rng = random.Random(12)
    for n in (30, 36):
        adj = formula(n, 0.5, rng)
        order = list(range(n))
        for use_sum in (False, True):
            exact = solve(adj, "random order", use_sum, order)[0]
            est = [2 ** estimate_log2(adj, "random order", use_sum, 8, random.Random(500 + r), order)
                   for r in range(40)]
            print(f"n={n} {'sum' if use_sum else 'per-clause'}: exact log2 {math.log2(exact):.2f},"
                  f" estimate (40 runs, M=8) {math.log2(sum(est) / len(est)):.2f}")


def row(n, d, M, rng, nforms=2):
    forms = [formula(n, min(1.0, d / (n - 1)), rng) for _ in range(nforms)]
    out = []
    for strategy, use_sum in VARIANTS:
        sav = sum(n - estimate_log2(adj, strategy, use_sum, M, rng) for adj in forms) / nforms
        out.append(sav / n)
    return out


def main():
    what = sys.argv[1] if len(sys.argv) > 1 else "check"
    if what == "check":
        check()
    elif what == "density":
        rng = random.Random(1)
        print("n = 400, saving as a fraction of n:   " + " | ".join(NAMES))
        for d in (16, 32, 64, 128, 199.5):
            print(f"  d = {d:5g}:  " + "   ".join(f"{v:.3f}" for v in row(400, d, 50, rng)), flush=True)
    elif what == "dense":
        rng = random.Random(2)
        print("dense (p = 1/2), saving as a fraction of n:   " + " | ".join(NAMES))
        for n in (50, 100, 200, 400):
            print(f"  n = {n:4d}:  " + "   ".join(f"{v:.3f}" for v in row(n, (n - 1) / 2, 50, rng)),
                  flush=True)


if __name__ == "__main__":
    main()
