#!/usr/bin/env python3
"""Availability of near-dominated variables along the tilted walk W.

Formulas in which every variable has a linear gap (relative deficit about
beta0).  Rule: if a counted clause is active, branch inside it (case 2);
otherwise, if a free variable has (p - 1) <= beta' * D and a feasible clause,
branch on the one with the smallest ratio (case 1); otherwise make a plain step.
W: case 1 -> preferred side w.p. 1/lam, non-preferred w.p. 1 - 1/lam;
case 2 -> lam^-drop of the clause transition (normalised); plain -> 1/2.
lam = 2^H(beta'), weights from explore_clause_weights.table.
Reported: the number S of plain steps per walk and log2 E[(2/lam)^S], the
factor by which the bound lam^n E[(2/lam)^S] exceeds lam^n.
  random gap formulas: biased signs, and aligned ((x|y) or (~x|~y))
  C_{n,c}: complete and homogeneous, the extreme case
"""
import math
import random

from explore_clause_weights import table


def biased(n, p_edge, p_pos, rng):
    adj = [[] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p_edge:
                si = 1 if rng.random() < p_pos else -1
                sj = 1 if rng.random() < p_pos else -1
                adj[i].append((j, si, sj))
                adj[j].append((i, sj, si))
    return adj


def aligned(n, p_edge, beta0, rng):
    adj = [[] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p_edge:
                s = -1 if rng.random() < beta0 else 1          # (x|y) or (~x|~y)
                adj[i].append((j, s, s))
                adj[j].append((i, s, s))
    return adj


def lit_true(val, s):
    return val == (1 if s == 1 else 0)


class Walk:
    def __init__(self, adj, lam, beta, eps, rng):
        self.adj, self.lam, self.beta, self.eps, self.rng = adj, lam, beta, eps, rng
        n = len(adj)
        self.P = [[0, 0] for _ in range(n)]
        for x in range(n):
            for (v, sx, sv) in adj[x]:
                self.P[x][0 if sx == -1 else 1] += 1
        self.A = [None] * n
        self.free = n
        self.cl = None          # active clause: [bad value per support var, l, k]
        self.c = math.log(1 / (lam - 1), lam)
        self.dead = False

    def assign(self, x, val):
        self.A[x] = val
        self.free -= 1
        for (v, sx, sv) in self.adj[x]:
            if self.A[v] is None:
                if not lit_true(val, sx):
                    self.P[v][0 if sv == 1 else 1] -= 1
                else:
                    self.P[v][1 if sv == 1 else 0] -= 1
        c = self.cl
        if c is not None and x in c[0]:
            c[1] -= 1
            if val == c[0][x]:
                c[2] -= 1
            if c[2] < 0:
                self.dead = True
            elif c[2] == 0:                       # propagation
                self.cl = None
                for y, bad in c[0].items():
                    if self.A[y] is None:
                        self.assign(y, 1 - bad)
            elif c[2] >= c[1] or self.eps.get((c[1], c[2]), 0.0) <= 0:
                self.cl = None                    # vacuous or released

    def closure(self):
        changed = True
        while changed and not self.dead:
            changed = False
            for v in range(len(self.adj)):
                if self.A[v] is None and (self.P[v][0] <= 0 or self.P[v][1] <= 0):
                    self.assign(v, 1 if self.P[v][0] <= 0 else 0)
                    changed = True
                    if self.dead:
                        return

    def run(self):
        lam, n = self.lam, len(self.adj)
        S, plain_free = 0, []
        while True:
            self.closure()
            if self.dead or self.free == 0:
                return S, plain_free
            c = self.cl
            if c is not None:                                      # case 2
                y = next(v for v in c[0] if self.A[v] is None)
                l, k = c[1], c[2]
                e = self.eps[(l, k)]
                vf = self.eps.get((l - 1, k), 0.0) if k <= l - 2 else 0.0
                vt = self.eps.get((l - 1, k - 1), 0.0) if k >= 2 else float(l - 1)
                pf, pt = lam ** -(1 + vf - e), lam ** -(1 + vt - e)
                bad = c[0][y]
                self.assign(y, bad if self.rng.random() < pt / (pf + pt) else 1 - bad)
                continue
            best = None
            for v in range(n):
                if self.A[v] is None:
                    D = self.P[v][0] + self.P[v][1]
                    p = min(self.P[v])
                    if D >= 2 and p - 1 <= self.beta * D and (p == 1 or self.eps.get((D, p - 1), 0) >= self.c):
                        r = (p - 1) / D
                        if best is None or r < best[0]:
                            best = (r, v)
            if best is not None:                                   # case 1
                x = best[1]
                pos = self.P[x][0] <= self.P[x][1]
                if self.rng.random() < 1 / lam:
                    self.assign(x, 1 if pos else 0)
                else:
                    lsign = 1 if pos else -1
                    fav = {}
                    for (v, sx, sv) in self.adj[x]:
                        if self.A[v] is None:
                            fav[v] = (0 if sv == 1 else 1) if sx == lsign else (1 if sv == 1 else 0)
                    p = self.P[x][0 if pos else 1]
                    self.cl = [fav, len(fav), p - 1]
                    self.assign(x, 0 if pos else 1)
                    c = self.cl
                    if c is not None and c[2] == 0:
                        self.cl = None
                        for y, bad in c[0].items():
                            if self.A[y] is None:
                                self.assign(y, 1 - bad)
                continue
            S += 1                                                 # plain step
            plain_free.append(self.free)
            x = max((v for v in range(n) if self.A[v] is None),
                    key=lambda v: self.P[v][0] + self.P[v][1])
            self.assign(x, self.rng.randrange(2))


def H(q):
    return -(q * math.log2(q) + (1 - q) * math.log2(1 - q))


def report(name, adj, beta, walks, rng):
    lam = 2 ** H(beta)
    eps = table(lam, max(len(a) for a in adj) + 2, math.inf)
    Ss, mom = [], []
    for _ in range(walks):
        S, _ = Walk(adj, lam, beta, eps, rng).run()
        Ss.append(S)
        mom.append((2 / lam) ** S)
    Ss.sort()
    with_plain = sum(1 for s in Ss if s) / walks
    print(f"  {name:44s} beta'={beta:.3f}: walks with a plain step {with_plain:.2f},"
          f" S max {Ss[-1]:3d}, log2 E[(2/lam)^S] = {math.log2(sum(mom) / walks):.2f}", flush=True)


def main():
    from explore_dpll_measures import aligned_circulant
    rng = random.Random(1)
    print("random gap formulas, beta0 = 0.25")
    for n, d in ((200, 20), (400, 40), (400, 200)):
        report(f"biased signs n={n} d={d}", biased(n, d / (n - 1), 0.75, rng), 0.26, 100, rng)
        report(f"aligned n={n} d={d}", aligned(n, d / (n - 1), 0.25, rng), 0.26, 100, rng)
    print("C_{n,c}, all variables identical")
    for n in (101, 201, 401):
        adj = aligned_circulant(n, 0.5).adj
        p = min(sum(1 for (v, sx, sv) in adj[0] if sx == -1), sum(1 for (v, sx, sv) in adj[0] if sx == 1))
        for slack in (0.02, 0.05):
            report(f"C_n,c n={n} (beta0={p / (n - 1):.3f})", adj, p / (n - 1) + slack, 150, rng)


if __name__ == "__main__":
    main()
