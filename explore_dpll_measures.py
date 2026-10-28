#!/usr/bin/env python3
"""Exploration of DPLL + domination on canonical Max 2-SAT formulas.

A literal is (var, sgn), sgn in {+1,-1}.  A canonical formula has at most one
binary clause per pair, or a complementary pair {(x|y),(~x|~y)} (B = 2).
State per variable v: P[v] = [deficit of literal v, deficit of literal ~v],
  p_l = d2(~l) - d1(l) + d1(~l),   so P[v][0] + P[v][1] = binary degree of v.
Assigning x: for each clause (l_x | l_v) with v free, if l_x is false the
deficit of l_v drops by one, otherwise the deficit of ~l_v drops by one.
Domination: p_l <= 0  ->  set l true.

Experiments
  E1  level budget  T <= 1 + sum_k N_k  for static orders (random instances)
  E2  aligned circulant family (all gaps equal): every branching rule gives the
      same tree, equal to the lattice count and to the level budget; large-n
      exponents vs H((1-eps)/2) and vs the two-level partition bounds
  E4  local validity of an additive 'entropy' measure  mu = sum_v W(p_v, q_v)
      (E3, max-degree vs gap-last, was dropped: the effect is asymptotic)
Runtime: about 3 minutes.
"""
import math
import random
import sys
from functools import lru_cache

sys.setrecursionlimit(10000)


def idx(s):
    return 0 if s == 1 else 1


class Formula:
    def __init__(self, n, clauses):
        self.n = n
        self.clauses = clauses
        self.adj = [[] for _ in range(n)]          # (other var, my sign, other sign)
        for (a, sa), (b, sb) in clauses:
            self.adj[a].append((b, sa, sb))
            self.adj[b].append((a, sb, sa))

    def initial_state(self):
        P = [[0, 0] for _ in range(self.n)]
        for (a, sa), (b, sb) in self.clauses:
            # literal (a,sa) occurs in a binary clause: deficit of ~(a,sa) += 1
            P[a][idx(-sa)] += 1
            P[b][idx(-sb)] += 1
        return P

    def gap(self, v):
        P = self.initial_state()
        return P[v][1] - P[v][0]          # d2(v) - d2(~v)


def assign(F, P, A, x, val):
    """Assign x := val (0/1) and update deficits of free neighbours."""
    A[x] = val
    for (v, sx, sv) in F.adj[x]:
        if A[v] is not None:
            continue
        lit_x_true = (val == 1) if sx == 1 else (val == 0)
        if not lit_x_true:
            P[v][idx(sv)] -= 1          # becomes unit (l_v)
        else:
            P[v][idx(-sv)] -= 1         # clause removed


def close(F, P, A):
    """Exhaustive domination; returns number of fixings."""
    changed, k = True, 0
    while changed:
        changed = False
        for v in range(F.n):
            if A[v] is None and (P[v][0] <= 0 or P[v][1] <= 0):
                assign(F, P, A, v, 1 if P[v][0] <= 0 else 0)
                changed, k = True, k + 1
    return k


def count_leaves(F, choose, P=None, A=None, hook=None):
    if P is None:
        P, A = F.initial_state(), [None] * F.n
    P = [r[:] for r in P]
    A = A[:]
    close(F, P, A)
    free = [v for v in range(F.n) if A[v] is None]
    if not free:
        return 1
    x = choose(F, P, A, free)
    kids = []
    for val in (0, 1):
        P2, A2 = [r[:] for r in P], A[:]
        assign(F, P2, A2, x, val)
        kids.append((P2, A2))
    if hook is not None:
        hook(F, P, A, x, kids)
    return sum(count_leaves(F, choose, P2, A2, hook) for (P2, A2) in kids)


# ---------------------------------------------------------------- rules
def static_rule(order):
    pos = {v: i for i, v in enumerate(order)}
    return lambda F, P, A, free: min(free, key=lambda v: pos[v])


def maxdeg_rule(F, P, A, free):
    return max(free, key=lambda v: (P[v][0] + P[v][1], -v))


# ---------------------------------------------------------------- level budget
def level_budget(F, order):
    """1 + sum_k N_k, N_k = #assignments of predecessors leaving x_k undominated."""
    P0 = F.initial_state()
    total = 1
    for k, x in enumerate(order):
        pred = set(order[:k])
        # decrements of x's two deficits for each predecessor value
        dec = {}
        for (u, sx, su) in F.adj[x]:
            if u not in pred:
                continue
            d = dec.setdefault(u, [[0, 0], [0, 0]])
            for val in (0, 1):
                lit_u_true = (val == 1) if su == 1 else (val == 0)
                if not lit_u_true:
                    d[val][idx(sx)] += 1
                else:
                    d[val][idx(-sx)] += 1
        dist = {(0, 0): 1}
        for u, d in dec.items():
            nd = {}
            for (a, b), c in dist.items():
                for val in (0, 1):
                    key = (a + d[val][0], b + d[val][1])
                    nd[key] = nd.get(key, 0) + c
            dist = nd
        bad = sum(c for (a, b), c in dist.items()
                  if P0[x][0] - a > 0 and P0[x][1] - b > 0)
        total += bad * 2 ** (k - len(dec))
    return total


# ---------------------------------------------------------------- instances
def random_canonical(n, p_edge=0.7, p_comp=0.0, rng=random):
    cl = []
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p_edge:
                si, sj = rng.choice((1, -1)), rng.choice((1, -1))
                cl.append(((i, si), (j, sj)))
                if rng.random() < p_comp:
                    cl.append(((i, -si), (j, -sj)))
    return Formula(n, cl)


def aligned_complete(n, eps, rng=random):
    """Every pair gets (x|y) w.p. (1+eps)/2, else (~x|~y)."""
    cl = []
    for i in range(n):
        for j in range(i + 1, n):
            s = 1 if rng.random() < (1 + eps) / 2 else -1
            cl.append(((i, s), (j, s)))
    return Formula(n, cl)


def aligned_circulant(n, eps):
    """n odd. (x_i|x_j) iff circular distance <= c, else (~x_i|~x_j).
    Every variable has gap 4c-(n-1), i.e. all gaps equal."""
    c = round((1 + eps) * (n - 1) / 4)
    cl = []
    for i in range(n):
        for j in range(i + 1, n):
            d = min(j - i, n - (j - i))
            s = 1 if d <= c else -1
            cl.append(((i, s), (j, s)))
    return Formula(n, cl)


def lattice_tree(a, b):
    """Leaves of the symmetric aligned tree: 1 + #{(z,o): z<a, o<b} paths."""
    return 1 + sum(math.comb(z + o, z) for z in range(a) for o in range(b))


def H(x):
    return 0.0 if x <= 0 or x >= 1 else -x * math.log2(x) - (1 - x) * math.log2(1 - x)


# ---------------------------------------------------------------- E4 measure
@lru_cache(maxsize=None)
def Wlat(p, q):
    """Additive 'lattice entropy' weight: log2 C(p+q, p) / (p+q+1)."""
    if p <= 0 or q <= 0:
        return 0.0
    return math.log2(math.comb(p + q, p)) / (p + q + 1)


def mu_entropy(F, P, A):
    return sum(Wlat(P[v][0], P[v][1]) for v in range(F.n) if A[v] is None)


def mu_after_close(F, P, A):
    P, A = [r[:] for r in P], A[:]
    close(F, P, A)
    return mu_entropy(F, P, A)


def main():
    rng = random.Random(2026)

    print("E1  level budget vs actual tree size (static orders)")
    worst = 0.0
    trials = 0
    for n in (8, 10, 12):
        for pc in (0.0, 0.3):
            for _ in range(40):
                F = random_canonical(n, p_edge=rng.uniform(0.3, 1.0), p_comp=pc, rng=rng)
                order = list(range(n))
                rng.shuffle(order)
                T = count_leaves(F, static_rule(order))
                B = level_budget(F, order)
                assert T <= B, (n, T, B)
                worst = max(worst, T / B)
                trials += 1
    print(f"    {trials} instances, T <= budget always; max T/budget = {worst:.3f}")

    print("\nE2  aligned circulant family (all gaps equal): exact tree sizes")
    print("    n   gap/n  lattice-LB  T(natural)  T(maxdeg)  T(random)   budget")
    for n, eps in ((13, 0.5), (15, 0.4), (17, 0.5), (19, 0.4)):
        F = aligned_circulant(n, eps)
        P0 = F.initial_state()
        a, b = P0[0][0], P0[0][1]
        lb = math.comb(a + b - 2, a - 1)
        Tn = count_leaves(F, static_rule(list(range(n))))
        Tm = count_leaves(F, maxdeg_rule)
        order = list(range(n)); rng.shuffle(order)
        Tr = count_leaves(F, static_rule(order))
        Bn = level_budget(F, list(range(n)))
        assert lb <= Tn == Tm == Tr == lattice_tree(a, b) == Bn
        print(f"   {n:3d}  {F.gap(0)/(n-1):5.3f}  {lb:10d}  {Tn:10d}  {Tm:9d}  {Tr:9d}  {Bn:7d}")

    print("\n    large n (exact lattice formula; any branching rule gives this tree):")
    print("    eps    n    log2(T)/n   H((1-eps)/2)   user bound 1-eps^2/4   optimized partition")
    for eps in (0.2, 0.4, 0.6):
        for n in (201, 801, 3201):
            D = n - 1
            gap = round(eps * D)
            a, b = (D - gap) // 2, (D + gap) // 2
            T = lattice_tree(a, b)
            # optimized two-level partition: alpha = (eps-alpha)^2/(2 ln 2)
            lo, hi = 0.0, eps
            for _ in range(100):
                mid = (lo + hi) / 2
                if mid < (eps - mid) ** 2 / (2 * math.log(2)): lo = mid
                else: hi = mid
            print(f"    {eps:.1f}  {n:5d}   {math.log2(T)/n:8.4f}     {H((1-eps)/2):8.4f}"
                  f"        {1-eps**2/4:8.4f}             {1-lo:8.4f}")

    print("\nE4  additive entropy measure: local inequality 2^mu0 + 2^mu1 <= 2^mu")
    for name, gen in (("aligned circulant", lambda n: aligned_circulant(n + 1, 0.4)),
                      ("aligned random  ", lambda n: aligned_complete(n, 0.4, rng)),
                      ("random signs    ", lambda n: random_canonical(n, 0.8, 0.0, rng))):
        for rule_name, rule in (("max-degree", maxdeg_rule),):
            nodes = viol = 0
            worst = 0.0

            def hook(F, P, A, x, kids):
                nonlocal nodes, viol, worst
                m = mu_entropy(F, P, A)
                s = sum(2 ** mu_after_close(F, P2, A2) for (P2, A2) in kids)
                r = s / 2 ** m
                nodes += 1
                if r > 1 + 1e-12:
                    viol += 1
                worst = max(worst, r)

            for _ in range(6):
                F = gen(12)
                count_leaves(F, rule, hook=hook)
            print(f"    {name} / {rule_name}: {nodes} branchings, {viol} violations, "
                  f"worst ratio {worst:.3f}")


if __name__ == "__main__":
    main()
