#!/usr/bin/env python3
"""The 'pruned branch' extension of the domination rule.

When branching on x, let l be the literal of x with the smaller deficit p_l.
For every neighbour y, one value of y lowers p_l (by c_xy).  In the branch
where l is FALSE we keep only assignments whose total lowering stays below
p_l, i.e. under which l would not become dominated; the branch where l is
TRUE is explored in full.  The constraint is checked whenever a constrained
variable gets assigned (by branching, by domination, or by propagation).

Checks
  S  soundness: optimum found = brute-force optimum, with nested constraints,
     domination, random units and complementary pairs
  T  tree sizes with and without the rule (circulant family, random families)
"""
import itertools
import random
import sys

from explore_dpll_measures import Formula, idx, aligned_circulant, random_canonical

sys.setrecursionlimit(10000)


def lit_true(val, s):
    return val == (1 if s == 1 else 0)


def score(F, units, A):
    s = sum(1 for (a, sa), (b, sb) in F.clauses if lit_true(A[a], sa) or lit_true(A[b], sb))
    return s + sum(m for (v, sv), m in units.items() if lit_true(A[v], sv))


def brute_opt(F, units):
    best = -1
    for bits in itertools.product((0, 1), repeat=F.n):
        best = max(best, score(F, units, list(bits)))
    return best


class Search:
    def __init__(self, F, units, use_rule, propagate, rule):
        self.F, self.units = F, units
        self.use_rule, self.propagate, self.rule = use_rule, propagate, rule
        self.leaves = 0
        self.best = -1

    # -- state = (P, A, cons); cons = list of [fav: {var: (value, weight)}, thr, count]
    def assign(self, P, A, cons, x, val):
        A[x] = val
        for (v, sx, sv) in self.F.adj[x]:
            if A[v] is None:
                if not lit_true(val, sx):
                    P[v][idx(sv)] -= 1
                else:
                    P[v][idx(-sv)] -= 1
        ok = True
        for c in cons:
            fv = c[0].get(x)
            if fv is not None and val == fv[0]:
                c[2] += fv[1]
                if c[2] >= c[1]:
                    ok = False
        return ok

    def closure(self, P, A, cons):
        n = self.F.n
        changed = True
        while changed:
            changed = False
            for v in range(n):
                if A[v] is None and (P[v][0] <= 0 or P[v][1] <= 0):
                    if not self.assign(P, A, cons, v, 1 if P[v][0] <= 0 else 0):
                        return False
                    changed = True
            if self.propagate:
                for c in cons:
                    slack = c[1] - c[2]
                    for y, (fv, w) in list(c[0].items()):
                        if A[y] is None and w >= slack:
                            if not self.assign(P, A, cons, y, 1 - fv):
                                return False
                            changed = True
        return True

    def run(self, P, A, cons):
        P = [r[:] for r in P]
        A = A[:]
        cons = [[c[0], c[1], c[2]] for c in cons]
        if not self.closure(P, A, cons):
            self.leaves += 1                     # pruned node
            return
        free = [v for v in range(self.F.n) if A[v] is None]
        if not free:
            self.leaves += 1
            self.best = max(self.best, score(self.F, self.units, A))
            return
        x = self.rule(self.F, P, A, free)
        lsign = 1 if P[x][0] <= P[x][1] else -1   # literal closer to domination
        for val in (0, 1):
            P2, A2 = [r[:] for r in P], A[:]
            cons2 = [[c[0], c[1], c[2]] for c in cons]
            l_false = not lit_true(val, lsign)
            if self.use_rule and l_false:
                fav = {}
                for (v, sx, sv) in self.F.adj[x]:
                    if A[v] is not None:
                        continue
                    # value of v that lowers p_l
                    if sx == lsign:      # clause contains l: v's literal false lowers p_l
                        good = 0 if sv == 1 else 1
                    else:                # clause contains ~l: v's literal true lowers p_l
                        good = 1 if sv == 1 else 0
                    g, w = fav.get(v, (good, 0))
                    assert g == good
                    fav[v] = (good, w + 1)
                cons2.append([fav, P[x][idx(lsign)], 0])
            if not self.assign(P2, A2, cons2, x, val):
                self.leaves += 1
                continue
            self.run(P2, A2, cons2)


def initial(F, units):
    P = F.initial_state()
    for (v, s), m in units.items():
        P[v][idx(s)] -= m
        P[v][idx(-s)] += m
    return P


def maxdeg_rule(F, P, A, free):
    return max(free, key=lambda v: (P[v][0] + P[v][1], -v))


def solve(F, units, use_rule, propagate=False, rule=maxdeg_rule):
    S = Search(F, units, use_rule, propagate, rule)
    S.run(initial(F, units), [None] * F.n, [])
    return S.best, S.leaves


def biased(n, p_edge, p_pos, p_comp, rng):
    cl = []
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p_edge:
                si = 1 if rng.random() < p_pos else -1
                sj = 1 if rng.random() < p_pos else -1
                cl.append(((i, si), (j, sj)))
                if rng.random() < p_comp:
                    cl.append(((i, -si), (j, -sj)))
    return Formula(n, cl)


def main():
    rng = random.Random(7)
    print("S  soundness against brute force")
    trials = 0
    for n in (6, 8, 10, 12):
        for _ in range(60):
            F = biased(n, rng.uniform(0.3, 1.0), rng.uniform(0.5, 0.9), rng.choice((0.0, 0.3)), rng)
            units = {}
            for _ in range(rng.randint(0, n)):
                v, s = rng.randrange(n), rng.choice((1, -1))
                units[(v, s)] = units.get((v, s), 0) + rng.randint(1, 3)
            opt = brute_opt(F, units)
            for use_rule, prop in ((False, False), (True, False), (True, True)):
                best, _ = solve(F, units, use_rule, prop)
                assert best == opt, (n, use_rule, prop, best, opt)
            trials += 1
    print(f"   {trials} instances x 3 variants: optimum always equals brute force")

    print("\nT  leaves: plain DPLL / with rule / with rule + propagation")
    for n, eps in ((13, 0.5), (15, 0.4), (17, 0.5), (19, 0.4)):
        F = aligned_circulant(n, eps)
        r = [solve(F, {}, u, p)[1] for (u, p) in ((False, False), (True, False), (True, True))]
        print(f"   circulant n={n:2d} eps={eps}:   {r[0]:6d} / {r[1]:6d} / {r[2]:6d}")
    for name, gen in (("biased signs p+=0.75", lambda n: biased(n, 0.9, 0.75, 0.0, rng)),
                      ("biased signs p+=0.65", lambda n: biased(n, 0.9, 0.65, 0.0, rng)),
                      ("random signs        ", lambda n: biased(n, 0.9, 0.50, 0.0, rng))):
        for n in (14, 16):
            tot = [0, 0, 0]
            for _ in range(5):
                F = gen(n)
                for i, (u, p) in enumerate(((False, False), (True, False), (True, True))):
                    tot[i] += solve(F, {}, u, p)[1]
            print(f"   {name} n={n}: {tot[0]:6d} / {tot[1]:6d} / {tot[2]:6d}   (sum over 5)")


if __name__ == "__main__":
    main()
