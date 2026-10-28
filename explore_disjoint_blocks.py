#!/usr/bin/env python3
"""Exact leaf count for pruning clauses with disjoint supports.

Centres x_1..x_m at pairwise distance >= 3 in the constraint graph (disjoint
closed neighbourhoods), order x_1, N(x_1), ..., x_m, N(x_m), rest.  Pruning
clauses only at the centres, cuts and propagation, no domination.  Predicted:
    leaves = 2^n * prod_i (1 + theta_i) / 2,
    theta_i = 2^{-D_i} * sum_{j < p_i} C(D_i, j),
where p_i is the smaller deficit of x_i.  Instances in which some centre is
already dominated (p_i = 0) are skipped: the proposition assumes p_i >= 1.
"""
import math
import random

from explore_dpll_measures import Formula, idx
from explore_extended_rule import Search, initial, lit_true


class CentresOnly(Search):
    """Propagation and cuts, no domination; clauses only at the centres."""

    def __init__(self, F, rule, centres):
        super().__init__(F, {}, True, True, rule)
        self.centres = set(centres)

    def closure(self, P, A, cons):
        changed = True
        while changed:
            changed = False
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
            self.leaves += 1
            return
        free = [v for v in range(self.F.n) if A[v] is None]
        if not free:
            self.leaves += 1
            return
        x = self.rule(self.F, P, A, free)
        lsign = 1 if P[x][0] <= P[x][1] else -1
        for val in (0, 1):
            P2, A2 = [r[:] for r in P], A[:]
            cons2 = [[c[0], c[1], c[2]] for c in cons]
            if x in self.centres and not lit_true(val, lsign):
                fav = {}
                for (v, sx, sv) in self.F.adj[x]:
                    if A[v] is None:
                        good = (0 if sv == 1 else 1) if sx == lsign else (1 if sv == 1 else 0)
                        g, w = fav.get(v, (good, 0))
                        fav[v] = (good, w + 1)
                cons2.append([fav, P[x][idx(lsign)], 0])
            if not self.assign(P2, A2, cons2, x, val):
                self.leaves += 1
                continue
            self.run(P2, A2, cons2)


def instance(rng, m, D, extra_p, rest):
    """m stars of size D (centres 0, D+1, ...), random extra edges between
    non-centres (inside and across blocks and to the rest)."""
    n = m * (D + 1) + rest
    cl, order, centres = [], [], []
    for i in range(m):
        c = i * (D + 1)
        centres.append(c)
        order.append(c)
        for j in range(1, D + 1):
            order.append(c + j)
            cl.append(((c, rng.choice((1, -1))), (c + j, rng.choice((1, -1)))))
    order += list(range(m * (D + 1), n))
    cs = set(centres)
    for a in range(n):
        for b in range(a + 1, n):
            if a not in cs and b not in cs and rng.random() < extra_p:
                cl.append(((a, rng.choice((1, -1))), (b, rng.choice((1, -1)))))
    return Formula(n, cl), order, centres


def main():
    rng = random.Random(5)
    checked = 0
    while checked < 12:
        m, D = rng.choice(((3, 4), (4, 3), (2, 6), (5, 2), (3, 3)))
        F, order, centres = instance(rng, m, D, rng.uniform(0.2, 0.6), rng.randint(0, 3))
        P0 = initial(F, {})
        if any(min(P0[c]) == 0 for c in centres):
            continue                                  # a centre is dominated
        pred = 2 ** F.n
        for c in centres:
            p, Dc = min(P0[c]), P0[c][0] + P0[c][1]
            pred *= (1 + sum(math.comb(Dc, j) for j in range(p)) / 2 ** Dc) / 2
        pos = {v: i for i, v in enumerate(order)}
        S = CentresOnly(F, lambda F_, P, A, free: min(free, key=lambda v: pos[v]), centres)
        S.run(initial(F, {}), [None] * F.n, [])
        assert abs(S.leaves - pred) < 1e-6, (S.leaves, pred)
        print(f"m={m} D={D} n={F.n}: predicted = observed = {S.leaves}   (2^n = {2 ** F.n})")
        checked += 1


if __name__ == "__main__":
    main()
