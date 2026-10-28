#!/usr/bin/env python3
"""Exact checks of neighborhood imbalance and two-sided flip constraints.

The preferred child keeps L >= p (ties permitted); the other keeps L <= p-1.
This differs from imposing strict flip conditions in both children.
Run with: python3 explore_imbalance.py
"""
import itertools
import json
import random
from collections import Counter
from pathlib import Path

from explore_dpll_measures import Formula, assign, idx, aligned_circulant
from explore_extended_rule import (Search, biased, brute_opt, initial,
                                   lit_true, maxdeg_rule, score, solve)


class TwoSidedSearch(Search):
    def run(self, P, A, cons):
        P, A = [r[:] for r in P], A[:]
        cons = [[c[0], c[1], c[2]] for c in cons]
        if not self.closure(P, A, cons):
            self.leaves += 1
            return
        free = [v for v in range(self.F.n) if A[v] is None]
        if not free:
            self.leaves += 1
            self.best = max(self.best, score(self.F, self.units, A))
            return
        x = self.rule(self.F, P, A, free)
        lsign = 1 if P[x][0] <= P[x][1] else -1
        p, D = P[x][idx(lsign)], sum(P[x])
        fav = {}
        for v, sx, sv in self.F.adj[x]:
            if A[v] is None:
                good = int(sv == -1) if sx == lsign else int(sv == 1)
                old, weight = fav.get(v, (good, 0))
                assert old == good
                fav[v] = good, weight + 1
        assert sum(w for _, w in fav.values()) == D
        for val in (0, 1):
            pp, aa = [r[:] for r in P], A[:]
            cc = [[c[0], c[1], c[2]] for c in cons]
            if lit_true(val, lsign):
                # D-L <= D-p, represented as strict threshold D-p+1.
                cf = {v: (1 - good, w) for v, (good, w) in fav.items()}
                threshold = D - p + 1
            else:
                cf, threshold = fav, p
            cc.append([cf, threshold, 0])
            if not self.assign(pp, aa, cc, x, val):
                self.leaves += 1
            else:
                self.run(pp, aa, cc)


def two_sided(F, units, propagation, rule=maxdeg_rule):
    s = TwoSidedSearch(F, units, True, propagation, rule)
    s.run(initial(F, units), [None] * F.n, [])
    return s.best, s.leaves


def imbalance_check():
    # Balanced center: d positive and d negative binary occurrences.
    d, k = 6, 4
    clauses = [((0, 1 if j <= d else -1), (j, 1))
               for j in range(1, 2 * d + 1)]
    f = Formula(2 * d + 1, clauses)
    gaps = Counter()
    for bits in itertools.product((0, 1), repeat=k):
        p, a = f.initial_state(), [None] * f.n
        for v, val in enumerate(bits, 1):
            assign(f, p, a, v, val)
        t = bits.count(0)  # Number of new positive units at the center.
        gap = p[0][1] - p[0][0]
        assert gap == 2 * t - k
        assert sum(p[0]) == 2 * d - k
        gaps[gap] += 1
    return dict(positive_degree=d, negative_degree=d, k=k,
                raw_binary_gap=-k, effective_gap_histogram=dict(sorted(gaps.items())))


def main():
    rng = random.Random(7102027)
    trials = 0
    for n in (6, 8, 10, 12):
        for _ in range(30):
            f = biased(n, rng.uniform(.35, 1), rng.uniform(.5, .8),
                       rng.choice((0, .3)), rng)
            units = {}
            for _ in range(rng.randrange(n + 1)):
                key = rng.randrange(n), rng.choice((-1, 1))
                units[key] = units.get(key, 0) + rng.randint(1, 3)
            opt = brute_opt(f, units)
            order = list(range(n))
            rng.shuffle(order)
            ranks = {v: i for i, v in enumerate(order)}
            static = lambda F, P, A, free: min(free, key=ranks.get)
            for rule in (maxdeg_rule, static):
                for prop in (False, True):
                    assert two_sided(f, units, prop, rule)[0] == opt
            trials += 1
    comparisons = []
    for n in (12, 16, 20):
        totals = [0, 0]
        for _ in range(8):
            f = biased(n, .8, .5, 0, rng)
            one = solve(f, {}, True, True)
            two = two_sided(f, {}, True)
            assert one[0] == two[0]
            if n <= 16:
                assert two[0] == brute_opt(f, {})
            totals[0] += one[1]
            totals[1] += two[1]
        comparisons.append(dict(n=n, formulas=8, one_sided_leaves=totals[0],
                                two_sided_leaves=totals[1]))
    circulants = []
    for n, eps in ((13, .5), (17, .5), (21, .2)):
        f = aligned_circulant(n, eps)
        one, two = solve(f, {}, True, True), two_sided(f, {}, True)
        assert one[0] == two[0]
        circulants.append(dict(n=n, eps=eps, one_sided_leaves=one[1],
                               two_sided_leaves=two[1]))
    result = dict(imbalance=imbalance_check(), exact_soundness_formulas=trials,
                  variants_per_formula=4, random_comparisons=comparisons,
                  circulant_comparisons=circulants)
    Path(__file__).with_name('imbalance_checks.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
