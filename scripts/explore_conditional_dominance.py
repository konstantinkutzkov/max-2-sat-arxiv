#!/usr/bin/env python3
"""Two-sided comparison branching with certified joint-constraint cuts.

Floating-point LPs propose nonnegative multiplier vectors. Every cut is
verified with exact Fraction arithmetic; an unverified proposal is ignored.
This preserves the established two-sided comparison search and its tie rule.
Run with python3 explore_conditional_dominance.py (requires scipy).
"""
import itertools
import json
import math
import random
import time
from fractions import Fraction
from pathlib import Path

from scipy.optimize import linprog
from explore_dpll_measures import Formula, idx
from explore_extended_rule import (Search, biased, brute_opt, initial,
                                   lit_true, maxdeg_rule, score)
from explore_imbalance import two_sided


def residual_rows(a, cons):
    free = [v for v, val in enumerate(a) if val is None]
    rows = []
    for fav, threshold, used in cons:
        k = threshold - used - 1
        c0 = [fav[v][1] if v in fav and fav[v][0] == 0 else 0 for v in free]
        c1 = [fav[v][1] if v in fav and fav[v][0] == 1 else 0 for v in free]
        if k < sum(max(x, y) for x, y in zip(c0, c1)):
            rows.append((c0, c1, k))
    return free, rows


def exact_margin(rows, weights):
    if not rows:
        return Fraction(0)
    n = len(rows[0][0])
    return (sum(min(sum(w * row[0][j] for row, w in zip(rows, weights)),
                    sum(w * row[1][j] for row, w in zip(rows, weights)))
                for j in range(n))
            - sum(w * row[2] for row, w in zip(rows, weights)))


def infeasibility_witness(rows):
    """Return a verified nonnegative linear-combination contradiction."""
    if not rows:
        return None, False
    m, n = len(rows), len(rows[0][0])
    # Common opposite-threshold contradictions need no LP.
    simple = [[Fraction(1)] * m]
    simple += [[Fraction(i in pair) for i in range(m)]
               for pair in itertools.combinations(range(m), 2)]
    for weights in simple:
        if exact_margin(rows, weights) > 0:
            return weights, False
    if m == 1:
        return None, False
    # Maximize sum_j t_j - sum_i w_i k_i with t_j <= sum_i w_i c_ij^b.
    objective = [row[2] for row in rows] + [-1] * n
    inequalities = []
    for j in range(n):
        for b in (0, 1):
            inequalities.append([-row[b][j] for row in rows]
                                + [int(k == j) for k in range(n)])
    result = linprog(objective, A_ub=inequalities or None,
                     b_ub=[0] * len(inequalities) if inequalities else None,
                     A_eq=[[1] * m + [0] * n], b_eq=[1],
                     bounds=[(0, None)] * m + [(None, None)] * n,
                     method='highs')
    if not result.success or result.fun >= -1e-9:
        return None, True
    weights = [max(Fraction(0), Fraction(float(x)).limit_denominator(1000000))
               for x in result.x[:m]]
    return (weights if exact_margin(rows, weights) > 0 else None), True


def make_child(search, p, a, cons, x, val):
    lsign = 1 if p[x][0] <= p[x][1] else -1
    budget, degree = p[x][idx(lsign)], sum(p[x])
    fav = {}
    for v, sx, sv in search.F.adj[x]:
        if a[v] is None:
            good = int(sv == -1) if sx == lsign else int(sv == 1)
            old, weight = fav.get(v, (good, 0))
            assert old == good
            fav[v] = good, weight + 1
    pp, aa = [row[:] for row in p], a[:]
    cc = [[c[0], c[1], c[2]] for c in cons]
    if lit_true(val, lsign):
        cc.append([{v: (1 - good, w) for v, (good, w) in fav.items()},
                   degree - budget + 1, 0])
    else:
        cc.append([fav, budget, 0])
    if not search.assign(pp, aa, cc, x, val):
        return None
    return pp, aa, cc


class JointComparisonSearch(Search):
    def __init__(self, f, units, rule=maxdeg_rule):
        super().__init__(f, units, True, True, rule)
        self.nodes = self.joint_cuts = self.lp_calls = self.implication_fixings = 0
        self.witness_checks = 0

    def run(self, p, a, cons):
        self.nodes += 1
        p, a, cons = [row[:] for row in p], a[:], [[c[0], c[1], c[2]] for c in cons]
        if not self.closure(p, a, cons):
            self.leaves += 1
            return
        free = [v for v, b in enumerate(a) if b is None]
        if not free:
            self.leaves += 1
            self.best = max(self.best, score(self.F, self.units, a))
            return
        x = self.rule(self.F, p, a, free)
        children = []
        joint_removed = 0
        for val in (0, 1):
            child = make_child(self, p, a, cons, x, val)
            if child is None:
                self.leaves += 1  # Count rejected children just as the baseline does.
                continue
            pp, aa, cc = child
            if not self.closure(pp, aa, cc):
                self.leaves += 1
                continue
            _, rows = residual_rows(aa, cc)
            witness, used_lp = infeasibility_witness(rows)
            self.lp_calls += used_lp
            if witness is not None:
                assert all(w >= 0 for w in witness) and exact_margin(rows, witness) > 0
                self.witness_checks += 1
                self.joint_cuts += 1
                joint_removed += 1
                self.leaves += 1
            else:
                children.append(child)
        if len(children) == 1 and joint_removed:
            self.implication_fixings += 1
        for child in children:
            self.run(*child)


def run_joint(f, units, rule=maxdeg_rule):
    start = time.perf_counter()
    search = JointComparisonSearch(f, units, rule)
    search.run(initial(f, units), [None] * f.n, [])
    return search, time.perf_counter() - start


def exact_witness_checks(seed=7102030, trials=150):
    rng = random.Random(seed)
    cuts = 0
    for _ in range(trials):
        n, m = rng.randint(2, 8), rng.randint(2, 9)
        rows = []
        for __ in range(m):
            signs = [rng.choice((-2, -1, 0, 1, 2)) for v in range(n)]
            c0 = [max(0, -z) for z in signs]
            c1 = [max(0, z) for z in signs]
            rows.append((c0, c1, rng.randint(0, sum(abs(z) for z in signs))))
        witness, _ = infeasibility_witness(rows)
        if witness is not None:
            feasible = sum(all(sum(row[b][j] for j, b in enumerate(bits)) <= row[2]
                               for row in rows)
                           for bits in itertools.product((0, 1), repeat=n))
            assert feasible == 0
            cuts += 1
    return dict(systems=trials, verified_infeasibility_witnesses=cuts)


def random_comparisons(seed=7102031):
    rng = random.Random(seed)
    rows = []
    for n, trials in ((10, 10), (12, 10), (14, 6)):
        for trial in range(trials):
            f = biased(n, rng.uniform(.65, 1), .5, rng.choice((0, .15)), rng)
            units = {}
            for _ in range(rng.randrange(n // 2 + 1)):
                key = rng.randrange(n), rng.choice((-1, 1))
                units[key] = units.get(key, 0) + 1
            t0 = time.perf_counter()
            old = two_sided(f, units, True)
            baseline_seconds = time.perf_counter() - t0
            new, seconds = run_joint(f, units)
            exact = brute_opt(f, units)
            assert old[0] == new.best == exact
            rows.append(dict(n=n, trial=trial, optimum=exact, old_leaves=old[1],
                             new_leaves=new.leaves, new_nodes=new.nodes,
                             joint_cuts=new.joint_cuts, implication_fixings=new.implication_fixings,
                             lp_calls=new.lp_calls, baseline_seconds=baseline_seconds,
                             new_seconds=seconds))
    return rows


def twins(t, d, seed):
    assert d % 2 == 0
    rng = random.Random(seed)
    clauses = []
    for x in range(t):
        for j in range(d):
            sign = 1 if j < d // 2 else -1
            clauses.append(((x, sign), (t + j, sign)))
    for i, j in itertools.combinations(range(d), 2):
        clauses.append(((t + i, rng.choice((-1, 1))), (t + j, rng.choice((-1, 1)))))
    f = Formula(t + d, clauses)
    # Neutralize strong unary fields on neighbors, leaving center gaps zero.
    units = {}
    for v in range(t, t + d):
        gap = f.gap(v)
        if abs(gap) >= 2:
            units[v, -1 if gap > 0 else 1] = abs(gap) // 2
    return f, units


def twin_comparisons():
    rows = []
    rule = lambda f, p, a, free: min(free)
    for t, d in ((4, 8), (6, 10), (8, 10)):
        f, units = twins(t, d, 111 + t)
        assert all(initial(f, units)[v] == [d // 2, d // 2] for v in range(t))
        old = two_sided(f, units, True, rule)
        new, seconds = run_joint(f, units, rule)
        assert old[0] == new.best
        if f.n <= 16:
            assert new.best == brute_opt(f, units)
        rows.append(dict(n=f.n, centers=t, center_degree=d, old_leaves=old[1],
                         new_leaves=new.leaves, new_nodes=new.nodes,
                         joint_cuts=new.joint_cuts, implication_fixings=new.implication_fixings,
                         lp_calls=new.lp_calls, new_seconds=seconds))
    return rows


def stability_example():
    # Max-Cut of K_n encoded by two 2-clauses per edge. Every balanced cut
    # is a strict one-variable local optimum.
    n = 12
    clauses = [clause for i, j in itertools.combinations(range(n), 2)
               for clause in ((((i, 1), (j, 1))), (((i, -1), (j, -1))))]
    f = Formula(n, clauses)
    survivors = []
    for bits in itertools.product((0, 1), repeat=n):
        s = score(f, {}, bits)
        if all(score(f, {}, bits[:i] + (1 - bits[i],) + bits[i + 1:]) < s
               for i in range(n)):
            survivors.append(bits)
    assert len(survivors) == math.comb(n, n // 2)
    assert all(sum(bits) == n // 2 for bits in survivors)
    return dict(n=n, strict_local_optima=len(survivors),
                surviving_fraction=len(survivors) / 2 ** n,
                information_bits=n - math.log2(len(survivors)))


def complete_cut_search():
    n = 10
    clauses = [cl for i, j in itertools.combinations(range(n), 2)
               for cl in ((((i, 1), (j, 1))), (((i, -1), (j, -1))))]
    f = Formula(n, clauses)
    old = two_sided(f, {}, True)
    new, seconds = run_joint(f, {})
    assert old[0] == new.best
    return dict(n=n, baseline_leaves=old[1], joint_leaves=new.leaves,
                joint_cuts=new.joint_cuts, lp_calls=new.lp_calls,
                joint_seconds=seconds)


def main():
    result = dict(witness_checks=exact_witness_checks(),
                  random_comparisons=random_comparisons(),
                  twins=twin_comparisons(), stability=stability_example(),
                  complete_cut_search=complete_cut_search())
    Path(__file__).with_name('conditional_dominance_checks.json').write_text(
        json.dumps(result, indent=2) + '\n')
    compact = dict(result)
    rr = result['random_comparisons']
    compact['random_comparisons'] = dict(
        formulas=len(rr), old_leaves=sum(r['old_leaves'] for r in rr),
        new_leaves=sum(r['new_leaves'] for r in rr),
        implication_fixings=sum(r['implication_fixings'] for r in rr),
        joint_cuts=sum(r['joint_cuts'] for r in rr),
        lp_calls=sum(r['lp_calls'] for r in rr),
        baseline_seconds=sum(r['baseline_seconds'] for r in rr),
        new_seconds=sum(r['new_seconds'] for r in rr))
    print(json.dumps(compact, indent=2))


if __name__ == '__main__':
    main()
