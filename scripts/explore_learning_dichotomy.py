#!/usr/bin/env python3
"""Small checks for fractional-packing certificates with core conditioning.

Exact Boolean counts and rational feasibility checks are used; certificate
values use floating-point logarithms with explicit comparison tolerances.
This is a research prototype, not an interval-certified production solver.
Run with python3 explore_learning_dichotomy.py (requires scipy).
"""
import itertools
import json
import math
import random
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from scipy.optimize import linprog
from explore_branching_frontier import choose_bound
from explore_extended_rule import Search, biased, initial, maxdeg_rule


@dataclass(frozen=True)
class Constraint:
    literals: tuple  # (variable, value making its counted literal true)
    budget: int

    def residual(self, assignment):
        used = sum(assignment[v] == b for v, b in self.literals if v in assignment)
        rest = tuple((v, b) for v, b in self.literals if v not in assignment)
        return rest, self.budget - used

    def probability(self, assignment):
        rest, k = self.residual(assignment)
        if k < 0:
            return Fraction(0)
        if k >= len(rest):
            return Fraction(1)
        return Fraction(sum(math.comb(len(rest), j) for j in range(k + 1)),
                        2 ** len(rest))


def disjunction(literals):
    return Constraint(tuple((v, 1 - b) for v, b in literals), len(literals) - 1)


def assignments(variables):
    for bits in itertools.product((0, 1), repeat=len(variables)):
        yield dict(zip(variables, bits))


def exact_count(n, clauses, partial):
    free = [v for v in range(n) if v not in partial]
    return sum(all(c.probability(partial | a) == 1 for c in clauses)
               for a in assignments(free))


def packing_weights(n, clauses, partial):
    probabilities = [c.probability(partial) for c in clauses]
    if 0 in probabilities:
        j = probabilities.index(0)
        return tuple(Fraction(i == j) for i in range(len(clauses)))
    active = [i for i, p in enumerate(probabilities) if p < 1]
    result = [Fraction(0)] * len(clauses)
    if not active:
        return tuple(result)
    free = [v for v in range(n) if v not in partial]
    supports = [{v for v, _ in clauses[i].residual(partial)[0]} for i in active]
    matrix = [[int(v in support) for support in supports] for v in free]
    costs = [math.log2(float(probabilities[i])) for i in active]
    lp = linprog(costs, A_ub=matrix, b_ub=[1] * len(free),
                 bounds=[(0, 1)] * len(active), method='highs')
    assert lp.success, lp.message
    rational = [max(Fraction(0), Fraction(float(x)).limit_denominator(1000000))
                for x in lp.x]
    load = max([Fraction(1)] + [sum(w for w, s in zip(rational, supports) if v in s)
                               for v in free])
    rational = [w / load for w in rational]
    for v in free:
        assert sum(w for w, s in zip(rational, supports) if v in s) <= 1
    for i, w in zip(active, rational):
        result[i] = w
    return tuple(result)


@dataclass
class Certificate:
    core: tuple
    weights: dict


def certificate(n, clauses, partial, core=()):
    core = tuple(sorted(set(core) - partial.keys()))
    rows = {}
    for a in assignments(core):
        rows[tuple(a[v] for v in core)] = packing_weights(n, clauses, partial | a)
    return Certificate(core, rows)


def value(n, clauses, partial, witness):
    total = 0.0
    free_core = tuple(v for v in witness.core if v not in partial)
    for a in assignments(free_core):
        fixed = partial | a
        key = tuple(fixed[v] for v in witness.core)
        weights = witness.weights[key]
        exponent = n - len(fixed)
        for c, w in zip(clauses, weights):
            if not w:
                continue
            p = c.probability(fixed)
            if not p:
                exponent = -math.inf
                break
            exponent += float(w) * math.log2(float(p))
        total += 2 ** exponent
    return total


def check_random(seed=7102028, trials=250):
    rng = random.Random(seed)
    splits = added = strengthening = 0
    max_split_excess = 0.0
    for _ in range(trials):
        n = rng.randint(3, 10)
        clauses = []
        for __ in range(rng.randint(1, 12)):
            vs = rng.sample(range(n), rng.randint(1, n))
            lits = tuple((v, rng.randrange(2)) for v in vs)
            k = len(vs) - 1 if rng.randrange(2) else rng.randrange(len(vs) + 1)
            clauses.append(Constraint(lits, k))
        partial = {v: rng.randrange(2) for v in rng.sample(range(n), rng.randrange(3))}
        free = [v for v in range(n) if v not in partial]
        core = rng.sample(free, min(rng.randrange(4), len(free)))
        w = certificate(n, clauses, partial, core)
        u = value(n, clauses, partial, w)
        exact = exact_count(n, clauses, partial)
        assert exact <= u + 1e-7 and u <= 2 ** len(free) + 1e-7
        for x in free:
            children = [value(n, clauses, partial | {x: b}, w) for b in (0, 1)]
            excess = sum(children) - u
            max_split_excess = max(max_split_excess, excess)
            assert excess <= 1e-7
            splits += 1
        x = rng.choice(free)
        new_clause = Constraint(tuple((v, rng.randrange(2)) for v in free if v != x),
                                rng.randrange(len(free)))
        total = 0
        for b in (0, 1):
            cc = clauses + ([new_clause] if b else [])
            pp = partial | {x: b}
            old = value(n, cc, pp, w)  # zip gives new constraints inherited weight zero
            fresh = certificate(n, cc, pp, core)
            improved = min(old, value(n, cc, pp, fresh))
            assert exact_count(n, cc, pp) <= improved + 1e-7
            total += improved
        assert total <= u + 1e-7
        added += 1
        extra = next((v for v in free if v not in core), None)
        if extra is not None:
            stronger = certificate(n, clauses, partial, core + [extra])
            assert value(n, clauses, partial, stronger) <= u + 1e-7
            strengthening += 1
    return dict(seed=seed, systems=trials, inherited_splits=splits,
                new_constraint_splits=added, core_extensions=strengthening,
                max_numerical_split_excess=max_split_excess)


def examples():
    q, t = 4, 12
    core = tuple(range(q))
    # All nonzero core patterns are forbidden. In the sole surviving pattern,
    # each long target clause becomes a unit.
    clauses = [disjunction(tuple((j, 1 - a[j]) for j in core))
               for a in assignments(core) if any(a.values())]
    clauses += [disjunction(((q + i, 1),) + tuple((j, 1) for j in core))
                for i in range(t)]
    n = q + t
    records = []
    for h in range(q + 1):
        w = certificate(n, clauses, {}, core[:h])
        u = value(n, clauses, {}, w)
        records.append(dict(core_size=h, upper_bound=u, certified_bits=n - math.log2(u)))
    assert exact_count(n, clauses, {}) == 1
    assert abs(records[-1]['upper_bound'] - 1) < 1e-9
    # Large information with no small ordinary clause: same padding core for
    # all sign patterns, now no restriction on the core itself.
    padding = [disjunction(((q + i, 1),) + tuple((j, 1 - a[j]) for j in core))
               for i in range(t) for a in assignments(core)]
    uc = value(n, padding, {}, certificate(n, padding, {}, core))
    assert abs(uc - 2 ** q) < 1e-9
    # Opposite cardinality constraints show that sums and packings complement
    # each other: a sum refutes immediately, while unconditioned packing does not.
    opposite = [Constraint(tuple((j, 1) for j in range(6)), 2),
                Constraint(tuple((j, 0) for j in range(6)), 2)]
    pack = value(6, opposite, {}, certificate(6, opposite, {}))
    assert pack == 22 and exact_count(6, opposite, {}) == 0
    return dict(gated_core=dict(n=n, clauses=len(clauses), widths=[q, q + 1],
                               exact_count=1, certificates=records),
                all_patterns=dict(n=n, clauses=len(padding), width=q + 1,
                                  conditioned_bound=uc, exact_count=2 ** q),
                opposite_cardinality=dict(packing_bound=pack, sum_bound=0,
                                          exact_count=0))


class Collector(Search):
    def __init__(self, f):
        super().__init__(f, {}, True, True, maxdeg_rule)
        self.states = []

    def closure(self, p, a, cons):
        ok = super().closure(p, a, cons)
        free = [v for v, b in enumerate(a) if b is None]
        if ok and 4 <= len(free) <= 10:
            rename = {v: j for j, v in enumerate(free)}
            clauses = []
            for fav, threshold, used in cons:
                assert all(weight == 1 for _, weight in fav.values())
                lits = tuple((rename[v], b) for v, (b, _) in fav.items() if v in rename)
                budget = threshold - used - 1
                if len(lits) > budget:
                    clauses.append(Constraint(lits, budget))
            if len(clauses) >= 2:
                self.states.append((len(free), clauses))
        return ok


def actual_frontiers(seed=7102029):
    rng = random.Random(seed)
    rows = []
    for trial in range(12):
        f = biased(14, .85, .5, 0, rng)
        s = Collector(f)
        s.run(initial(f, {}), [None] * f.n, [])
        states = rng.sample(s.states, min(5, len(s.states)))
        for n, clauses in states:
            occurrence = {v: sum(v in dict(c.literals) for c in clauses) for v in range(n)}
            core = sorted(range(n), key=lambda v: (-occurrence[v], v))[:2]
            u0 = value(n, clauses, {}, certificate(n, clauses, {}))
            uh = value(n, clauses, {}, certificate(n, clauses, {}, core))
            rr = [tuple(1 if dict(c.literals).get(v) == 1 else
                        -1 if dict(c.literals).get(v) == 0 else 0 for v in range(n))
                  for c in clauses]
            us, _ = choose_bound(rr, [c.budget for c in clauses], n)
            exact = exact_count(n, clauses, {})
            assert exact <= min(u0, uh, us) + 1e-7
            assert uh <= u0 + 1e-7
            rows.append(dict(formula=trial, free_variables=n, constraints=len(clauses),
                             exact_count=exact, packing_bound=u0,
                             core2_bound=uh, weighted_sum_bound=us))
    return dict(seed=seed, formulas=12, sampled_states=len(rows),
                core_improved=sum(r['core2_bound'] < r['packing_bound'] - 1e-7 for r in rows),
                core_better_than_sum=sum(r['core2_bound'] < r['weighted_sum_bound'] - 1e-7 for r in rows),
                sum_better_than_core=sum(r['weighted_sum_bound'] < r['core2_bound'] - 1e-7 for r in rows),
                rows=rows)


def main():
    result = dict(random_checks=check_random(), examples=examples(),
                  max2sat_frontiers=actual_frontiers())
    out = Path(__file__).with_name('learning_dichotomy_checks.json')
    out.write_text(json.dumps(result, indent=2) + '\n')
    compact = dict(result)
    compact['max2sat_frontiers'] = {k: v for k, v in result['max2sat_frontiers'].items()
                                   if k != 'rows'}
    print(json.dumps(compact, indent=2))


if __name__ == '__main__':
    main()
