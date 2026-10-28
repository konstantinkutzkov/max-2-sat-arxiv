#!/usr/bin/env python3
"""Exact checks for the early-enumeration proof; standard library only.

The experiment verifies correctness and identities, not asymptotic
probability estimates. Run: python3 explore_early_enumeration.py
"""
import itertools
import json
import math
import random
from pathlib import Path


def signed_regular(n, degree, rng):
    """A relabeled circulant regular graph with independent incidence signs."""
    assert degree < n and n % 2 == 0
    edges = set()
    for u in range(n):
        for offset in range(1, degree // 2 + 1):
            edges.add(tuple(sorted((u, (u + offset) % n))))
        if degree % 2:
            edges.add(tuple(sorted((u, (u + n // 2) % n))))
    labels = list(range(n))
    rng.shuffle(labels)
    clauses = []
    for u, v in sorted(edges):
        u, v = sorted((labels[u], labels[v]))
        clauses.append((u, rng.choice((-1, 1)), v, rng.choice((-1, 1))))
    assert all(sum(u == w or v == w for u, _, v, _ in clauses) == degree
               for w in range(n))
    return clauses


def coefficients(n, clauses):
    J = [[0] * n for _ in range(n)]
    h = [0] * n
    for u, su, v, sv in clauses:
        J[u][v] = J[v][u] = su * sv
        h[u] += su
        h[v] += sv
    return J, h


def score(clauses, assignment):
    return sum(assignment[u] == su or assignment[v] == sv
               for u, su, v, sv in clauses)


def learned(J, h, prefix):
    n = len(h)
    constraints = []
    shortfall_twice = 0
    for i, value in enumerate(prefix):
        gap = h[i] - sum(J[i][j] * prefix[j] for j in range(i))
        preferred = 1 if gap >= 0 else -1
        if value == preferred:
            continue
        support = {w: J[i][w] * value for w in range(i + 1, n) if J[i][w]}
        assert (len(support) - abs(gap)) % 2 == 0
        allowance = (len(support) - abs(gap)) // 2 - 1
        constraints.append((support, allowance))
        shortfall_twice += abs(gap) + 2
    return constraints, shortfall_twice


def budget(n, prefix, constraints):
    t = len(prefix)
    counts = [[0, 0] for _ in range(n - t)]  # indices 0,1 mean -1,+1
    allowance = 0
    for support, k in constraints:
        allowance += k
        for w, bad in support.items():
            if w < t:
                allowance -= int(prefix[w] == bad)
            else:
                counts[w - t][int(bad == 1)] += 1
    B = allowance - sum(min(row) for row in counts)
    weights = [abs(row[1] - row[0]) for row in counts]
    cheaper = [-1 if row[0] <= row[1] else 1 for row in counts]
    return B, weights, cheaper


def count_budget(B, weights):
    if B < 0:
        return 0
    cap = min(B, sum(weights))
    dp = [0] * (cap + 1)
    dp[0] = 1
    for w in weights:
        for k in range(cap, w - 1, -1):
            dp[k] += dp[k - w]
    return sum(dp)


def generate_budget(B, weights, cheaper):
    """Depth-first generator with polynomial space, including zero weights."""
    assignment = [0] * len(weights)

    def visit(i, remaining):
        if remaining < 0:
            return
        if i == len(weights):
            yield tuple(assignment)
            return
        assignment[i] = cheaper[i]
        yield from visit(i + 1, remaining)
        if weights[i] <= remaining:
            assignment[i] = -cheaper[i]
            yield from visit(i + 1, remaining - weights[i])

    yield from visit(0, B)


def check_instance(n, degree, trial, rng):
    clauses = signed_regular(n, degree, rng)
    J, h = coefficients(n, clauses)
    T = (n + 1) // 2
    optimum = -1
    exhaustive_optimum = -1
    candidates = 0
    identities = 0
    empty_budgets = 0
    nontrivial_budgets = 0
    for prefix in itertools.product((-1, 1), repeat=T):
        constraints, S2 = learned(J, h, prefix)
        B, weights, cheaper = budget(n, prefix, constraints)
        generated = set(generate_budget(B, weights, cheaper))
        predicted = count_budget(B, weights)
        assert len(generated) == predicted
        direct = set()
        for suffix in itertools.product((-1, 1), repeat=n - T):
            assignment = prefix + suffix
            total_bad = sum(sum(assignment[w] == bad for w, bad in support.items())
                            for support, _ in constraints)
            total_allowance = sum(k for _, k in constraints)
            Q2 = sum(2 * sum(assignment[w] == bad for w, bad in support.items())
                     - len(support) for support, _ in constraints)
            assert 2 * (total_bad - total_allowance) == S2 + Q2
            identities += 1
            value = score(clauses, assignment)
            exhaustive_optimum = max(exhaustive_optimum, value)
            if total_bad <= total_allowance:
                direct.add(suffix)
                optimum = max(optimum, value)
        assert direct == generated
        candidates += predicted
        empty_budgets += predicted == 0
        nontrivial_budgets += 0 < predicted < 2 ** (n - T)
    assert optimum == exhaustive_optimum
    return dict(n=n, degree=degree, trial=trial, optimum=optimum,
                prefixes=2 ** T, candidates=candidates,
                exhaustive_candidates=2 ** n, identity_checks=identities,
                empty_budgets=empty_budgets,
                nontrivial_nonempty_budgets=nontrivial_budgets)


def main():
    rng = random.Random(81020262)
    rows = []
    for n in (6, 8, 10, 12):
        for degree in sorted({2, min(6, n - 1), n - 1}):
            for trial in range(4):
                rows.append(check_instance(n, degree, trial, rng))
    assert 2 / 25 + 1 / 100 + 1 / 20 < 1 / (4 * math.sqrt(3))
    assert all(D / 2 + math.sqrt(D) + .5 <= D for D in range(6, 1001))
    results = dict(
        seed=81020262,
        summary=dict(instances=len(rows),
                     optimum_matches=len(rows),
                     prefix_count_checks=sum(x['prefixes'] for x in rows),
                     full_assignment_identity_checks=sum(x['identity_checks'] for x in rows),
                     empty_budgets=sum(x['empty_budgets'] for x in rows),
                     nontrivial_nonempty_budgets=sum(x['nontrivial_nonempty_budgets'] for x in rows)),
        constants=dict(shortfall_coefficient=1 / (4 * math.sqrt(3)),
                       allocated_deviations=2 / 25 + 1 / 100 + 1 / 20,
                       regular_high_probability_base=2 * math.exp(-1 / 1250),
                       regular_expected_base=2 * math.exp(-1 / 625)),
        instances=rows)
    Path(__file__).with_name('early_enumeration_checks.json').write_text(
        json.dumps(results, indent=2) + '\n')
    print(json.dumps({k: results[k] for k in ('summary', 'constants')}, indent=2))


if __name__ == '__main__':
    main()
