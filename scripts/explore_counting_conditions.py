#!/usr/bin/env python3
"""Exact checks for deterministic neighborhood-count conditions."""
import itertools
import json
import math
import random
from pathlib import Path

from explore_early_enumeration import coefficients, learned, budget, count_budget, score


def hadamard(q):
    H = [[1]]
    while len(H) < q:
        H = [row + row for row in H] + [row + [-x for x in row] for row in H]
    assert len(H) == q
    return H


def instance(p, q, gap):
    H = hadamard(q)[:p]
    assert (q + gap) % 2 == 0
    own = [1] * ((q + gap) // 2) + [-1] * ((q - gap) // 2)
    clauses = [(i, own[w], p + w, own[w] * H[i][w])
               for i in range(p) for w in range(q)]
    J, h = coefficients(p + q, clauses)
    assert h[:p] == [gap] * p
    for i in range(p):
        for j in range(p):
            assert sum(H[i][w] * H[j][w] for w in range(q)) == (q if i == j else 0)
    return H, clauses, J, h


def check(p, q, gap, exhaustive):
    H, clauses, J, h = instance(p, q, gap)
    W = 0
    optimum = -1
    retained_optimum = -1
    assignments_checked = 0
    for prefix in itertools.product((-1, 1), repeat=p):
        constraints, S2 = learned(J, h, prefix)
        B, weights, cheaper = budget(p + q, prefix, constraints)
        N = count_budget(B, weights)
        k = prefix.count(-1)
        V = sum(sum(-H[i][w] for i in range(p) if prefix[i] == -1) ** 2
                for w in range(q))
        assert V == q * k
        assert S2 == k * (gap + 2)
        if gap:
            assert N <= 2 ** q * math.exp(-gap * gap * k / (2 * q)) + 1e-9
        elif k and q >= 16 * p:
            assert N * 32 >= 3 * 2 ** q
        if exhaustive:
            direct = 0
            for suffix in itertools.product((-1, 1), repeat=q):
                full = prefix + suffix
                value = score(clauses, full)
                optimum = max(optimum, value)
                total = sum(sum(full[w] == bad for w, bad in support.items()) - allowance
                            for support, allowance in constraints)
                Q2 = sum(2 * sum(full[w] == bad for w, bad in support.items()) - len(support)
                         for support, _ in constraints)
                assert 2 * total == S2 + Q2
                assignments_checked += 1
                if total <= 0:
                    direct += 1
                    retained_optimum = max(retained_optimum, value)
            assert direct == N
        W += N
    row = dict(p=p, q=q, gap=gap, prefixes=2 ** p, candidates=W,
               candidate_fraction=W / 2 ** (p + q),
               exhaustive_assignments_checked=assignments_checked)
    if gap:
        upper = 2 ** q * (1 + math.exp(-gap * gap / (2 * q))) ** p
        assert W <= upper
        row['upper_bound'] = upper
    else:
        lower = 3 * (2 ** p - 1) * 2 ** q / 32
        assert W >= lower
        row['lower_bound'] = lower
    if exhaustive:
        assert optimum == retained_optimum
        row['optimum'] = optimum
    return row


def check_general_identities():
    """Check the ordered-count representation on non-bipartite inputs."""
    rng = random.Random(81020263)
    checked = 0
    for n in (8, 10):
        T = n // 2
        for trial in range(2):
            clauses = [(i, rng.choice((-1, 1)), j, rng.choice((-1, 1)))
                       for i in range(n) for j in range(i + 1, n)]
            J, h = coefficients(n, clauses)
            R = [[J[i][w] if w > i else 0 for w in range(n)] for i in range(T)]
            A = [[sum(R[i][w] * R[j][w] for w in range(n))
                  for j in range(T)] for i in range(T)]
            norm_squared_bound = max(sum(abs(x) for x in row) for row in A)
            for full in itertools.product((-1, 1), repeat=n):
                gaps = [h[i] - sum(J[i][j] * full[j] for j in range(i)) for i in range(T)]
                v = [full[i] if full[i] != (1 if gaps[i] >= 0 else -1) else 0
                     for i in range(T)]
                balances = [sum(R[i][w] * v[i] for i in range(T)) for w in range(n)]
                energy = sum(x * x for x in balances)
                assert energy == sum(v[i] * A[i][j] * v[j] for i in range(T) for j in range(T))
                assert energy <= norm_squared_bound * sum(x * x for x in v)
                assert sum(x * x for x in gaps) <= 2 * sum(x * x for x in h[:T]) + 2 * norm_squared_bound * T
                constraints, S2 = learned(J, h, full[:T])
                Q2 = sum(2 * sum(full[w] == bad for w, bad in support.items()) - len(support)
                         for support, _ in constraints)
                assert Q2 == sum(full[w] * balances[w] for w in range(n))
                total = sum(sum(full[w] == bad for w, bad in support.items()) - k
                            for support, k in constraints)
                assert S2 + Q2 == 2 * total
                checked += 1
    return checked


def main():
    rows = [check(4, 4, 2, True), check(8, 8, 4, True),
            check(2, 32, 0, False), check(4, 64, 0, False),
            check(8, 128, 0, False)]
    results = dict(instances=rows,
                   regular_example_base=math.sqrt(2 * (1 + math.exp(-.5))),
                   general_complete_graph_identity_checks=check_general_identities(),
                   total_prefixes=sum(row['prefixes'] for row in rows),
                   exhaustive_assignments_checked=sum(row['exhaustive_assignments_checked'] for row in rows))
    Path(__file__).with_name('counting_condition_checks.json').write_text(
        json.dumps(results, indent=2) + '\n')
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
