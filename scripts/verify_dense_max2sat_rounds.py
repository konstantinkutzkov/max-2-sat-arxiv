"""Exact finite checks for weighted comparisons, rounds, and projection errors.

Uses rational arithmetic for every assertion. Floating point is used only
to propose Jacobi rotations; orthogonality and progress are then checked
exactly. This is not a verification of the asymptotic probability bounds.
"""
from fractions import Fraction as F
from itertools import product
from math import atan2, isqrt, pi, tan
from pathlib import Path
import json
import random


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def transpose(a):
    return list(map(list, zip(*a)))


def multiply(a, b):
    return [[dot(row, col) for col in zip(*b)] for row in a]


def identity(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def score(x, a, j):
    return dot(x, a) + sum(j[t][w] * x[t] * x[w]
                          for t in range(len(x)) for w in range(t + 1, len(x)))


def round_comparison(x, a, j, lam, vectors, guessed, errors, rounds):
    n = len(x)
    p = [[sum(l * v[t] * v[w] for l, v in zip(lam, vectors))
          for w in range(n)] for t in range(n)]
    remainder = [[j[t][w] - p[t][w] if t != w else F(0)
                  for w in range(n)] for t in range(n)]
    shifted = [a[t] + sum(l * y * v[t] for l, y, v in zip(lam, guessed, vectors))
               for t in range(n)]
    slack = [sum(abs(l) * abs(v[t]) * (error + abs(v[t]))
                 for l, v, error in zip(lam, vectors, errors)) for t in range(n)]
    depth = len(rounds)
    rnd = rounds + [max(rounds) + 1] * (n - depth)
    signs = [2 * bit - 1 for bit in x]
    shortfall = same = later = tested = F(0)
    per_creator = []
    for t in range(n):
        original_gain = a[t] + dot(j[t], x)
        auxiliary_gain = shifted[t] + dot(remainder[t], x)
        assert abs(original_gain - auxiliary_gain) <= slack[t]
        if t >= depth:
            continue
        delta = shifted[t] + sum(remainder[t][w] * x[w] for w in range(n) if rnd[w] < rnd[t])
        delta += sum(remainder[t][w] * F(1, 2) for w in range(n) if w != t and rnd[w] >= rnd[t])
        preferred = int(delta >= 0)
        if x[t] == preferred:
            continue
        gain = (2 * preferred - 1) * auxiliary_gain
        per_creator.append(gain <= slack[t])
        tested += gain - slack[t]
        shortfall += abs(delta) - slack[t]
        same -= signs[t] * sum(remainder[t][w] * signs[w]
                               for w in range(n) if w != t and rnd[w] == rnd[t]) * F(1, 2)
        later -= signs[t] * sum(remainder[t][w] * signs[w]
                                for w in range(n) if rnd[w] > rnd[t]) * F(1, 2)
    assert tested == shortfall + same + later
    return tested <= 0, all(per_creator)


def comparison_checks(rng):
    counts = dict(formulas=0, weighted_assignments=0, round_race_identities=0,
                  projection_gain_bounds=0, optimum_survival_checks=0)
    for n, trial in product((5, 6, 7), range(6)):
        j = [[F(0) for _ in range(n)] for _ in range(n)]
        for t in range(n):
            for w in range(t + 1, n):
                j[t][w] = j[w][t] = F(rng.randrange(-2, 3))
        a = [F(rng.randrange(-4, 5)) for _ in range(n)]
        assignments = tuple(product((0, 1), repeat=n))
        scores = [score(x, a, j) for x in assignments]
        optimum = max(scores)
        depth = n // 2 + 1
        best_weighted = None
        for x, value in zip(assignments, scores):
            total = F(0)
            for t in range(depth):
                degree = sum(j[t][w] != 0 for w in range(n))
                if degree == 0:
                    weight = F(1)
                else:
                    root = isqrt(degree)
                    weight = F(1, root if root * root == degree else root + 1)
                delta = a[t] + dot(j[t][:t], x[:t]) + sum(j[t][t + 1:]) * F(1, 2)
                preferred = int(delta >= 0)
                if x[t] != preferred:
                    total += weight * ((2 * preferred - 1) * (a[t] + dot(j[t], x)) + 1)
            if total <= 0:
                best_weighted = value if best_weighted is None else max(best_weighted, value)
            counts['weighted_assignments'] += 1
            for mode in ("counts", "approximate"):
                if mode == "counts":
                    lam = [sum(j[t][w] for t in range(n) for w in range(t + 1, n)) / (n * (n - 1) // 2)]
                    vectors, errors, guessed = [[F(1)] * n], [F(0)], [F(sum(x))]
                else:
                    lam = [F(3, 2), F(-2, 3)]
                    vectors = [[F((t % 3) - 1, 2) for t in range(n)],
                               [F(1 if t % 2 else -1, 3) for t in range(n)]]
                    errors = [F(1, 2)] * 2
                    guessed = [F(round(dot(v, x))) for v in vectors]
                rounds = [t % 3 for t in range(depth)]
                rounds.sort()
                passed, each = round_comparison(x, a, j, lam, vectors, guessed, errors, rounds)
                counts['round_race_identities'] += 1
                counts['projection_gain_bounds'] += n
                if value == optimum:
                    assert passed and each
                    counts['optimum_survival_checks'] += 1
        assert best_weighted == optimum
        counts['formulas'] += 1
    return counts


def jacobi_checks(rng):
    rotations = 0
    for trial in range(3):
        n = 4
        a = [[F(0) for _ in range(n)] for _ in range(n)]
        for t in range(n):
            for w in range(t, n):
                a[t][w] = a[w][t] = F(rng.randrange(-4, 5))
        original = [row[:] for row in a]
        q = identity(n)
        for step in range(12):
            t, w = max(((t, w) for t in range(n) for w in range(t + 1, n)), key=lambda pair: abs(a[pair[0]][pair[1]]))
            if a[t][w] == 0:
                break
            before = sum(a[i][j]**2 for i in range(n) for j in range(n) if i != j)
            angle = atan2(float(2 * a[t][w]), float(a[w][w] - a[t][t])) * F(1, 2)
            if angle > pi / 4:
                angle -= pi * F(1, 2)
            if angle < -pi / 4:
                angle += pi * F(1, 2)
            parameter = F(tan(angle * F(1, 2))).limit_denominator(1 << 24)
            cosine = (1 - parameter**2) / (1 + parameter**2)
            sine = 2 * parameter / (1 + parameter**2)
            rotation = identity(n)
            rotation[t][t] = rotation[w][w] = cosine
            rotation[t][w], rotation[w][t] = sine, -sine
            a = multiply(transpose(rotation), multiply(a, rotation))
            q = multiply(q, rotation)
            assert multiply(transpose(q), q) == identity(n)
            assert multiply(q, multiply(a, transpose(q))) == original
            after = sum(a[i][j]**2 for i in range(n) for j in range(n) if i != j)
            assert after <= before * F(11, 12) + F(1, 10**10)
            rotations += 1
    return rotations


if __name__ == "__main__":
    rng = random.Random(20261012)
    result = comparison_checks(rng)
    result['rational_jacobi_rotations'] = jacobi_checks(rng)
    result['status'] = 'passed'
    result['scope'] = 'Finite exact identities and optimum preservation, not asymptotic bounds.'
    Path(__file__).with_name('dense_max2sat_rounds_checks.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
