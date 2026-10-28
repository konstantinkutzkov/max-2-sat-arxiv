"""Exact finite checks for the SBM specialization and supplied-group gains.

These check identities and optimum preservation, not asymptotic tail bounds.
Run with standard-library Python; the report is written beside this script.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import random


def rank(matrix):
    rows = [list(row) for row in matrix]
    pivot = 0
    for col in range(len(rows[0])):
        chosen = next((r for r in range(pivot, len(rows)) if rows[r][col]), None)
        if chosen is None:
            continue
        rows[pivot], rows[chosen] = rows[chosen], rows[pivot]
        scale = rows[pivot][col]
        rows[pivot] = [value / scale for value in rows[pivot]]
        for r in range(pivot + 1, len(rows)):
            factor = rows[r][col]
            rows[r] = [a - factor * b for a, b in zip(rows[r], rows[pivot])]
        pivot += 1
        if pivot == len(rows):
            break
    return pivot


def score(x, edges, fields):
    return sum(x[u] != x[v] for u, v in edges) + sum(a * b for a, b in zip(x, fields))


def checks():
    rng = random.Random(20261012)
    report = dict(pair_moment_checks=0, mean_rank_checks=0, graphs=0,
                  assignment_checks=0, group_gain_identities=0,
                  optimum_survival_checks=0, clique_field_checks=0)
    models = [
        [[F(3, 4), F(1, 4)], [F(1, 4), F(3, 4)]],
        [[F(1, 20), F(1, 10)], [F(1, 10), F(3, 20)]],
        [[F(19, 20), F(9, 10)], [F(9, 10), F(17, 20)]],
        [[F(1, 2)] * 3 for _ in range(3)],
        [[F(1), F(0)], [F(0), F(1)]],
        [[F(2, 3), F(1, 4), F(1, 2)],
         [F(1, 4), F(3, 5), F(1, 3)],
         [F(1, 2), F(1, 3), F(3, 4)]],
    ]
    for pi in models:
        k = len(pi)
        for row in pi:
            for probability in row:
                mean = sum(prob * value for value, prob in ((F(0), 1 - probability), (F(-2), probability)))
                variance = sum(prob * (value - mean) ** 2
                               for value, prob in ((F(0), 1 - probability), (F(-2), probability)))
                assert mean == -2 * probability
                assert variance == 4 * probability * (1 - probability)
                assert all(abs(value - mean) <= 2 for value in (F(0), F(-2)))
                report['pair_moment_checks'] += 1
        for n in (5, 6, 7):
            # Deliberately unequal community sizes in some instances.
            groups = [min(t, k - 1) for t in range(n)]
            mean_matrix = [[-2 * pi[groups[t]][groups[w]] for w in range(n)] for t in range(n)]
            assert rank(mean_matrix) <= k
            assert max(sum(abs(z) for z in row) for row in mean_matrix) <= 2 * n
            assert max(abs(mean_matrix[t][t]) for t in range(n)) <= 2
            report['mean_rank_checks'] += 1
            edges = [(u, v) for u in range(n) for v in range(u + 1, n)
                     if rng.randrange(pi[groups[u]][groups[v]].denominator)
                     < pi[groups[u]][groups[v]].numerator]
            neighbors = [{v if u == t else u for u, v in edges if t in (u, v)} for t in range(n)]
            # Fields may depend on the sampled graph.
            fields = [len(neighbors[t]) + rng.randrange(-4, 3) for t in range(n)]
            assignments = list(product((0, 1), repeat=n))
            values = [score(x, edges, fields) for x in assignments]
            optimum = max(values)
            depth = n // 2
            rounds = [0] * (n // 4) + [1] * (depth - n // 4) + [2] * (n - depth)
            for x, value in zip(assignments, values):
                counts = [sum(x[t] for t in range(n) if groups[t] == a) for a in range(k)]
                summed = F(0)
                for t in range(n):
                    a = groups[t]
                    gain = fields[t] + len(neighbors[t]) - 2 * sum(x[w] for w in neighbors[t])
                    flipped = list(x)
                    flipped[t] = 1 - flipped[t]
                    assert score(flipped, edges, fields) - value == (1 - 2 * x[t]) * gain
                    adjusted = gain - 2 * sum(
                        pi[a][b] * (counts[b] - sum(x[w] for w in range(n) if w != t and groups[w] == b))
                        for b in range(k))
                    assert adjusted == gain - 2 * pi[a][a] * x[t]
                    assert abs(adjusted - gain) <= 2 * pi[a][a]
                    report['group_gain_identities'] += 1
                    if t >= depth:
                        continue
                    average_bits = [F(x[w]) if rounds[w] < rounds[t] else F(1, 2) for w in range(n)]
                    delta = fields[t] + len(neighbors[t]) - 2 * sum(average_bits[w] for w in neighbors[t])
                    delta -= 2 * sum(
                        pi[a][b] * (counts[b] - sum(average_bits[w] for w in range(n) if w != t and groups[w] == b))
                        for b in range(k))
                    preferred = int(delta >= 0)
                    if x[t] != preferred:
                        comparison = (2 * preferred - 1) * adjusted - 2 * pi[a][a]
                        summed += comparison
                        if value == optimum:
                            assert comparison <= 0
                if value == optimum:
                    assert summed <= 0
                    report['optimum_survival_checks'] += 1
                report['assignment_checks'] += 1
            report['graphs'] += 1
    for n in range(2, 9):
        fields = [rng.randrange(-5, 6) for _ in range(n)]
        edges = [(u, v) for u in range(n) for v in range(u + 1, n)]
        brute = max(score(x, edges, fields) for x in product((0, 1), repeat=n))
        ordered = sorted(fields, reverse=True)
        compressed = max(h * (n - h) + sum(ordered[:h]) for h in range(n + 1))
        assert brute == compressed
        report['clique_field_checks'] += 1
    return report


if __name__ == '__main__':
    result = checks()
    Path(__file__).with_name('dense_max2sat_sbm_checks.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
