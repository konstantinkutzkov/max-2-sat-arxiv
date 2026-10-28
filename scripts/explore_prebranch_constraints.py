#!/usr/bin/env python3
"""Exact finite checks for max2sat_prebranch_constraints.tex.

Standard-library only. Run from any directory; writes the companion JSON
beside this script. All mathematical claims in the note also have proofs.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb, prod, sqrt
from pathlib import Path
import json
import random


def bits(x, n):
    return tuple((x >> i) & 1 for i in range(n))


def from_clauses(n, clauses, units):
    c, h = 0, list(units)
    J = [[0] * n for _ in range(n)]
    # A signed unit difference is represented up to an additive constant.
    for u, a, v, b in clauses:
        table = {(i, j): int(i == a or j == b)
                 for i, j in product((0, 1), repeat=2)}
        c += table[0, 0]
        h[u] += table[1, 0] - table[0, 0]
        h[v] += table[0, 1] - table[0, 0]
        z = table[1, 1] - table[1, 0] - table[0, 1] + table[0, 0]
        J[u][v] += z
        J[v][u] += z
    return c, h, J


def scores_of(c, h, J):
    n = len(h)
    return [c + sum(h[i] * ((x >> i) & 1) for i in range(n))
            + sum(J[i][j] * ((x >> i) & 1) * ((x >> j) & 1)
                  for i in range(n) for j in range(i + 1, n))
            for x in range(1 << n)]


def single_ok(scores, x, u, preference):
    delta = scores[x] - scores[x ^ (1 << u)]
    return delta > 0 or (delta == 0 and ((x >> u) & 1) == preference[u])


def local_survivors(scores, n, preference):
    return [x for x in range(1 << n)
            if all(single_ok(scores, x, u, preference) for u in range(n))]


def swap_edges(h, J):
    """All unconditional implications x_v => x_u; lex prefers bit 1 at u<v."""
    n = len(h)
    edges = []
    for u in range(n):
        for v in range(n):
            if u == v:
                continue
            lower = h[u] - h[v] + sum(
                min(0, J[u][w] - J[v][w])
                for w in range(n) if w not in (u, v))
            if lower > 0 or (lower == 0 and u < v):
                edges.append((u, v))
    return edges


def edge_ok(x, uv):
    u, v = uv
    return bool((x >> u) & 1) or not bool((x >> v) & 1)


def finite_checks():
    rng = random.Random(12102026)
    totals = Counter()
    for trial in range(100):
        n = 4 + trial % 4
        clauses = [(u, rng.randrange(2), v, rng.randrange(2))
                   for u in range(n) for v in range(u + 1, n)
                   if rng.random() < 0.65]
        if trial % 5 == 0:
            clauses += [(u, 1, v, 1) for u, v in combinations(range(n), 2)]
        units = [rng.randrange(-2, 3) for _ in range(n)]
        c, h, J = from_clauses(n, clauses, units)
        scores = scores_of(c, h, J)
        pref = (1,) * n
        best = max(range(1 << n), key=lambda x: (scores[x], bits(x, n)))
        survivors = local_survivors(scores, n, pref)
        assert best in survivors
        totals['formulas'] += 1
        totals['one_vertex_checks'] += n * (1 << n)
        for u in range(n):
            assert sum(single_ok(scores, x, u, pref)
                       for x in range(1 << n)) == 1 << (n - 1)

        # User's occurrence-gap identity, including the signed unit count.
        for u in range(n):
            pos = [(v if u == a else a, sb if u == a else sa)
                   for a, sa, v, sb in clauses
                   if (a == u and sa == 1) or (v == u and sb == 1)]
            neg = [(v if u == a else a, sb if u == a else sa)
                   for a, sa, v, sb in clauses
                   if (a == u and sa == 0) or (v == u and sb == 0)]
            G = len(pos) - len(neg) + units[u]
            for x in range(1 << n):
                A = sum(((x >> v) & 1) == b for v, b in pos)
                B = sum(((x >> v) & 1) == b for v, b in neg)
                d = scores[x | (1 << u)] - scores[x & ~(1 << u)]
                assert d == G - A + B
                if not ((x >> u) & 1) and single_ok(scores, x, u, pref):
                    assert A >= G + 1
                    totals['one_neighborhood_implications'] += 1
                totals['flip_identities'] += 1

        # No effective internal interactions: one best response per center.
        T = []
        for u in range(n):
            if all(J[u][v] == 0 for v in T):
                T.append(u)
        assert sum(all(single_ok(scores, x, u, pref) for u in T)
                   for x in range(1 << n)) == 1 << (n - len(T))
        totals['independent_center_counts'] += 1

        edges = swap_edges(h, J)
        for u, v in edges:
            assert edge_ok(best, (u, v))
            for x in range(1 << n):
                if not edge_ok(x, (u, v)):
                    z = x ^ (1 << u) ^ (1 << v)
                    assert (scores[z], bits(z, n)) > (scores[x], bits(x, n))
                    totals['exchange_implications'] += 1
        common = [x for x in survivors if all(edge_ok(x, e) for e in edges)]
        assert best in common
        used, matching = set(), []
        for u, v in edges:
            if u not in used and v not in used:
                matching.append((u, v))
                used.update((u, v))
        count = sum(all(edge_ok(x, e) for e in matching) for x in range(1 << n))
        assert count == 3 ** len(matching) * 2 ** (n - 2 * len(matching))
        totals['matching_counts'] += 1

        # Check affine minimum for every pair-pattern replacement on smaller cases.
        if trial < 35:
            for S in combinations(range(n), 2):
                outside = [w for w in range(n) if w not in S]
                for a, b in product(product((0, 1), repeat=2), repeat=2):
                    if a == b:
                        continue
                    xa = sum(a[i] << S[i] for i in range(2))
                    xb = sum(b[i] << S[i] for i in range(2))
                    constant = scores[xb] - scores[xa]
                    coeff = [sum(J[u][w] * (b[j] - a[j])
                                 for j, u in enumerate(S)) for w in outside]
                    lower = constant + sum(min(0, z) for z in coeff)
                    vals = []
                    for y in product((0, 1), repeat=len(outside)):
                        mask = sum(z << w for z, w in zip(y, outside))
                        vals.append(scores[xb | mask] - scores[xa | mask])
                    assert lower == min(vals)
                    totals['block_minimum_checks'] += 1
                    if lower > 0 or (lower == 0 and b > a):
                        assert tuple((best >> w) & 1 for w in S) != a
                        totals['block_nogoods'] += 1

    # Exact expectation over all random tie vectors on small formulas.
    for trial in range(24):
        n = 5
        clauses = [(u, rng.randrange(2), v, rng.randrange(2))
                   for u, v in combinations(range(n), 2) if rng.random() < 0.7]
        c, h, J = from_clauses(n, clauses, [rng.randrange(-1, 2) for _ in range(n)])
        scores = scores_of(c, h, J)
        predicted = Fraction(0)
        for x in range(1 << n):
            diffs = [scores[x] - scores[x ^ (1 << u)] for u in range(n)]
            if min(diffs) >= 0:
                predicted += Fraction(1, 1 << diffs.count(0))
        actual = sum(len(local_survivors(scores, n, bits(a, n)))
                     for a in range(1 << n))
        assert Fraction(actual, 1 << n) == predicted
        totals['random_tie_identities'] += 1
    return dict(totals)


def marginal_one_probability(degree, bias, preference):
    # D = bias + S_degree, P(S_degree=s)=binom(2d,d+s)/4^d.
    numerator = sum(comb(2 * degree, degree + s)
                    for s in range(-degree, degree + 1)
                    if bias + s > 0 or (bias + s == 0 and preference == 1))
    return Fraction(numerator, 4 ** degree)


def exhaust_signs(name, n, edges, units, preference):
    N = 1 << n
    unit_scores = [sum(units[u] * ((x >> u) & 1) for u in range(n)) for x in range(N)]
    edge_tables = [[[int(((x >> u) & 1) == a or ((x >> v) & 1) == b)
                     for x in range(N)]
                    for a, b in product((0, 1), repeat=2)] for u, v in edges]
    point_counts, hist = [0] * N, Counter()
    number_signings = 4 ** len(edges)
    for signing in product(range(4), repeat=len(edges)):
        scores = list(unit_scores)
        for j, label in enumerate(signing):
            scores = [a + b for a, b in zip(scores, edge_tables[j][label])]
        survivors = local_survivors(scores, n, preference)
        assert survivors and max(scores[x] for x in survivors) == max(scores)
        hist[len(survivors)] += 1
        for x in survivors:
            point_counts[x] += 1
    degree = [sum(u in e for e in edges) for u in range(n)]
    p = [marginal_one_probability(degree[u], units[u], preference[u]) for u in range(n)]
    for x in range(N):
        qprod = prod(p[u] if ((x >> u) & 1) else 1 - p[u] for u in range(n))
        assert Fraction(point_counts[x], number_signings) ** 2 <= qprod
    mean = Fraction(sum(point_counts), number_signings)
    refined = prod(sqrt(float(q)) + sqrt(float(1 - q)) for q in p)
    assert float(mean) <= refined + 1e-12 <= 2 ** (n / 2) + 2e-12
    return {'name': name, 'n': n, 'edges': len(edges), 'units': units,
            'preferences': preference, 'signings': number_signings,
            'mean_survivors_exact': str(mean), 'mean_survivors': float(mean),
            'read_two_bound': refined, 'universal_bound': 2 ** (n / 2),
            'histogram': dict(sorted(hist.items())), 'pointwise_checks': N}


def random_sign_checks():
    cases = [
        ('empty', 4, [], [0, 0, 0, 0], [1] * 4),
        ('matching', 4, [(0, 1), (2, 3)], [0] * 4, [1] * 4),
        ('path', 4, [(0, 1), (1, 2), (2, 3)], [0] * 4, [1] * 4),
        ('star', 4, [(0, 1), (0, 2), (0, 3)], [0] * 4, [1] * 4),
        ('triangle', 3, list(combinations(range(3), 2)), [0] * 3, [1] * 3),
        ('complete', 4, list(combinations(range(4), 2)), [0] * 4, [1] * 4),
        ('complete_units', 4, list(combinations(range(4), 2)), [1, -1, 0, 2], [1] * 4),
        ('complete_mixed_ties', 4, list(combinations(range(4), 2)), [1, -1, 0, 2], [0, 1, 0, 1]),
    ]
    return [exhaust_signs(*args) for args in cases]


def structural_examples():
    rows = []
    for n in (6, 8, 10, 12):
        # Complete Max Cut encoded by the two complementary clauses per edge.
        clauses = [(u, b, v, b) for u, v in combinations(range(n), 2) for b in (0, 1)]
        c, h, J = from_clauses(n, clauses, [0] * n)
        scores = scores_of(c, h, J)
        single = local_survivors(scores, n, [1] * n)
        chain = [(u, u + 1) for u in range(n - 1)]
        allowed = [x for x in range(1 << n) if all(edge_ok(x, e) for e in chain)]
        assert len(single) == comb(n, n // 2)
        assert len(allowed) == n + 1
        assert max(scores[x] for x in allowed) == max(scores)
        assert len(set(single).intersection(allowed)) == 1
        rows.append({'n': n, 'single_comparisons': len(single),
                     'chain_only': len(allowed), 'single_and_chain': 1})
    return rows


def main():
    result = {'finite_checks': finite_checks(), 'random_sign_checks': random_sign_checks(),
              'complete_cut_examples': structural_examples()}
    dest = Path(__file__).with_name('prebranch_constraint_checks.json')
    dest.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
