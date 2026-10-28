#!/usr/bin/env python3
"""Exact tests of pair compression and the discrepancy-graph bound."""
import itertools
import json
import random
from fractions import Fraction
from pathlib import Path


def discrepancy(J, pair, eps):
    u, v = pair
    return {w for w in range(len(J)) if w not in pair and J[u][w] != eps * J[v][w]}


def conflict_graph(J, pairs, orientations):
    owner = {v: i for i, pair in enumerate(pairs) for v in pair}
    graph = [set() for _ in pairs]
    discrepancies = []
    for i, (pair, eps) in enumerate(zip(pairs, orientations)):
        D = discrepancy(J, pair, eps)
        discrepancies.append(D)
        for w in D:
            if w in owner:
                j = owner[w]
                graph[i].add(j)
                graph[j].add(i)
    return graph, discrepancies


def choose_compatible(graph):
    remaining = set(range(len(graph)))
    order = []
    degeneracy = 0
    while remaining:
        v = min(remaining, key=lambda i: (len(graph[i] & remaining), i))
        degeneracy = max(degeneracy, len(graph[v] & remaining))
        order.append(v)
        remaining.remove(v)
    colors = {}
    for v in reversed(order):
        used = {colors[w] for w in graph[v] if w in colors}
        c = 0
        while c in used:
            c += 1
        colors[v] = c
    groups = [[v for v in range(len(graph)) if colors[v] == c]
              for c in range(max(colors.values()) + 1)]
    colored = max(groups, key=len)
    # Derandomize the independent set consisting of local minima of a
    # uniformly random vertex ordering. All expectations are exact.
    waiting = set(range(len(graph)))
    blocked = set()
    picked = []
    weights = [Fraction(1, len(neighbors) + 1) for neighbors in graph]
    initial_expectation = sum(weights)
    while waiting:
        eligible = waiting - blocked

        def gain(u):
            value = (1 - weights[u]) if u in eligible else 0
            return value - sum(weights[v] for v in graph[u] & eligible)

        u = max(waiting, key=lambda v: (gain(v), -v))
        assert gain(u) >= 0
        if u not in blocked:
            picked.append(u)
        blocked.update(graph[u])
        waiting.remove(u)
    assert len(picked) >= initial_expectation
    assert all(not (graph[i] & set(picked)) for i in picked)
    return max((colored, picked), key=len), degeneracy, len(groups)


def planted(m, outsiders, mode, rng):
    n = 2 * m + outsiders
    pairs = [(2 * i, 2 * i + 1) for i in range(m)]
    eps = [rng.choice((-1, 1)) for _ in pairs]
    switches = [x for e in eps for x in (1, e)]
    J = [[0] * n for _ in range(n)]
    for i in range(m):
        u, v = pairs[i]
        J[u][v] = J[v][u] = rng.choice((-1, 1))
        for j in range(i + 1, m):
            value = rng.choice((-1, 1))
            for u in pairs[i]:
                for v in pairs[j]:
                    J[u][v] = J[v][u] = value * switches[u] * switches[v]
    for u in range(n):
        for v in range(max(u + 1, 2 * m), n):
            J[u][v] = J[v][u] = rng.choice((-1, 1))
    changed = set()
    if mode == 'matching':
        changed = {(i, i + 1) for i in range(0, m - 1, 2)}
    elif mode == 'cycle':
        changed = {tuple(sorted((i, (i + 1) % m))) for i in range(m)}
    elif mode == 'star':
        changed = {(0, j) for j in range(1, m)}
    for i, j in changed:
        u, v = pairs[i][0], pairs[j][0]
        J[u][v] = J[v][u] = -J[u][v]
    # Realize every nonzero interaction with one binary clause.
    clauses = []
    h = [0] * n
    for u in range(n):
        for v in range(u + 1, n):
            if J[u][v]:
                su = rng.choice((-1, 1))
                sv = su * J[u][v]
                clauses.append((u, su, v, sv))
                h[u] += su
                h[v] += sv
    units = []
    for u in range(n):
        for _ in range(rng.randrange(3)):
            s = rng.choice((-1, 1))
            h[u] += 2 * s
            units.append((u, s))
    return J, h, pairs, eps, clauses, units


def check_case(m, outsiders, mode, rng):
    J, h, pairs, eps, clauses, units = planted(m, outsiders, mode, rng)
    n = len(h)
    edges = [(u, v, J[u][v]) for u in range(n) for v in range(u + 1, n) if J[u][v]]

    def value(a):
        return sum(x * y for x, y in zip(h, a)) - sum(j * a[u] * a[v] for u, v, j in edges)

    graph, discrepancies = conflict_graph(J, pairs, eps)
    selected, degeneracy, colors = choose_compatible(graph)
    selected_vertices = {v for i in selected for v in pairs[i]}
    paired_vertices = {v for pair in pairs for v in pair}
    r_internal = max(len(D & paired_vertices) for D in discrepancies)
    total_internal = sum(len(D & paired_vertices) for D in discrepancies)
    conflict_edges = sum(map(len, graph)) // 2
    assert 2 * conflict_edges <= total_internal
    assert degeneracy <= r_internal
    assert len(selected) * (r_internal + 1) >= m
    assert len(selected) * (m + total_internal) >= m * m
    assert all(not (graph[i] & set(selected)) for i in selected)
    identity_checks = 0
    for pair, e, D in zip(pairs, eps, discrepancies):
        u, v = pair
        others = [w for w in range(n) if w not in pair]
        support_difference = sum(bool(J[u][w]) != bool(J[v][w]) for w in others)
        opposite = sum(bool(J[u][w]) and bool(J[v][w]) and J[u][w] != e * J[v][w] for w in others)
        dot = sum(J[u][w] * J[v][w] for w in others)
        energy = sum((J[u][w] - e * J[v][w]) ** 2 for w in others)
        assert len(D) == support_difference + opposite
        assert energy == support_difference + 4 * opposite
        assert energy == sum(J[u][w] ** 2 + J[v][w] ** 2 for w in others) - 2 * e * dot
        for _ in range(20):
            assigned = {w: rng.choice((-1, 1)) for w in others if rng.randrange(2)}
            du = h[u] - sum(J[u][w] * a for w, a in assigned.items())
            dv = h[v] - sum(J[v][w] * a for w, a in assigned.items())
            difference = h[u] - e * h[v] - sum((J[u][w] - e * J[v][w]) * a for w, a in assigned.items())
            assert du - e * dv == difference
            assert abs(difference) <= abs(h[u] - e * h[v]) + 2 * len(D)
            identity_checks += 1
    exhaustive_best = None
    for a in itertools.product((-1, 1), repeat=n):
        z = value(a)
        exhaustive_best = z if exhaustive_best is None else max(exhaustive_best, z)
        if a == (1,) * n:
            sat = sum(a[u] == su or a[v] == sv for u, su, v, sv in clauses)
            sat += sum(a[u] == s for u, s in units)
            assert 4 * sat == 3 * len(clauses) + 2 * len(units) + z
    outside = [v for v in range(n) if v not in selected_vertices]
    compressed_best = None
    candidates = 0
    mixed_choices = set()
    for fixed in itertools.product((-1, 1), repeat=len(outside)):
        a = [0] * n
        for v, x in zip(outside, fixed):
            a[v] = x
        states = []
        for i in selected:
            u, v = pairs[i]
            hu = h[u] - sum(J[u][w] * a[w] for w in outside)
            hv = h[v] - sum(J[v][w] * a[w] for w in outside)
            orient = 1 if hu >= eps[i] * hv else -1
            mixed_choices.add((i, orient))
            states.append([(1, eps[i]), (-1, -eps[i]), (orient, -eps[i] * orient)])
        for choice in itertools.product(*states):
            for i, state in zip(selected, choice):
                u, v = pairs[i]
                a[u], a[v] = state
            z = value(a)
            compressed_best = z if compressed_best is None else max(compressed_best, z)
            candidates += 1
    assert exhaustive_best == compressed_best
    assert candidates == 2 ** (n - 2 * len(selected)) * 3 ** len(selected)
    return dict(n=n, pairs=m, outsiders=outsiders, perturbation=mode,
                internal_discrepancy_bound=r_internal,
                full_discrepancy_bound=max(map(len, discrepancies)),
                total_internal_discrepancies=total_internal,
                conflicts=conflict_edges, colors=colors,
                selected_pairs=len(selected), optimum_scaled=compressed_best,
                candidates=candidates, exhaustive_candidates=2 ** n,
                gap_identity_checks=identity_checks,
                pairs_whose_mixed_choice_changes=sum((i, 1) in mixed_choices and (i, -1) in mixed_choices for i in selected))


def check_compatibility_lemmas():
    blocks = 0
    for a, b, c, d in itertools.product((-1, 0, 1), repeat=4):
        for ei, ej in itertools.product((-1, 1), repeat=2):
            discrepancies = int(a != ei * c) + int(b != ei * d)
            discrepancies += int(a != ej * b) + int(c != ej * d)
            assert discrepancies == 0 or discrepancies >= 2
            blocks += 1
    graphs = 0
    for m in range(1, 6):
        edges = list(itertools.combinations(range(m), 2))
        for mask in range(1 << len(edges)):
            graph = [set() for _ in range(m)]
            count = 0
            for bit, (u, v) in enumerate(edges):
                if mask & (1 << bit):
                    graph[u].add(v)
                    graph[v].add(u)
                    count += 1
            chosen, _, _ = choose_compatible(graph)
            assert len(chosen) * (m + 2 * count) >= m * m
            assert all(not (graph[u] & set(chosen)) for u in chosen)
            graphs += 1
    return blocks, graphs


def main():
    rng = random.Random(81020264)
    rows = [check_case(m, out, mode, rng)
            for m in (3, 4, 5) for out in (0, 2)
            for mode in ('none', 'matching', 'cycle', 'star')]
    rows.extend(check_case(6, 2, mode, rng) for mode in ('matching', 'star'))
    blocks, graphs = check_compatibility_lemmas()
    summary = dict(instances=len(rows), optimum_matches=len(rows),
                   interaction_blocks_checked=blocks,
                   conflict_graphs_checked=graphs,
                   exhaustive_assignments=sum(r['exhaustive_candidates'] for r in rows),
                   compressed_candidates=sum(r['candidates'] for r in rows),
                   gap_identity_checks=sum(r['gap_identity_checks'] for r in rows),
                   changing_mixed_choices=sum(r['pairs_whose_mixed_choice_changes'] for r in rows))
    result = dict(seed=81020264, summary=summary, instances=rows)
    Path(__file__).with_name('near_twin_pair_checks.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
