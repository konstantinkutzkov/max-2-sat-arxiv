"""Finite checks of the new bounded-block and conditional-comparison lemmas.

Run with Python 3. These checks supplement, and do not prove, the theorems.
The generated integral quadratic objectives have unweighted Max 2-SAT
representations: realize signed quadratic coefficients by repeated binary
clauses and correct their linear terms by repeated unit clauses.
"""
from itertools import product
from pathlib import Path
import json
import random


def score(h, J, x):
    return sum(a * b for a, b in zip(h, x)) + sum(
        J[u][v] * x[u] * x[v]
        for u in range(len(x)) for v in range(u + 1, len(x))
    )


def build(rng, q, outside_count, perturbations):
    n = 4 * q + outside_count
    blocks = [tuple(range(4 * i, 4 * i + 4)) for i in range(q)]
    h = [rng.randrange(-4, 5) for _ in range(n)]
    J = [[0] * n for _ in range(n)]
    basis = ((1, 0, 1, 0), (0, 1, 0, 1), (1, 0, 0, 1))
    for i, Bi in enumerate(blocks):
        for j in range(i + 1, q):
            Bj = blocks[j]
            W = [[rng.randrange(-1, 2) for _ in basis] for _ in basis]
            for u, a in enumerate(Bi):
                for v, b in enumerate(Bj):
                    J[a][b] = J[b][a] = sum(
                        basis[k][u] * W[k][l] * basis[l][v]
                        for k in range(3) for l in range(3)
                    )
        for v in range(4 * q, n):
            weights = [rng.randrange(-2, 3) for _ in basis]
            for k, u in enumerate(Bi):
                J[u][v] = J[v][u] = sum(weights[t] * basis[t][k] for t in range(3))
        for k, u in enumerate(Bi):
            for v in Bi[k + 1:]:
                J[u][v] = J[v][u] = rng.randrange(-2, 3)
    for u in range(4 * q, n):
        for v in range(u + 1, n):
            J[u][v] = J[v][u] = rng.randrange(-2, 3)
    for _ in range(perturbations):
        u, v = rng.sample(range(n), 2)
        J[u][v] += rng.choice((-1, 1))
        J[v][u] = J[u][v]
    return h, J, blocks


def block_check(h, J, blocks):
    n, q = len(h), len(blocks)
    a, b = (1, 1, 0, 0), (0, 0, 1, 1)
    diff = tuple(y - x for x, y in zip(a, b))
    D = [{v for v in range(n) if v not in B and
          sum(J[u][v] * diff[k] for k, u in enumerate(B)) != 0}
         for B in blocks]
    r = max(map(len, D))
    adj = [{j for j in range(q) if i != j and
            (D[i].intersection(blocks[j]) or D[j].intersection(blocks[i]))}
           for i in range(q)]
    remaining, removed = set(range(q)), []
    while remaining:
        u = min(remaining, key=lambda v: len(adj[v] & remaining))
        assert len(adj[u] & remaining) <= 2 * r
        remaining.remove(u)
        removed.append(u)
    colors = {}
    for u in reversed(removed):
        forbidden = {colors[v] for v in adj[u] if v in colors}
        colors[u] = next(c for c in range(2 * r + 1) if c not in forbidden)
    groups = [[u for u in range(q) if colors[u] == c] for c in set(colors.values())]
    retained = max(groups, key=len)
    assert len(retained) * (2 * r + 1) >= q
    free = set().union(*(set(blocks[i]) for i in retained))
    outside = sorted(set(range(n)) - free)
    optimum = max(score(h, J, x) for x in product((0, 1), repeat=n))
    best, candidates, certified = None, 0, 0
    for y in product((0, 1), repeat=len(outside)):
        x = [0] * n
        for v, value in zip(outside, y):
            x[v] = value
        allowed = []
        for i in retained:
            B = blocks[i]
            xa, xb = x.copy(), x.copy()
            for v, va, vb in zip(B, a, b):
                xa[v], xb[v] = va, vb
            fa, fb = score(h, J, xa), score(h, J, xb)
            forbidden = a if fb >= fa else b
            allowed.append([z for z in product((0, 1), repeat=4) if z != forbidden])
            assert not (D[i] & (free - set(B)))
            certified += 1
        for states in product(*allowed):
            for i, state in zip(retained, states):
                for v, value in zip(blocks[i], state):
                    x[v] = value
            value = score(h, J, x)
            best = value if best is None else max(best, value)
            candidates += 1
    assert best == optimum
    assert candidates == 2 ** len(outside) * 15 ** len(retained)
    return dict(n=n, q=q, r=r, retained=len(retained), candidates=candidates,
                optimal=best, certificates=certified)


def conditional_checks(rng):
    checks = 0
    for _ in range(80):
        n, p = 7, 3
        h = [rng.randrange(-4, 5) for _ in range(n)]
        J = [[0] * n for _ in range(n)]
        for u in range(n):
            for v in range(u + 1, n):
                J[u][v] = J[v][u] = rng.randrange(-2, 3)
        alpha, beta = rng.sample(list(product((0, 1), repeat=p)), 2)
        region = [(rng.randrange(n-p), rng.randrange(2)) for _ in range(3)]
        ys = list(product((0, 1), repeat=n-p))
        def covered(y):
            return any(y[v] == bit for v, bit in region)
        incumbent = max(score(h, J, alpha+y) for y in ys if covered(y))
        for y in ys:
            fa, fb = score(h, J, alpha+y), score(h, J, beta+y)
            delta0 = score(h, J, alpha+(0,)*(n-p)) - score(h, J, beta+(0,)*(n-p))
            coeffs = [sum(J[u][v] * (alpha[u]-beta[u]) for u in range(p))
                      for v in range(p, n)]
            assert fa-fb == delta0 + sum(c*t for c,t in zip(coeffs,y))
            if covered(y) and fa >= fb:
                assert fb <= incumbent
            checks += 1
    return checks


def main():
    rng = random.Random(20261012)
    rows = []
    for q, outside in ((2, 0), (2, 2), (3, 0)):
        for perturbations in (0, 1, 3):
            for _ in range(4):
                rows.append(block_check(*build(rng, q, outside, perturbations)))
    result = dict(seed=20261012, block_instances=len(rows),
                  block_certificates=sum(x['certificates'] for x in rows),
                  conditional_checks=conditional_checks(rng), instances=rows)
    Path(__file__).with_name('dense_max2sat_block_checks.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'instances'}))


if __name__ == '__main__':
    main()
