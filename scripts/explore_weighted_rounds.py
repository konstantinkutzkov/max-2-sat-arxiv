#!/usr/bin/env python3
"""Exactness checks for max2sat_weighted_rounds.tex against exhaustive search.

  A   weighted early enumeration (weights deg^-1/2), random signs on a fixed graph, one clause per
      edge or each of the four clauses with probability q, random unit clauses, random order
  C   round-based enumeration with guessed projections: mean-centred counts (exact grid) and
      spectral projections (top eigenvectors of J, grid of spacing delta), two or three rounds;
      biased random formulas and Max-Cut with unit clauses on random regular graphs

For every formula the set of enumerated assignments is computed exactly (all 2^n assignments are
tested against the summed inequality of their own prefix), and the best enumerated score is
compared with the optimum.

  python3 explore_weighted_rounds.py
"""
import itertools
import sys

import numpy as np

sys.path.insert(0, "/Users/konstantin.kutzkov/Desktop/max-2-sat")
from explore_two_sided import from_clauses_units  # noqa: E402


def all_x(n):
    return np.array(list(itertools.product((0, 1), repeat=n)), dtype=float)


def scores(c0, h, J, X):
    return c0 + X @ h + 0.5 * np.einsum("ij,jk,ik->i", X, J, X)


def random_graph(n, p, rng):
    E = [(u, v) for u in range(n) for v in range(u + 1, n) if rng.random() < p]
    deg = np.zeros(n)
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    return E, deg


def clauses_on(E, model, rng):
    cl = []
    for u, v in E:
        if model == "one":
            cl.append((u, int(rng.choice((1, -1))), v, int(rng.choice((1, -1)))))
        else:                                   # each of the four clauses with probability q
            for su in (1, -1):
                for sv in (1, -1):
                    if rng.random() < model:
                        cl.append((u, su, v, sv))
    return cl


def units(n, rng, rate):
    return [(u, s, u, s) for u, s in zip(rng.integers(0, n, int(rate * n)),
                                         rng.choice((1, -1), int(rate * n)))]


def passes_A(h, J, X, T, w):
    """weighted summed constraint, strict creator constraints (integer scores)"""
    total = np.zeros(len(X))
    for t in range(T):
        delta = h[t] + X[:, :t] @ J[t, :t] + 0.5 * J[t, t + 1:].sum()
        pref = (delta >= 0).astype(float)
        creator = X[:, t] != pref
        gain = h[t] + X @ J[t] - X[:, t] * J[t, t]
        signed = np.where(pref == 1, gain, -gain)
        total += np.where(creator, w[t] * (signed + 1), 0.0)
    return total <= 1e-9


def check_A(trials, rng):
    lost = 0
    frac = []
    for trial in range(trials):
        n = int(rng.integers(6, 12))
        E, deg = random_graph(n, float(rng.choice([0.3, 0.6, 1.0])), rng)
        if (deg == 0).any():
            keep = deg > 0                       # the model has no isolated vertices
            idx = {old: new for new, old in enumerate(np.nonzero(keep)[0])}
            E = [(idx[u], idx[v]) for u, v in E]
            deg = deg[keep]
            n = int(keep.sum())
            if n < 3:
                continue
        model = "one" if trial % 2 == 0 else float(rng.choice([0.25, 0.5]))
        cl = clauses_on(E, model, rng) + units(n, rng, float(rng.choice([0.0, 0.7])))
        order = rng.permutation(n)
        inv = np.argsort(order)
        cl = [(int(inv[u]), su, int(inv[v]), sv) for u, su, v, sv in cl]
        deg = deg[order]
        c0, h, J = from_clauses_units(n, cl)
        X = all_x(n)
        F = scores(c0, h, J, X)
        ok = passes_A(h, J, X, (n + 1) // 2, 1 / np.sqrt(deg))
        lost += abs(F[ok].max() - F.max()) > 1e-9 if ok.any() else 1
        frac.append(ok.mean())
    return lost, float(np.mean(frac))


def run_C(c0, h, J, X, F, lams, vecs, grids, deltas, rounds):
    """best enumerated score over all runs of Algorithm C"""
    n = len(h)
    P = sum(l * np.outer(v, v) for l, v in zip(lams, vecs)) if lams else np.zeros((n, n))
    N = J - P
    np.fill_diagonal(N, 0.0)
    s = np.zeros(n)
    for l, v, d in zip(lams, vecs, deltas):
        s += abs(l) * np.abs(v) * (d + np.abs(v))
    rnd = np.zeros(n, dtype=int)                 # round of each variable; free = len(rounds)
    rnd[:] = len(rounds)
    for j, B in enumerate(rounds):
        rnd[B] = j
    T = sum(len(B) for B in rounds)
    best = -1e18
    passed = runs = 0
    for yhat in itertools.product(*grids) if grids else [()]:
        hh = h + sum(l * y * v for l, y, v in zip(lams, yhat, vecs)) if lams else h.copy()
        total = np.zeros(len(X))
        for t in range(T):
            earlier = rnd < rnd[t]
            later = (rnd >= rnd[t]) & (np.arange(n) != t)
            delta = hh[t] + X[:, earlier] @ N[t, earlier] + 0.5 * N[t, later].sum()
            pref = (delta >= 0).astype(float)
            creator = X[:, t] != pref
            gain = hh[t] + X @ N[t]                # N has zero diagonal
            signed = np.where(pref == 1, gain, -gain)
            total += np.where(creator, signed - s[t], 0.0)
        ok = total <= 1e-9
        passed += ok.sum()
        runs += 1
        if ok.any():
            best = max(best, F[ok].max())
    return best, passed / (runs * len(X))


def check_C(trials, rng):
    lost = {"counts": 0, "spectral": 0}
    frac = {"counts": [], "spectral": []}
    for trial in range(trials):
        n = int(rng.integers(6, 11))
        if trial % 2 == 0:                       # biased random formula, one clause per pair
            eps = float(rng.choice([0.0, 0.6, 1.0]))
            cl = []
            for u in range(n):
                for v in range(u + 1, n):
                    if rng.random() < 0.8:
                        su = int(rng.choice((1, -1)))
                        sv = su if rng.random() < (1 + eps) / 2 else -su
                        cl.append((u, su, v, sv))
        else:                                    # Max-Cut constraints on a random graph
            E, _ = random_graph(n, 0.5, rng)
            cl = [c for u, v in E for c in ((u, 1, v, 1), (u, -1, v, -1))]
        cl += units(n, rng, float(rng.choice([0.0, 1.0])))
        c0, h, J = from_clauses_units(n, cl)
        X = all_x(n)
        F = scores(c0, h, J, X)
        opt = F.max()
        T = n // 2 + 1
        cut = sorted(rng.choice(np.arange(1, T), size=int(rng.integers(1, 3)), replace=False))
        rounds = [list(r) for r in np.split(np.arange(T), cut)]
        beta = J[np.triu_indices(n, 1)].mean()
        best, fr = run_C(c0, h, J, X, F, [beta], [np.ones(n)], [range(n + 1)], [0.0], rounds)
        lost["counts"] += abs(best - opt) > 1e-9
        frac["counts"].append(fr)
        w, V = np.linalg.eigh(J)
        k = np.argsort(-np.abs(w))[: int(rng.integers(1, 3))]
        delta = float(rng.choice([0.3, 0.8]))
        grids, lams, vecs = [], [], []
        for i in k:
            v = V[:, i]
            a = np.abs(v).sum() + delta
            grids.append(np.arange(-a, a + delta, delta))
            lams.append(w[i])
            vecs.append(v)
        best, fr = run_C(c0, h, J, X, F, lams, vecs, grids, [delta / 2] * len(k), rounds)
        lost["spectral"] += abs(best - opt) > 1e-9
        frac["spectral"].append(fr)
    return lost, {k: float(np.mean(v)) for k, v in frac.items()}


def main():
    rng = np.random.default_rng(12)
    a, fa = check_A(200, rng)
    print(f"Algorithm A (weighted): optimum lost in {a} of 200 formulas; "
          f"mean fraction of assignments enumerated {fa:.3f}")
    c, fc = check_C(120, rng)
    print(f"Algorithm C (rounds): optimum lost with exact counts in {c['counts']} of 120 "
          f"(mean fraction enumerated per run {fc['counts']:.3f}), with spectral grids in "
          f"{c['spectral']} of 120 (mean fraction per run {fc['spectral']:.3f})")


if __name__ == "__main__":
    main()
