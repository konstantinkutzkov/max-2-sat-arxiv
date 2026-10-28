#!/usr/bin/env python3
"""Checks for max2sat_explicit_class.tex.

Canonical formulas: unit clauses (with multiplicity), and on each pair of
variables either nothing, one binary clause, or a complementary pair
(x v y),(-x v -y) or (x v -y),(-x v y).  The search: fixed order x_1..x_n,
pruning clauses <L <= p-1> on the non-preferred side (complementary pairs give
multiplicity 2), cut when a clause is violated or when the sum check over the
live non-vacuous clauses fires.

  python3 explore_explicit_class.py identities   race identity with multiplicities, the
                                                  representation by J and h, and
                                                  "survival implies Z_t <= 0"
  python3 explore_explicit_class.py params        ||J||, ||L||, sum h^2 on random and aligned formulas
  python3 explore_explicit_class.py constant      the constant of the theorem
"""
import math
import random
import sys


def lit_true(val, s):
    return val == (1 if s == 1 else 0)


def random_canonical(n, d, q, units, rng):
    """Each pair: a binary interaction with probability d/(n-1); it is a complementary pair
    with probability q (random type), otherwise one clause with random signs.  Each variable
    gets Poisson-like 0..units unit clauses with random signs."""
    p = d / (n - 1)
    binary, unit = [], []
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                if rng.random() < q:
                    if rng.random() < 0.5:
                        binary += [(i, 1, j, 1), (i, -1, j, -1)]
                    else:
                        binary += [(i, 1, j, -1), (i, -1, j, 1)]
                else:
                    binary.append((i, rng.choice((1, -1)), j, rng.choice((1, -1))))
        for _ in range(rng.randint(0, units)):
            unit.append((i, rng.choice((1, -1))))
    return n, binary, unit


def circulant(n, c):
    binary = []
    for i in range(n):
        for j in range(i + 1, n):
            s = 1 if min(j - i, n - j + i) <= c else -1
            binary.append((i, s, j, s))
    return n, binary, []


def maxcut(m):
    binary = []
    for i in range(m):
        for j in range(i + 1, m):
            binary += [(i, 1, j, 1), (i, -1, j, -1)]
    return m, binary, []


def J_and_h(F):
    n, binary, unit = F
    J = [[0] * n for _ in range(n)]
    h = [0] * n
    for (u, su, v, sv) in binary:
        J[u][v] += su * sv
        J[v][u] += su * sv
        h[u] += su
        h[v] += sv
    for (v, s) in unit:
        h[v] += 2 * s
    return J, h


def simulate(F, sigma):
    """Runs sigma through the search.  Returns the number of checks of each identity
    and asserts them; also asserts that every surviving prefix has Z <= 0."""
    n, binary, unit = F
    J, h = J_and_h(F)
    a = [2 * s - 1 for s in sigma]
    inc = [[] for _ in range(n)]                 # binary clauses at each variable: (other, s_self, s_other)
    for (u, su, v, sv) in binary:
        inc[u].append((v, su, sv))
        inc[v].append((u, sv, su))
    P = [[0, 0] for _ in range(n)]
    for x in range(n):
        for (v, sx, sv) in inc[x]:
            P[x][1 if sx == 1 else 0] += 1
    for (v, s) in unit:
        P[v][1 if s == 1 else 0] += 1
        P[v][0 if s == 1 else 1] -= 1
    # all created clauses (uncut process)
    occ = [[] for _ in range(n)]                 # clause dicts containing w: c = [sup, k0, j]
    m = [[0, 0] for _ in range(n)]
    S2 = Q2 = U2 = 0
    tmin = tslack = 0
    # the actual search
    alive = True
    locc = [[] for _ in range(n)]
    lm = [[0, 0] for _ in range(n)]
    lmin = lslack = 0
    C = []
    checks = 0
    for t in range(n):
        x = t
        delta = P[x][1] - P[x][0]
        assert delta == h[x] - sum(J[x][u] * a[u] for u in range(x)), "gap formula"
        bx = m[x][1] - m[x][0]
        assert bx == sum(J[s][x] * a[s] for s in C), "bad-value balance formula"
        checks += 2
        pos = P[x][0] <= P[x][1]
        val = sigma[x]
        if (val == 1) != pos:                                   # non-preferred: create P_x
            C.append(x)
            lsign = 1 if pos else -1
            sup = {}
            for (v, sx, sv) in inc[x]:
                if v > x:
                    bad = (0 if sv == 1 else 1) if sx == lsign else (1 if sv == 1 else 0)
                    if v in sup:
                        assert sup[v][0] == bad, "complementary pair with two bad values"
                        sup[v][1] += 1
                    else:
                        sup[v] = [bad, 1]
            k = P[x][0 if pos else 1] - 1
            assert sum(mu for (_, mu) in sup.values()) == P[x][0] + P[x][1], "support size"
            S2 += abs(delta) + 2
            c = [sup, k, 0]
            tslack += k
            for w, (bad, mu) in sup.items():
                occ[w].append(c)
                o, ob = min(m[w]), abs(m[w][1] - m[w][0])
                m[w][bad] += mu
                tmin += min(m[w]) - o
                U2 += abs(m[w][1] - m[w][0]) - ob
            if alive:
                if k < 0:
                    alive = False
                else:
                    r = sum(mu for (_, mu) in sup.values())
                    if k < r:
                        lc = [sup, k, r, True]
                        lslack += k
                        for w, (bad, mu) in sup.items():
                            locc[w].append(lc)
                            o = min(lm[w]); lm[w][bad] += mu; lmin += min(lm[w]) - o
        # assign x
        U2 -= abs(m[x][1] - m[x][0])
        tmin -= min(m[x])
        for c in occ[x]:
            bad, mu = c[0][x]
            if val == bad:
                c[2] += mu
                tslack -= mu
                Q2 += mu
            else:
                Q2 -= mu
        for (v, sx, sv) in inc[x]:
            if v > x:
                if not lit_true(val, sx):
                    P[v][0 if sv == 1 else 1] -= 1
                else:
                    P[v][1 if sv == 1 else 0] -= 1
        if alive:
            lmin -= min(lm[x])
            for lc in locc[x]:
                if not lc[3]:
                    continue
                bad, mu = lc[0][x]
                lc[2] -= mu
                if val == bad:
                    lc[1] -= mu
                    lslack -= mu
                    if lc[1] < 0:
                        alive = False
                if lc[2] <= lc[1]:
                    lc[3] = False
                    lslack -= lc[1]
                    for w, (b, mu2) in lc[0].items():
                        if w > x:
                            o = min(lm[w]); lm[w][b] -= mu2; lmin += min(lm[w]) - o
            if lmin > lslack:
                alive = False
        Z2 = S2 + Q2 - U2
        assert 2 * (tmin - tslack) == Z2, "race identity"
        Cs = set(C)
        Uf = sum(abs(sum(J[s][w] * a[s] for s in Cs if s <= x)) for w in range(x + 1, n))
        assert Uf == U2, "uncertainty formula"
        checks += 2
        if alive:
            assert Z2 <= 0, "a surviving prefix with Z > 0"
            checks += 1
    return checks


def identities():
    rng = random.Random(4)
    total = 0
    for trial in range(400):
        n = rng.randint(6, 40)
        F = random_canonical(n, rng.uniform(2, n - 1), rng.choice((0.0, 0.3, 1.0)), rng.choice((0, 1, 3)), rng)
        for _ in range(3):
            total += simulate(F, [rng.randrange(2) for _ in range(n)])
    for F in (circulant(21, 6), circulant(31, 9), maxcut(12), maxcut(16)):
        for _ in range(20):
            total += simulate(F, [rng.randrange(2) for _ in range(F[0])])
    print(f"{total} checks passed: gap formula, bad-value formula, race identity with multiplicities,"
          f" uncertainty formula, and Z <= 0 on every surviving prefix")


def params():
    import numpy as np
    rng = random.Random(3)

    def report(name, F):
        J, h = J_and_h(F)
        J = np.array(J, dtype=float)
        n = len(h)
        d = float((J ** 2).sum()) / n
        nJ = np.linalg.norm(J, 2)
        nL = np.linalg.norm(np.tril(J, -1), 2)
        h2 = float(np.dot(h, h))
        print(f"{name:34s} d={d:7.1f}  ||J||={nJ / math.sqrt(d):5.2f} sqrt d  ||L||={nL / math.sqrt(d):5.2f} sqrt d"
              f"  sum h^2={h2 / (n * d):5.2f} nd")

    for (n, d) in ((1000, 30), (1000, 100), (1000, 300), (1000, 999)):
        report(f"random, n={n}, d={d}", random_canonical(n, d, 0.0, 0, rng))
    report("random with pairs+units, n=1000", random_canonical(1000, 100, 0.3, 2, rng))
    report("circulant C_(401,100)", circulant(401, 100))
    report("Max-Cut on K_400", maxcut(400))


def constant():
    for K in (1, 2, 3, 4):
        delta = 1 / (128 * K ** 4)
        first = (0.5 - delta * K ** 2) / (4 * math.sqrt(2) * K)
        second = 0.5 * K * math.sqrt(delta * (1 - delta))
        A = first - second
        c = A ** 2 / (256 * K ** 2)
        eps = min(delta, c / math.log(2))
        print(f"K={K}: delta={delta:.2e}, margin A={A:.4f} (units n sqrt d), rate c={c:.2e},"
              f" saving eps={eps:.2e}  (eps*K^4 = {eps * K ** 4:.2e})")


if __name__ == "__main__":
    {"identities": identities, "params": params, "constant": constant}[sys.argv[1]]()
