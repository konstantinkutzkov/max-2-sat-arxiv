#!/usr/bin/env python3
"""Checks for the proof of the Key Lemma (max2sat_key_lemma_proof.tex).

Setting of the plan note: canonical B = 1 formula, fixed order x_1..x_n, no
domination; branching on x_t gives the non-preferred child the pruning clause
<L_t <= p-1> over the free neighbours of x_t; a node is cut when a clause is
violated (p = 0 included) or when the sum check over the live non-vacuous
clauses fires.  The "uncut process" runs a uniformly random sigma through all
steps and keeps every created clause.

  python3 explore_key_lemma_proof.py inclusion   survival to depth t implies Z_t <= 0 for the
                                                 uncut process, and Lemma 2 holds exactly
  python3 explore_key_lemma_proof.py terms       S_T, Q_T, U_T against the bounds of Theorem 1
  python3 explore_key_lemma_proof.py constant    the constants of Corollaries 6 and 7
"""
import math
import random
import statistics
import sys


def formula(n, d, rng):
    p = d / (n - 1)
    adj = [[] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                si, sj = rng.choice((1, -1)), rng.choice((1, -1))
                adj[i].append((j, si, sj))
                adj[j].append((i, sj, si))
    return adj


def lit_true(val, s):
    return val == (1 if s == 1 else 0)


def run(adj, sigma, T, actual=False):
    """Uncut process up to depth T.  All half-integers are doubled.
    Returns per-step records and, if actual, the list of (alive, Z2) after each step."""
    n = len(adj)
    P = [[0, 0] for _ in range(n)]
    for x in range(n):
        for (v, sx, sv) in adj[x]:
            P[x][0 if sx == -1 else 1] += 1
    occ = [[] for _ in range(n)]          # all created clauses containing w: [sup, k0, j, a]
    m = [[0, 0] for _ in range(n)]
    S2 = Q2 = U2 = 0
    tmin = tslack = 0                     # all clauses: sum_w free min(m0,m1), sum_c k_c
    # actual search
    alive = True
    locc = [[] for _ in range(n)]         # live clauses: [sup, k, r, live]
    lm = [[0, 0] for _ in range(n)]
    lmin = lslack = 0
    rec, trace = [], []
    for t in range(T):
        x = t
        D = sum(1 for (v, sx, sv) in adj[x] if v > x)
        k_back = sum(1 for (v, sx, sv) in adj[x] if v < x)
        r = sum(1 for (v, sx, sv) in adj[x] if v < x and not lit_true(sigma[v], sv))
        delta = P[x][1] - P[x][0]
        pos = P[x][0] <= P[x][1]
        val = sigma[x]
        create = (val == 1) != pos
        bx = m[x][1] - m[x][0]
        rec.append((D, k_back, r, delta, create, bx))
        # creation (the support excludes x)
        if create:
            lsign = 1 if pos else -1
            sup = {}
            for (v, sx, sv) in adj[x]:
                if v > x:
                    sup[v] = (0 if sv == 1 else 1) if sx == lsign else (1 if sv == 1 else 0)
            k = P[x][0 if pos else 1] - 1
            S2 += abs(delta) + 2
            c = [sup, k, 0, 0]
            tslack += k
            for w, bad in sup.items():
                occ[w].append(c)
                old_min, old_b = min(m[w]), abs(m[w][1] - m[w][0])
                m[w][bad] += 1
                tmin += min(m[w]) - old_min
                U2 += abs(m[w][1] - m[w][0]) - old_b
            if actual and alive:
                if k < 0:
                    alive = False
                elif k < len(sup):
                    lc = [sup, k, len(sup), True]
                    lslack += k
                    for w, bad in sup.items():
                        locc[w].append(lc)
                        o = min(lm[w]); lm[w][bad] += 1; lmin += min(lm[w]) - o
        # assignment of x
        U2 -= abs(m[x][1] - m[x][0])
        tmin -= min(m[x])
        for c in occ[x]:
            bad = c[0][x]
            c[3] += 1
            if val == bad:
                c[2] += 1
                tslack -= 1
                Q2 += 1
            else:
                Q2 -= 1
        for (v, sx, sv) in adj[x]:
            if v > x:
                if not lit_true(val, sx):
                    P[v][0 if sv == 1 else 1] -= 1
                else:
                    P[v][1 if sv == 1 else 0] -= 1
        if actual and alive:
            lmin -= min(lm[x])
            for lc in locc[x]:
                if not lc[3]:
                    continue
                bad = lc[0][x]
                lc[2] -= 1
                if val == bad:
                    lc[1] -= 1; lslack -= 1
                    if lc[1] < 0:
                        alive = False
                if lc[2] <= lc[1]:
                    lc[3] = False
                    lslack -= lc[1]
                    for w, b in lc[0].items():
                        if w > x:
                            o = min(lm[w]); lm[w][b] -= 1; lmin += min(lm[w]) - o
            if lmin > lslack:
                alive = False
        Z2 = S2 + Q2 - U2
        assert 2 * (tmin - tslack) == Z2, "Lemma 2 identity fails"
        if actual:
            trace.append((alive, Z2))
    return rec, S2 / 2, Q2 / 2, U2 / 2, trace


def graph_quantities(adj, T):
    n = len(adj)
    mu = V = 0.0
    e_le = e_T = 0
    U = 0.0
    for t in range(T):
        D = sum(1 for (v, _, _) in adj[t] if v > t)
        k = sum(1 for (v, _, _) in adj[t] if v < t)
        mu += math.sqrt(D + 2 * k)
        A = D + 4 * k
        V += A / 8 + math.sqrt(A) / 2 + 0.5
        e_le += k
    for w in range(T, n):
        dw = sum(1 for (v, _, _) in adj[w] if v < T)
        U += 0.5 * math.sqrt(dw)
        e_T += dw
    return mu / (4 * math.sqrt(2)), U, V, e_le, e_T


def inclusion():
    rng = random.Random(11)
    checked = 0
    worst = -10 ** 9
    for n, d in ((60, 8), (120, 16), (200, 30), (200, 100), (400, 60)):
        adj = formula(n, d, rng)
        alive_pairs = cuts = cuts_nonpos = 0
        for _ in range(150):
            sigma = [rng.randrange(2) for _ in range(n)]
            _, _, _, _, trace = run(adj, sigma, n, actual=True)
            for (al, Z2) in trace:
                if al:
                    alive_pairs += 1
                    worst = max(worst, Z2 / 2)
                    assert Z2 <= 0, "a surviving partial assignment with Z_t > 0"
                else:                                   # the step at which sigma is cut
                    cuts += 1
                    cuts_nonpos += Z2 <= 0
                    break
        checked += alive_pairs
        print(f"n={n:3d} d={d:3d}: {alive_pairs:6d} surviving (sigma, t) pairs, all with Z_t <= 0; "
              f"of {cuts} cuts, {cuts_nonpos} happen while Z_t <= 0 (a single clause or p = 0)")
    print(f"total {checked} surviving pairs checked; max Z_t over them = {worst}; Lemma 2 held at every step")


def terms():
    rng = random.Random(2)
    tau = 0.9
    for n, d in ((1000, 30), (1000, 100), (2000, 200), (2000, 1000), (1500, 1499)):
        adj = formula(n, d, rng)
        T = int(tau * n)
        muG, UG, V, e_le, e_T = graph_quantities(adj, T)
        norm = n * math.sqrt(d)
        rows = []
        ratios = []
        for _ in range(4):
            sigma = [rng.randrange(2) for _ in range(n)]
            rec, S, Q, U, _ = run(adj, sigma, T)
            mu_sum = sum(math.sqrt(D + 4 * r) / (4 * math.sqrt(2)) + 0.5 for (D, k, r, *_r) in rec)
            for (D, k, r, delta, create, bx) in rec:
                if D + 4 * r > 0:
                    ratios.append(abs(delta) / math.sqrt((D + 4 * r) / 2))
            rows.append((S, Q, U, mu_sum))
        S = statistics.mean(r[0] for r in rows); Q = statistics.mean(r[1] for r in rows)
        U = statistics.mean(r[2] for r in rows); ms = statistics.mean(r[3] for r in rows)
        print(f"n={n} d={d}: S_T {S/norm:.3f} >= sum mu_t {ms/norm:.3f} >= mu_G {muG/norm:.3f};  "
              f"U_T {U/norm:.4f} <= U_G {UG/norm:.4f};  Q_T {Q/norm:+.4f} (scale sqrt(e_<=T)/(n sqrt d) = "
              f"{math.sqrt(e_le)/norm:.4f});  mean |Delta_t|/sqrt((D_t+4r_t)/2) = {statistics.mean(ratios):.3f}")
        print(f"      normalized: V/(nd) = {V/(n*d):.3f}, e_<=T/(nd) = {e_le/(n*d):.3f}, e_T/(nd) = {e_T/(n*d):.3f}; "
              f"margin (mu_G - U_G)/(n sqrt d) = {(muG-UG)/norm:.3f}")


def best_split(M, ks):
    """max over splits a_i >= 0, sum a_i = M, of min_i k_i a_i^2."""
    s = sum(1 / math.sqrt(k) for k in ks)
    return (M / s) ** 2


def constant():
    c4 = 1 / (4 * math.sqrt(2))
    print("Random graph G(n, d/(n-1)), d large:")
    best = (0, 0, 0)
    for i in range(1, 1000):
        tau = i / 1000
        M = c4 * (2 / 3) * ((1 + tau) ** 1.5 - 1) - 0.5 * (1 - tau) * math.sqrt(tau)
        if M <= 0:
            continue
        ks = (4 / (tau + 1.5 * tau ** 2), 32 / tau ** 2, 4 / tau ** 2, 2 / (tau * (1 - tau)))
        c = best_split(M, ks)
        g = min(1 - tau, c / math.log(2))
        if g > best[0]:
            best = (g, tau, c)
    print(f"  best tau = {best[1]:.3f}: survival to depth tau*n has probability <= 4 exp(-{best[2]:.4f} n), "
          f"gamma = {best[0]:.4f}")
    print("Every d-regular graph, any order, d large:")
    best = (0, 0, 0)
    for i in range(1, 1000):
        tau = i / 1000
        M = c4 * tau - 0.5 * (1 - tau)
        if M <= 0:
            continue
        ks = (1 / tau, 32 / tau, 4 / tau, 2 / (1 - tau))
        c = best_split(M, ks)
        g = min(1 - tau, c / math.log(2))
        if g > best[0]:
            best = (g, tau, c)
    print(f"  best tau = {best[1]:.3f}: survival probability <= 4 exp(-{best[2]:.4f} n), gamma = {best[0]:.4f}")


if __name__ == "__main__":
    {"inclusion": inclusion, "terms": terms, "constant": constant}[sys.argv[1]]()
