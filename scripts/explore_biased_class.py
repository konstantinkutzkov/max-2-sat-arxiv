#!/usr/bin/env python3
"""Tree size of the fixed-order search (pruning clauses + sum check, no
domination) on BIASED formulas: every variable v has |Delta_v| >= eps*D_v.
Reuses the search and the population-splitting estimator of explore_key_lemma.py.
  python3 explore_biased_class.py             (tables; minutes)
  python3 explore_biased_class.py terms       (race terms S_T, U_T at depth T)
"""
import math, random, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0] or '.')
from explore_key_lemma import log2_tree, lit_true, root, step

def biased_formula(n, d, eps, rng, aligned=False):
    """Each pair carries a clause w.p. d/(n-1).  Variable v gets a preferred sign
    s_v; its literal in each clause is s_v with probability (1+eps')/2 (eps'
    chosen so that the realised gap is >= eps*D_v; resample until true).
    aligned=True: every clause is (u v v) or (~u v ~v) up to the per-variable
    renaming (the aligned type of C_{n,c}), with the same bias."""
    p = d / (n - 1)
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n) if rng.random() < p]
    pref = [rng.choice((1, -1)) for _ in range(n)]
    for attempt in range(200):
        q = (1 + min(1.0, eps + 0.15 + 0.03 * attempt)) / 2
        adj = [[] for _ in range(n)]
        gap = [0] * n
        for (i, j) in pairs:
            if aligned:
                # pick the clause type: both literals 'with preference' (prob q)
                # or both 'against' (prob 1-q), so that J = +1 after renaming
                t = 1 if rng.random() < q else -1
                si, sj = t * pref[i], t * pref[j]
            else:
                si = pref[i] if rng.random() < q else -pref[i]
                sj = pref[j] if rng.random() < q else -pref[j]
            adj[i].append((j, si, sj)); adj[j].append((i, sj, si))
            gap[i] += si; gap[j] += sj
        ok = all(abs(gap[v]) >= eps * len(adj[v]) for v in range(n))
        if ok:
            return adj
    return adj   # (not in the class; reported)

def in_class(adj, eps):
    worst = 1.0
    for v in range(len(adj)):
        D = len(adj[v])
        if D == 0: continue
        g = abs(sum(s for (_, s, _) in adj[v]))
        worst = min(worst, g / D)
    return worst >= eps - 1e-12, worst

def race_terms(adj, T, rng, trials=20):
    """Average of S_T, U_T, Q_T (uncut process) over uniform sigma, units of n*dbar."""
    n = len(adj); dbar = sum(len(a) for a in adj) / n
    out = [0.0, 0.0, 0.0]
    for _ in range(trials):
        P = [[0, 0] for _ in range(n)]
        for x in range(n):
            for (v, sx, sv) in adj[x]:
                P[x][0 if sx == -1 else 1] += 1
        clauses = []
        for t in range(T):
            x, val = t, rng.randrange(2)
            pos = P[x][0] <= P[x][1]
            if (val == 1) != pos:
                lsign = 1 if pos else -1
                sup = {v: ((0 if sv == 1 else 1) if sx == lsign else (1 if sv == 1 else 0))
                       for (v, sx, sv) in adj[x] if v > x}
                p_c = P[x][0 if pos else 1]
                clauses.append(dict(sup=sup, absDelta=len(sup) - 2 * p_c, a=0, j=0))
            for (v, sx, sv) in adj[x]:
                if v > x:
                    if not lit_true(val, sx): P[v][0 if sv == 1 else 1] -= 1
                    else: P[v][1 if sv == 1 else 0] -= 1
            for c in clauses:
                if x in c['sup']:
                    c['a'] += 1; c['j'] += (val == c['sup'][x])
        S = sum(c['absDelta'] / 2 + 1 for c in clauses)
        Q = sum(c['j'] - c['a'] / 2 for c in clauses)
        m = {w: [0, 0] for w in range(T, n)}
        for c in clauses:
            for w, b in c['sup'].items():
                if w >= T: m[w][b] += 1
        U = sum(abs(m[w][1] - m[w][0]) for w in m) / 2
        out[0] += S; out[1] += U; out[2] += Q
    return [o / trials / (n * dbar) for o in out]

def main():
    rng = random.Random(7)
    if len(sys.argv) > 1 and sys.argv[1] == 'terms':
        n = 1000
        for eps in (0.25, 0.5):
            for d in (6, 30, 200, (n - 1) / 2):
                adj = biased_formula(n, d, eps, rng)
                ok, worst = in_class(adj, eps)
                for tau in (0.8, 0.9):
                    S, U, Q = race_terms(adj, int(tau * n), rng, 8)
                    print(f"eps={eps} d={d:6.1f} in class={ok} (min ratio {worst:.2f}) "
                          f"T={tau}n: S={S:.3f} U={U:.3f} Q={Q:+.3f}  (units n*dbar)", flush=True)
        return
    n, M = (int(sys.argv[1]) if len(sys.argv) > 1 else 300), 40
    for aligned in (False, True):
        for eps in (0.25, 0.5):
            for d in (6, 12, 32, 128, (n - 1) / 2):
                adj = biased_formula(n, d, eps, rng, aligned)
                ok, worst = in_class(adj, eps)
                sav_single = n - log2_tree(adj, False, M, rng)
                sav_sum = n - log2_tree(adj, True, M, rng)
                print(f"{'aligned' if aligned else 'random '} eps={eps} n={n} d={d:6.1f} "
                      f"in class={ok} (min ratio {worst:.2f}): saving single {sav_single/n:.3f} n,"
                      f" with sum check {sav_sum/n:.3f} n", flush=True)

if __name__ == '__main__':
    main()
