#!/usr/bin/env python3
"""Early enumeration on complete formulas whose clause parities are biased.

Complete formula on n variables, one clause per pair: with probability (1+eps)/2 the clause has
equal polarities, (u v v) or (-u v -v); otherwise opposite polarities, (u v -v) or (-u v v).
Boolean form F(x) = c0 + h.x + sum_{u<v} J_uv x_u x_v with J_uv = -1 (equal) or +1 (opposite),
so J = -eps (11^T - I) + N with N of mean zero.

Early enumeration (EE): branch on x_1..x_T in this order, learn in every non-preferred child the
constraint g_t(x) < 0, where g_t is the gain of flipping x_t back to its preferred value; then
enumerate the completions of the summed constraint.  The work is 2^n * Pr_sigma[sigma passes].

Count-guessing (CG): for each k, run EE on F'_k(x) = c0 + (h - eps k).x + sum N_uv x_u x_v,
learning g'_t(x) < eps.  In the run with k = |x*| every learned constraint holds at the optimum
x*, so the best assignment found over all runs is optimal.  Run k only needs to enumerate the
completions with |x| = k, so every assignment is tested once, in the run of its own count.

  python3 explore_parity_bias.py
"""
import math
import sys
import numpy as np


def formula(n, eps, rng):
    J = np.zeros((n, n))
    h = np.zeros(n)
    c0 = 0.0
    iu = np.triu_indices(n, 1)
    equal = rng.random(len(iu[0])) < (1 + eps) / 2
    sign = rng.random(len(iu[0])) < 0.5
    for (u, v, e, s) in zip(iu[0], iu[1], equal, sign):
        if e:
            if s:            # (u v v) = x_u + x_v - x_u x_v
                h[u] += 1; h[v] += 1; J[u, v] -= 1
            else:            # (-u v -v) = 1 - x_u x_v
                c0 += 1; J[u, v] -= 1
        else:
            if s:            # (u v -v) = 1 - x_v + x_u x_v
                c0 += 1; h[v] -= 1; J[u, v] += 1
            else:            # (-u v v) = 1 - x_u + x_u x_v
                c0 += 1; h[u] -= 1; J[u, v] += 1
    J = J + J.T
    return c0, h, J


def pass_rate(h, J, T, slack, X, strict_int, shift=None):
    """X: samples x n matrix of 0/1 assignments.  For each sample run the uncut EE process through
    T steps; return the fraction passing the summed constraint sum_{t in I} g_t(x) < slack*|I|
    (for integer data, sum g_t <= -|I|).  shift (one value per sample) is subtracted from every
    field: the count-guessing run that belongs to the sample's own count."""
    S, n = X.shape
    if shift is None:
        shift = np.zeros(S)
    total = np.zeros(S)
    count = np.zeros(S)
    for t in range(T):
        prefix = X[:, :t] @ J[t, :t]
        free = 0.5 * J[t, t + 1:].sum()
        delta = h[t] - shift + prefix + free
        pref = (delta >= 0).astype(float)
        creator = X[:, t] != pref
        m = h[t] - shift + X @ J[t] - X[:, t] * J[t, t]
        gain = np.where(pref == 1, m, -m)
        total += np.where(creator, gain, 0.0)
        count += creator
    if strict_int:
        ok = total <= -count
    else:
        ok = total < slack * count
    return ok.mean()


def main():
    rng = np.random.default_rng(1)
    samples = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
    print("fraction of all 2^n assignments enumerated by early enumeration at T = n/2")
    print(f"{'n':>4} {'eps':>5} {'plain EE':>9} {'count guessing':>15}")
    for n in (60, 120, 240):
        for eps in (0.0, 0.1, 0.2, 0.4, 1.0):
            c0, h, J = formula(n, eps, rng)
            T = n // 2
            X = (rng.random((samples, n)) < 0.5).astype(float)
            plain = pass_rate(h, J, T, 0.0, X, True)
            N = J + eps * (np.ones((n, n)) - np.eye(n))
            k = X.sum(axis=1)
            guessed = pass_rate(h, N, T, eps, X, eps == 0, shift=eps * k)
            print(f"{n:4d} {eps:5.2f} {plain:9.4f} {guessed:15.4f}", flush=True)


if __name__ == "__main__":
    main()
