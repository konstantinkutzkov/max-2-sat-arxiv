#!/usr/bin/env python3
"""Measure-and-conquer weights for counted pruning clauses (class 1).

Clause state (l, k): at most k more of its l free literals may become true.
A variable with free degree D and deficit p gives (D, p - 1) in its
non-preferred branch; k = 0 means propagation, k >= l means vacuous.  Counted
clauses have disjoint supports (a new clause is counted on its new variables
only, which keeps it a valid pruning clause).

Measure  mu = free variables - sum over counted clauses of eps(l, k).
Case 1, branch on a near-dominated x outside the counted supports:
    drops (1, 1 + eps(D, k0)).
Case 2, branch on a variable of a counted clause (l, k):
    literal false -> (l-1, k)      drop 1 + V_f - eps(l, k), V_f = eps(l-1, k) or 0 if vacuous
    literal true  -> (l-1, k-1)    drop 1 + V_t - eps(l, k), V_t = eps(l-1, k-1),
                                   or V_t = l - 1 if k = 1 (the rest is forced false)
For a target lam every step needs lam^-drop_f + lam^-drop_t <= 1, so the largest
weights are computed backwards:  eps(l, k) = min(cap, 1 - log_lam(lam^-V_f + lam^-V_t)),
and a state where this is negative is released (weight 0, no step inside it).
The script finds the smallest lam for which creating (D, k0) is feasible, with
the cap eps < 1 and without a cap, and compares with 2^H(k0/D), the exponent of
the linear-gap bound.  It also checks that forced assignments (domination,
propagation) never increase mu, i.e. no single transition lowers eps by more
than 1.
"""
import math


def table(lam, L, cap):
    eps = {}
    for l in range(2, L + 1):
        for k in range(1, l):
            vf = eps[(l - 1, k)] if k <= l - 2 else 0.0
            vt = eps[(l - 1, k - 1)] if k >= 2 else float(l - 1)
            g = 1 - math.log(lam ** -vf + lam ** -vt, lam)
            eps[(l, k)] = max(0.0, min(cap, g))
    return eps


def best_lam(D, k0, cap):
    lo, hi = 1.0001, 2.0
    for _ in range(60):
        lam = (lo + hi) / 2
        need = math.log(lam / (lam - 1), lam) - 1          # case 1: lam^-1 + lam^-(1+e) <= 1
        if table(lam, D, cap)[(D, k0)] >= need:
            hi = lam
        else:
            lo = lam
    return hi


def worst_forced(lam, L, cap):
    e = table(lam, L, cap)
    worst = -math.inf
    for (l, k), v in e.items():
        if l >= 3:
            vf = e[(l - 1, k)] if k <= l - 2 else 0.0
            vt = e[(l - 1, k - 1)] if k >= 2 else float(l - 1)
            worst = max(worst, v - vf - 1, v - vt - 1)
    return worst


def H(q):
    return -q * math.log2(q) - (1 - q) * math.log2(1 - q)


def main():
    print("cap eps < 1: branching number for creating 'at most k0 of D' (it depends on k0 only)")
    for k0 in (1, 2, 3, 4, 8, 16):
        print(f"  k0 = {k0:2d}: {best_lam(4 * k0 + 4, k0, 1.0):.4f}")
    print("no cap: branching number for allowance ratio beta = k0/D, against 2^H(beta)")
    for beta in (0.125, 0.25, 0.375):
        row = []
        for D in (32, 64, 128, 256):
            lam = best_lam(D, int(beta * D), math.inf)
            assert worst_forced(lam, D, math.inf) <= 1e-9
            row.append(f"D={D}: {lam:.4f}")
        print(f"  beta = {beta}: " + "  ".join(row) + f"   limit 2^H = {2 ** H(beta):.4f}")
    lam = best_lam(16, 4, math.inf)
    e = table(lam, 16, math.inf)
    print(f"weights without cap at lam = {lam:.4f} (rows l, columns k = 1..4)")
    for l in (4, 8, 12, 16):
        print(f"  l = {l:2d}: " + "  ".join(f"{e[(l, k)]:5.2f}" if k < l and e[(l, k)] > 0 else "    -"
                                         for k in range(1, 5)))


if __name__ == "__main__":
    main()
