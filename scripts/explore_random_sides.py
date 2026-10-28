#!/usr/bin/env python3
"""Early enumeration where each branching node puts its strict constraint on a random side:
on the non-preferred side with probability q, on the preferred side otherwise (q = 1 is plain EE).
Sound for every coin outcome (each node has exactly one strict side).  Reports the fraction of all
assignments that pass the summed constraint at T = n/2 (over uniform x and the coins); what matters
is the trend in n: exponential decay (base below 2) or a constant floor (no saving).

  python3 explore_random_sides.py           both tables below
  python3 explore_random_sides.py biased    complete formulas, parity bias 0.9, q = 1, 0.9, 0.75
  python3 explore_random_sides.py random    complete formulas, no bias,         q = 0.75, 0.6, 0.5
"""
import sys

import numpy as np

sys.path.insert(0, "/Users/konstantin.kutzkov/Desktop/max-2-sat")
from explore_parity_bias import formula  # noqa: E402


def pass_counts(h, J, T, X, qs, rng):
    """number of samples (rows of X) that pass the summed constraint, for each q"""
    S, n = X.shape
    M = X @ J                                   # M[:, t] = sum_w J_tw x_w
    P = X @ np.tril(J, -1).T                    # P[:, t] = sum_{j<t} J_tj x_j
    free = np.array([0.5 * J[t, t + 1:].sum() for t in range(n)])
    out = []
    for q in qs:
        total = np.zeros(S)
        count = np.zeros(S)
        for t in range(T):
            pref = h[t] + P[:, t] + free[t] >= 0
            c = np.where(rng.random(S) < q, ~pref, pref).astype(float)   # constrained value
            active = X[:, t] == c
            m = h[t] + M[:, t]                  # gain of x_t: 0 -> 1
            gain = np.where(c == 0, m, -m)      # gain of flipping away from c
            total += np.where(active, gain, 0.0)
            count += active
        out.append(int((total <= -count).sum()))
    return out


def trend(eps, qs, sizes, seed):
    rng = np.random.default_rng(seed)
    print(f"parity bias {eps}: fraction passing at T = n/2 (passing samples in brackets)")
    for n, batches in sizes:
        c0, h, J = formula(n, eps, rng)
        cnt = np.zeros(len(qs), dtype=int)
        tot = 0
        for _ in range(batches):
            X = (rng.random((5000, n)) < 0.5).astype(float)
            cnt += pass_counts(h, J, n // 2, X, qs, rng)
            tot += 5000
        print(f"  n={n:5d} ({tot} samples)  " +
              "  ".join(f"q={q}: {c / tot:.2e} ({c})" for q, c in zip(qs, cnt)), flush=True)


def biased():
    trend(0.9, (1.0, 0.9, 0.75), ((480, 60), (960, 60), (1920, 40)), 17)


def random_():
    trend(0.0, (0.75, 0.6, 0.5), ((120, 40), (240, 40), (480, 40), (960, 20)), 17)


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "both"
    if mode in ("biased", "both"):
        biased()
    if mode in ("random", "both"):
        random_()
