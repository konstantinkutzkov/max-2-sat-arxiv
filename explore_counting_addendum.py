#!/usr/bin/env python3
"""Checks for max2sat_counting_addendum.tex.

For a simple signed interaction graph in a fixed order and T = floor(tau n):
  K   = ||R||^2 / d, with R_iw = J_iw for w > i, i <= T      (condition C1)
  H   = sum_{i<=T} h_i^2 / (n d)                            (condition C2)
  g   = half the left side of (C3'), per n sqrt(d):
        sum_{i<=T} max(|h_i|, sqrt(D_i^-/3)) / (2 n sqrt(d))
  G(u) = sum_{i<=T} |h_i - sum_{j<i} J_ij u_j| over uniform prefixes u, per n sqrt(d)
The proposition says: (C1) and (C3') give Pr[G(u) < g n sqrt d] <= 4 exp(-g^2 n/(64 tau K)).
Also printed: the K needed by the row-sum certificate max_i sum_j |M_ij| <= K d.

  python3 explore_counting_addendum.py
"""
import math
import numpy as np


def quantities(J, h, T, d, rng, samples=4000):
    n = J.shape[0]
    R = np.triu(J, 1)[:T, :]
    K = np.linalg.norm(R, 2) ** 2 / d
    Krow = np.abs(R @ R.T).sum(axis=1).max() / d          # the row-sum certificate
    H = float((h[:T] ** 2).sum()) / (n * d)
    Lt = np.tril(J, -1)[:T, :T]
    Dminus = np.count_nonzero(Lt, axis=1)
    left = np.maximum(np.abs(h[:T]), np.sqrt(Dminus / 3)).sum() / (n * math.sqrt(d))
    U = rng.choice([-1, 1], size=(samples, T))
    G = np.abs(h[:T][None, :] - U @ Lt.T).sum(axis=1) / (n * math.sqrt(d))
    return K, H, left / 2, G, Krow


def random_signed(n, d, rng):
    A = np.triu(rng.random((n, n)) < d / (n - 1), 1)
    s1 = np.where(A, rng.choice([-1, 1], size=(n, n)), 0)    # sign of the smaller endpoint
    s2 = np.where(A, rng.choice([-1, 1], size=(n, n)), 0)    # sign of the larger endpoint
    J = s1 * s2
    J = J + J.T
    h = s1.sum(axis=1) + s2.sum(axis=0)
    return J, h, 2 * A.sum() / n


def hadamard(k):
    Hm = np.array([[1]])
    for _ in range(2 * k):
        Hm = np.block([[Hm, Hm], [Hm, -Hm]])
    q = Hm.shape[0]
    u = np.array([1] * ((q + int(math.isqrt(q))) // 2) + [-1] * ((q - int(math.isqrt(q))) // 2))
    n = 2 * q
    J = np.zeros((n, n), dtype=int)
    h = np.zeros(n, dtype=int)
    for i in range(q):                      # left vertices 0..q-1 come first
        for w in range(q):
            si, sw = u[w], u[w] * Hm[i, w]
            J[i, q + w] = J[q + w, i] = si * sw
            h[i] += si
            h[q + w] += sw
    return J, h, q, n


def zero_gap(q):
    Hm = np.array([[1]])
    while Hm.shape[0] < q:
        Hm = np.block([[Hm, Hm], [Hm, -Hm]])
    p = q // 16
    n = p + q
    J = np.zeros((n, n), dtype=int)
    h = np.zeros(n, dtype=int)
    for i in range(p):
        for w in range(q):
            si = 1 if w % 2 == 0 else -1     # balanced own-literal signs at each left vertex
            sw = si * Hm[i, w]
            J[i, p + w] = J[p + w, i] = si * sw
            h[i] += si
            h[p + w] += sw
    return J, h, q, n, p


def main():
    rng = np.random.default_rng(7)
    print("Random signed graphs, natural order, T = n/2:")
    print(f"{'n':>5} {'d':>6} {'K':>5} {'H':>5} {'g':>6} {'E G':>6} {'sd G':>7} {'min G':>6} {'K row-sum':>10}")
    for (n, d) in ((400, 20), (400, 80), (400, 200), (800, 100), (800, 400)):
        J, h, dd = random_signed(n, d, rng)
        T = n // 2
        K, H, g, G, Krow = quantities(J, h, T, dd, rng)
        assert G.min() >= g, "an observed prefix below the threshold"
        print(f"{n:5d} {dd:6.1f} {K:5.2f} {H:5.2f} {g:6.3f} {G.mean():6.3f} {G.std():7.4f} {G.min():6.3f} {Krow:10.2f}")
    J, h, q, n = hadamard(2)
    K, H, g, G, _ = quantities(J, h, q, q, rng)
    print(f"Hadamard example, n={n}, d={q}, left side first, T={q}: K={K:.2f}, H={H:.2f}, g={g:.3f},"
          f" G constant = {G.mean():.3f} n sqrt d")
    J, h, q, n, p = zero_gap(64)
    K, H, g, G, _ = quantities(J, h, p, q, rng)
    print(f"Zero-gap example, p={p}, q={q}, left side first, T={p}: K={K:.2f}, g={g:.3f} (condition C3' fails),"
          f" G max = {G.max():.3f}")


if __name__ == "__main__":
    main()
