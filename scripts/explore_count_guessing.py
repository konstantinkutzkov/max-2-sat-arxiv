#!/usr/bin/env python3
"""Count guessing: aligned blocks plus a pseudo-random residual.

Boolean form F(x) = c0 + h.x + sum_{u<v} J_uv x_u x_v.  Write J = sum_k beta_k s_k s_k^T (off the
diagonal) + N with s_k in {-1,0,1}^n.  For every vector c of values of <s_k, x>, run early
enumeration on F'_c(x) = c0 + (h + sum_k beta_k c_k s_k).x + sum N_uv x_u x_v: branch through depth T
in a fixed order, learn in each non-preferred child the constraint "flipping back gains less than
sigma = sum_k |beta_k|", then enumerate the completions x with <s_k, x> = c_k that satisfy the
summed constraint.  The best assignment found is optimal (checked here against exhaustive search).

  python3 explore_count_guessing.py exact      small instances: optimum found, work counted
  python3 explore_count_guessing.py scaling    pass rates of plain EE and count guessing
  python3 explore_count_guessing.py membership constants K, g and the (R3) margin of random parity-biased
                                               formulas under the mean-centred decomposition
"""
import itertools
import math
import sys
import numpy as np


# ------------------------------------------------------------------ instances
def from_clauses(n, clauses):
    J = np.zeros((n, n)); h = np.zeros(n); c0 = 0.0
    for (u, su, v, sv) in clauses:
        # clause (l_u v l_v) = 1 - [l_u false][l_v false]; [l false] = x or 1-x
        # [l_u false] = a_u + b_u x_u with (a,b) = (1,-1) if positive literal, (0,1) if negative
        au, bu = (1.0, -1.0) if su == 1 else (0.0, 1.0)
        av, bv = (1.0, -1.0) if sv == 1 else (0.0, 1.0)
        c0 += 1 - au * av
        h[u] -= au * 0 + bu * av
        h[v] -= av * 0 + bv * au
        J[u, v] -= bu * bv
    return c0, h, J + J.T


def parity_biased(n, eps, rng):
    cl = []
    for u in range(n):
        for v in range(u + 1, n):
            s = rng.choice((1, -1))
            if rng.random() < (1 + eps) / 2:
                cl.append((u, s, v, s))          # equal polarities
            else:
                cl.append((u, s, v, -s))         # opposite polarities
    return cl


def planted(n, beta, rng):
    """each pair: equal polarities with prob (1 + beta s_u s_v)/2, else opposite"""
    s = rng.choice((1, -1), size=n)
    cl = []
    for u in range(n):
        for v in range(u + 1, n):
            sg = rng.choice((1, -1))
            if rng.random() < (1 + beta * s[u] * s[v]) / 2:
                cl.append((u, sg, v, sg))
            else:
                cl.append((u, sg, v, -sg))
    return cl, s


def score(c0, h, J, x):
    return c0 + h @ x + 0.5 * x @ J @ x


# ------------------------------------------------------------------ the algorithm
def ee_run(h, N, T, slack, slice_ok, n):
    """all prefixes of length T; returns (best value of F' is not used) the list of candidates:
    completions passing the summed constraint and lying in the slice"""
    cands = []
    for prefix in itertools.product((0, 1), repeat=T):
        x = np.zeros(n)
        x[:T] = prefix
        creators = []
        for t in range(T):
            delta = h[t] + N[t, :t] @ x[:t] + 0.5 * N[t, t + 1:].sum()
            pref = 1 if delta >= 0 else 0
            if prefix[t] != pref:
                creators.append((t, pref))
        for suffix in itertools.product((0, 1), repeat=n - T):
            x[T:] = suffix
            if not slice_ok(x):
                continue
            tot = 0.0
            for (t, pref) in creators:
                m = h[t] + N[t] @ x - x[t] * N[t, t]
                tot += m if pref == 1 else -m
            if tot <= slack * len(creators) + 1e-9:
                cands.append(x.copy())
    return cands


def count_guessing(c0, h, J, S, beta, T):
    """S: list of vectors s_k; beta: list of reals.  Returns (best value, work)."""
    n = len(h)
    A = sum(b * np.outer(s, s) for s, b in zip(S, beta)) if S else np.zeros((n, n))
    np.fill_diagonal(A, 0)
    N = J - A
    slack = sum(abs(b) for b in beta)
    values = [range(int(-np.abs(s).sum()), int(np.abs(s).sum()) + 1) for s in S]
    best, work = -1e18, 0
    for c in itertools.product(*values) if S else [()]:
        hc = h + sum(b * ck * s for s, b, ck in zip(S, beta, c)) if S else h
        ok = (lambda x, c=c: all(abs(s @ x - ck) < 1e-9 for s, ck in zip(S, c)))
        for x in ee_run(hc, N, T, slack, ok, n):
            work += 1
            best = max(best, score(c0, h, J, x))
    return best, work


def exact():
    rng = np.random.default_rng(11)
    trials = fails = 0
    tot_work = tot_all = 0
    for trial in range(60):
        n = int(rng.integers(6, 12))
        kind = trial % 3
        if kind == 0:
            eps = float(rng.choice([0.3, 0.6, 1.0]))
            cl = parity_biased(n, eps, rng)
            c0, h, J = from_clauses(n, cl)
            S, beta = [np.ones(n)], [-eps]
        elif kind == 1:
            b = float(rng.choice([0.5, 0.9]))
            cl, s = planted(n, b, rng)
            c0, h, J = from_clauses(n, cl)
            S, beta = [s.astype(float)], [-b]
        else:
            cl = parity_biased(n, 0.0, rng)
            c0, h, J = from_clauses(n, cl)
            g = np.array([1.0 if rng.random() < 0.5 else 0.0 for _ in range(n)])
            S, beta = [g, 1 - g], [-0.4, 0.3]
        opt = max(score(c0, h, J, np.array(v, dtype=float)) for v in itertools.product((0, 1), repeat=n))
        T = n // 2
        best, work = count_guessing(c0, h, J, S, beta, T)
        trials += 1
        fails += abs(best - opt) > 1e-9
        tot_work += work
        tot_all += 2 ** n
    print(f"{trials} instances (parity-biased, planted bisection, two groups), n = 6..11:"
          f" optimum missed {fails} times; candidates enumerated {tot_work} of {tot_all} assignments")


def scaling():
    sys.path.insert(0, "/Users/konstantin.kutzkov/Desktop/max-2-sat")
    from explore_parity_bias import pass_rate
    rng = np.random.default_rng(3)
    print("fraction of assignments enumerated, T = n/2 (plain EE / count guessing)")
    for kind in ("parity eps=0.9", "parity eps=1.0", "planted beta=0.6", "planted beta=0.9"):
        for n in (60, 120, 240, 480):
            samples = 16000 if n <= 240 else 6000
            if kind.startswith("parity"):
                eps = float(kind.split("=")[1])
                c0, h, J = from_clauses(n, parity_biased(n, eps, rng))
                s, beta = np.ones(n), -eps
            else:
                b = float(kind.split("=")[1])
                cl, s = planted(n, b, rng)
                c0, h, J = from_clauses(n, cl)
                s, beta = s.astype(float), -b
            A = beta * np.outer(s, s); np.fill_diagonal(A, 0)
            N = J - A
            T = n // 2
            hp = hg = 0.0
            done = 0
            while done < samples:
                bsz = min(2000, samples - done)
                X = (rng.random((bsz, n)) < 0.5).astype(float)
                hp += pass_rate(h, J, T, 0.0, X, True) * bsz
                # run of the sample's own value c = <s, x>: fields h + beta c s
                c = X @ s
                hg += pass_rate_vec(h, N, T, abs(beta), X, beta, s, c) * bsz
                done += bsz
            print(f"  {kind:17s} n={n:4d}: plain {hp / samples:.5f}   count guessing {hg / samples:.5f}",
                  flush=True)


def pass_rate_vec(h, N, T, slack, X, beta, s, c):
    """per-sample fields h + beta c_s s"""
    S, n = X.shape
    total = np.zeros(S); count = np.zeros(S)
    for t in range(T):
        ht = h[t] + beta * c * s[t]
        delta = ht + X[:, :t] @ N[t, :t] + 0.5 * N[t, t + 1:].sum()
        pref = (delta >= 0).astype(float)
        creator = X[:, t] != pref
        m = ht + X @ N[t] - X[:, t] * N[t, t]
        gain = np.where(pref == 1, m, -m)
        total += np.where(creator, gain, 0.0)
        count += creator
    return (total <= slack * count + 1e-9).mean()


def random_parity_J(n, p, eps, rng):
    """the random model: every pair independently carries a clause with probability p; the clause has
    equal polarities with probability (1+eps)/2 (J_uv = -1), else mixed polarities (J_uv = +1).  The
    polarity of the first literal is a fair coin, which only affects the fields, so it is not drawn."""
    iu = np.triu_indices(n, 1)
    present = rng.random(len(iu[0])) < p
    equal = rng.random(len(iu[0])) < (1 + eps) / 2
    J = np.zeros((n, n))
    J[iu] = np.where(present, np.where(equal, -1.0, 1.0), 0.0)
    return J + J.T


def independent_clauses_J(n, q, eps, rng):
    """the other common model: each of the four clauses on a pair is included independently, the two
    equal-polarity ones (u v v), (-u v -v) with probability q(1+eps), the two mixed ones with probability
    q(1-eps).  A pair can carry 0..4 clauses; J_uv = #mixed - #equal on the pair."""
    iu = np.triu_indices(n, 1)
    k = len(iu[0])
    equal = (rng.random((2, k)) < q * (1 + eps)).sum(axis=0)
    mixed = (rng.random((2, k)) < q * (1 - eps)).sum(axis=0)
    J = np.zeros((n, n))
    J[iu] = mixed - equal
    return J + J.T


def class_constants(J, tau=0.5):
    """mean-centred decomposition: beta = mean of J over pairs u != v, N = J - beta(11^T - I).
    Returns beta, D, K = ||R||^2/D, g from (R2) taken with equality, and the (R3) margin
    g sqrt(D)/(8 tau) / |beta| (the condition holds iff the margin is >= 1)."""
    n = len(J)
    T = int(tau * n)
    beta = J.sum() / (n * (n - 1))
    N = J - beta * (np.ones((n, n)) - np.eye(n))
    D = (N ** 2).sum() / n
    R = np.triu(N, 1)[:T]
    K = np.linalg.norm(R, 2) ** 2 / D
    W = (np.tril(N, -1)[:T] ** 2).sum(axis=1)
    g = np.sqrt(W).sum() / (4 * math.sqrt(3) * n * math.sqrt(D))
    margin = g * math.sqrt(D) / (8 * tau) / abs(beta) if beta != 0 else float("inf")
    alpha = max(2.0, 9 * tau * math.sqrt(K) / (4 * g))
    cstar = g * g / (64 * tau * alpha * alpha * K)
    return beta, D, K, g, margin, cstar


def membership():
    rng = np.random.default_rng(5)
    print("random parity-biased formulas, mean-centred decomposition, tau = 1/2")
    print(f"{'model':>22} {'n':>5} {'eps':>5} {'beta':>8} {'D':>8} {'K':>6} {'g':>7} {'R3 margin':>10} {'c*':>9}")
    rows = [("complete", n, 1.0, e) for n in (500, 1000, 2000) for e in (0.0, 0.5, 0.9, 0.99)]
    rows += [(f"sparse d={d}", 4000, d / 4000, e) for d in (5, 20, 80) for e in (0.0, 0.5, 1.0)]
    rows += [("indep. q=1/4", 2000, 0.25, e) for e in (0.0, 0.5)]
    rows += [("indep. q=d/4n, d=20", 4000, 20 / 16000, e) for e in (0.0, 1.0)]
    for name, n, p, e in rows:
        J = (independent_clauses_J if name.startswith("indep") else random_parity_J)(n, p, e, rng)
        beta, D, K, g, margin, cstar = class_constants(J)
        print(f"{name:>22} {n:5d} {e:5.2f} {beta:8.4f} {D:8.1f} {K:6.2f} {g:7.4f} {margin:10.3g} {cstar:9.1e}",
              flush=True)


if __name__ == "__main__":
    {"exact": exact, "scaling": scaling, "membership": membership}[sys.argv[1]]()
