#!/usr/bin/env python3
"""Pruning constraints in one branch or in both branches.

Boolean form F(x) = c0 + h.x + sum_{u<v} J_uv x_u x_v.  The gain of u is g_u(x) = h_u + sum_w J_uw x_w,
the change of F when x_u goes from 0 to 1 (linear in the other variables).

DPLL over the order 0..n-1 with domination (force x_u = 1 if g_u >= 0 for every completion, x_u = 0
if g_u <= 0 for every completion).  Otherwise branch; the preferred value p is 1 iff the expected gain
with the free variables at 1/2 is >= 0.  Constraints (all checked at every node: a node dies as soon
as some constraint fails for every completion):
  one   non-preferred child only: flipping u back strictly loses      (the user's rule)
  two   additionally, preferred child: flipping u away does not gain  (non-strict, ties go there)
  both  both children strict (to show that ties then cut the optimum)

  python3 explore_two_sided.py [table | soundness | scaling | combine]
"""
import itertools
import sys

import numpy as np

sys.path.insert(0, "/Users/konstantin.kutzkov/Desktop/max-2-sat")
from explore_count_guessing import from_clauses, parity_biased  # noqa: E402


def brute(c0, h, J):
    n = len(h)
    X = np.array(list(itertools.product((0, 1), repeat=n)), dtype=float)
    return (c0 + X @ h + 0.5 * np.einsum("ij,jk,ik->i", X, J, X)).max()


class Search:
    def __init__(self, c0, h, J, mode):
        self.c0, self.h, self.J, self.mode = c0, h, J, mode
        # constraints registered at the root, before branching: for every u, on the side
        # r_u = root non-preferred value (all other variables at 1/2), "flipping u strictly loses"
        self.root_side = (h + 0.5 * J.sum(axis=1) < 0).astype(int)
        n = self.n = len(h)
        neg, pos = np.minimum(J, 0), np.maximum(J, 0)
        # tail sums over the free variables w >= t
        self.negtail = np.zeros((n, n + 1))
        self.postail = np.zeros((n, n + 1))
        self.halftail = np.zeros((n, n + 1))
        for t in range(n - 1, -1, -1):
            self.negtail[:, t] = self.negtail[:, t + 1] + neg[:, t]
            self.postail[:, t] = self.postail[:, t + 1] + pos[:, t]
            self.halftail[:, t] = self.halftail[:, t + 1] + 0.5 * J[:, t]
        self.nodes = 0
        self.leaves = 0
        self.best = -1e18
        self.x = np.zeros(n)

    def alive(self, t, cons):
        """cons: list of (u, kind); kind in lt, gt, le, ge (g_u compared with 0)."""
        if not cons:
            return True
        U = np.array([u for u, _ in cons])
        s = self.h[U] + self.J[U, :t] @ self.x[:t]
        lo = s + self.negtail[U, t]
        hi = s + self.postail[U, t]
        for (u, kind), a, b in zip(cons, lo, hi):
            if kind == "lt" and a >= 0:
                return False
            if kind == "gt" and b <= 0:
                return False
            if kind == "le" and a > 0:
                return False
            if kind == "ge" and b < 0:
                return False
        return True

    def run(self, t=0, cons=()):
        self.nodes += 1
        if not self.alive(t, cons):
            return
        if t == self.n:
            self.leaves += 1
            x = self.x
            self.best = max(self.best, self.c0 + self.h @ x + 0.5 * x @ self.J @ x)
            return
        s = self.h[t] + self.J[t, :t] @ self.x[:t]
        lo, hi = s + self.negtail[t, t + 1], s + self.postail[t, t + 1]
        if lo >= 0 or hi <= 0:                       # domination: one child
            self.x[t] = 1.0 if lo >= 0 else 0.0
            self.run(t + 1, cons)
            return
        if self.mode in ("pre", "prec", "prens"):
            r = int(self.root_side[t])
            pre = ("lt" if r == 0 else "gt")         # x_t = r: flipping to 1 - r strictly loses
            dead = (lo >= 0) if r == 0 else (hi <= 0)
            if dead:                                  # the registered constraint forces x_t
                self.x[t] = 1.0 - r
                self.run(t + 1, cons)
                return
            if self.mode == "prec":                   # branch with the registered orientation
                for val in (1 - r, r):
                    self.x[t] = val
                    self.run(t + 1, tuple(cons) + (((t, pre),) if val == r else ()))
                self.x[t] = 0.0
                return
            p = 1 if s + self.halftail[t, t + 1] >= 0 else 0
            bad = ("lt" if p == 1 else "gt")
            if self.mode == "prens" and p == r:       # path preference disagrees with the registered
                bad = ("le" if p == 1 else "ge")      # orientation: flipping to p must not strictly gain
            for val in (p, 1 - p):                    # path-dependent branching constraint, plus
                self.x[t] = val                       # the registered one wherever x_t = r
                extra = ((t, bad),) if val != p else ()
                if val == r:
                    extra = extra + ((t, pre),)
                self.run(t + 1, tuple(cons) + extra)
            self.x[t] = 0.0
            return
        p = 1 if s + self.halftail[t, t + 1] >= 0 else 0
        # constraint on g_t in the non-preferred child: flipping back to p strictly loses
        bad = ("lt" if p == 1 else "gt")
        if self.mode == "one":
            good = None
        elif self.mode == "two":                     # flipping away from p does not gain
            good = ("ge" if p == 1 else "le")
        else:                                        # both strict
            good = ("gt" if p == 1 else "lt")
        for val in (p, 1 - p):
            self.x[t] = val
            extra = ((t, bad),) if val != p else (((t, good),) if good else ())
            self.run(t + 1, tuple(cons) + extra)
        self.x[t] = 0.0


def with_units(n, clauses, rng, rate):
    """add rate*n unit clauses on random literals (as one-literal clauses u v u)"""
    cl = list(clauses)
    for _ in range(int(rate * n)):
        u = int(rng.integers(n))
        s = int(rng.choice((1, -1)))
        cl.append((u, s, u, s))
    return cl


def from_clauses_units(n, clauses):
    """clauses with u == v are unit clauses on the literal (u, s)"""
    c0, h, J = from_clauses(n, [c for c in clauses if c[0] != c[2]])
    for (u, s, v, _) in clauses:
        if u == v:
            if s == 1:
                h[u] += 1                  # clause (u) = x_u
            else:
                c0 += 1
                h[u] -= 1                  # clause (-u) = 1 - x_u
    return c0, h, J


def random_formula(n, d, rng):
    m = int(d * n / 2)
    cl = []
    for _ in range(m):
        u, v = rng.choice(n, 2, replace=False)
        cl.append((int(u), int(rng.choice((1, -1))), int(v), int(rng.choice((1, -1)))))
    return cl


def maxcut_complete(m):
    cl = []
    for u in range(m):
        for v in range(u + 1, m):
            cl += [(u, 1, v, 1), (u, -1, v, -1)]
    return cl


def main():
    rng = np.random.default_rng(7)
    families = []
    for d in (4, 8):
        for _ in range(6):
            n = 16
            families.append((f"random d={d}, units", n,
                             with_units(n, random_formula(n, d, rng), rng, 1.0)))
    for _ in range(6):
        n = 16
        families.append(("complete, eps=0.9, units", n,
                         with_units(n, parity_biased(n, 0.9, rng), rng, 1.0)))
    for m in (12, 14, 16):
        families.append((f"Max-Cut K_{m}", m, maxcut_complete(m)))

    print(f"{'family':28s} {'nodes one':>10s} {'nodes two':>10s} {'ratio':>6s} "
          f"{'lost one/two/both':>18s}")
    agg = {}
    for name, n, cl in families:
        c0, h, J = from_clauses_units(n, cl)
        opt = brute(c0, h, J)
        res = {}
        for mode in ("one", "two", "both"):
            S = Search(c0, h, J, mode)
            S.run()
            res[mode] = (S.nodes, abs(S.best - opt) > 1e-9)
        a = agg.setdefault(name, [0, 0, 0, 0, 0, 0])
        a[0] += res["one"][0]; a[1] += res["two"][0]
        a[2] += res["one"][1]; a[3] += res["two"][1]; a[4] += res["both"][1]; a[5] += 1
    for name, (n1, n2, l1, l2, l3, k) in agg.items():
        print(f"{name:28s} {n1 / k:10.0f} {n2 / k:10.0f} {n1 / n2:6.2f} "
              f"{f'{l1}/{l2}/{l3} of {k}':>18s}", flush=True)


def soundness():
    """many small instances: how often is the optimum lost?"""
    rng = np.random.default_rng(11)
    lost = {"one": 0, "two": 0, "both": 0}
    k = 0
    for trial in range(300):
        n = int(rng.integers(6, 13))
        kind = trial % 3
        if kind == 0:
            cl = with_units(n, random_formula(n, float(rng.choice([2, 4, 8])), rng), rng, 1.0)
        elif kind == 1:
            cl = with_units(n, parity_biased(n, float(rng.choice([0.0, 0.5, 0.9])), rng), rng, 0.5)
        else:
            cl = random_formula(n, float(rng.choice([3, 6])), rng)       # no units: many ties
        c0, h, J = from_clauses_units(n, cl)
        opt = brute(c0, h, J)
        for mode in lost:
            S = Search(c0, h, J, mode)
            S.run()
            lost[mode] += abs(S.best - opt) > 1e-9
        k += 1
    print(f"soundness, {k} instances with n = 6..12: optimum lost  one {lost['one']}, "
          f"two {lost['two']}, both strict {lost['both']}")


def combine():
    """constraints registered before branching, combined with path-dependent branching constraints"""
    rng = np.random.default_rng(13)
    modes = ("one", "pre", "prec", "prens")
    lost = dict.fromkeys(modes, 0)
    nodes = dict.fromkeys(modes, 0)
    k = 0
    for trial in range(300):
        n = int(rng.integers(6, 13))
        if trial % 2 == 0:
            cl = with_units(n, random_formula(n, float(rng.choice([3, 6, 9])), rng), rng, 0.7)
        else:
            cl = with_units(n, parity_biased(n, float(rng.choice([0.0, 0.6])), rng), rng, 0.5)
        c0, h, J = from_clauses_units(n, cl)
        opt = brute(c0, h, J)
        for mode in modes:
            S = Search(c0, h, J, mode)
            S.run()
            lost[mode] += abs(S.best - opt) > 1e-9
            nodes[mode] += S.nodes
        k += 1
    for mode, label in (("one", "branching constraints only"),
                        ("pre", "registered at root + path-dependent branching constraints"),
                        ("prec", "registered at root, branching follows their orientation"),
                        ("prens", "registered at root + path-dependent, non-strict where they disagree")):
        print(f"{label:58s} optimum lost {lost[mode]:3d} of {k}, nodes {nodes[mode]}")


def scaling():
    rng = np.random.default_rng(5)
    print(f"{'family':30s} {'n':>3s} {'nodes one':>10s} {'nodes two':>10s} "
          f"{'leaves one':>11s} {'leaves two':>11s}")
    for name, make in (("random d=6, units", lambda n: with_units(n, random_formula(n, 6, rng), rng, 1.0)),
                       ("random d=12, units", lambda n: with_units(n, random_formula(n, 12, rng), rng, 1.0)),
                       ("complete eps=0, units", lambda n: with_units(n, parity_biased(n, 0.0, rng), rng, 1.0)),
                       ("complete eps=0.9, units", lambda n: with_units(n, parity_biased(n, 0.9, rng), rng, 1.0))):
        for n in (16, 20, 24):
            tot = np.zeros(4)
            for _ in range(3):
                c0, h, J = from_clauses_units(n, make(n))
                for j, mode in enumerate(("one", "two")):
                    S = Search(c0, h, J, mode)
                    S.run()
                    tot[j] += S.nodes
                    tot[2 + j] += S.leaves
            tot /= 3
            print(f"{name:30s} {n:3d} {tot[0]:10.0f} {tot[1]:10.0f} {tot[2]:11.0f} {tot[3]:11.0f}",
                  flush=True)


if __name__ == "__main__":
    {"table": main, "soundness": soundness, "scaling": scaling, "combine": combine}[sys.argv[1] if len(sys.argv) > 1 else "table"]()
