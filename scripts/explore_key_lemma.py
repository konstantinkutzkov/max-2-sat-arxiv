#!/usr/bin/env python3
"""Tree size of the search in the setting of the Key Lemma.

Random formula (each pair carries a clause with probability d/(n-1), uniform
signs, B = 1), fixed order x_1..x_n, no domination.  Branching on x_t creates
the pruning clause of x_t on its non-preferred side; a node is cut when one
clause is violated or when the sum of the live non-vacuous clauses is
violated.  The tree size is estimated by population splitting (keep M random
live nodes per depth, expand both children, resample), which is unbiased.
Reported: the saving n - log2(tree size), with and without the sum check.
  python3 explore_key_lemma.py 400 50      (n, population; a few minutes)
  python3 explore_key_lemma.py check       (the identity of Lemma 2, exact arithmetic)
"""
import math
import random
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


class State:
    __slots__ = ("P", "cl", "m", "tmin", "tslack")

    def copy(self):
        s = State()
        s.P = [r[:] for r in self.P]
        s.cl = [c[:] for c in self.cl]          # [support dict (shared), k, r, live]
        s.m = [r[:] for r in self.m]
        s.tmin, s.tslack = self.tmin, self.tslack
        return s


def root(adj):
    s = State()
    n = len(adj)
    s.P = [[0, 0] for _ in range(n)]
    for x in range(n):
        for (v, sx, sv) in adj[x]:
            s.P[x][0 if sx == -1 else 1] += 1
    s.cl, s.m, s.tmin, s.tslack = [], [[0, 0] for _ in range(n)], 0, 0
    return s


def add_w(s, w, bad, sgn):
    old = min(s.m[w])
    s.m[w][bad] += sgn
    s.tmin += min(s.m[w]) - old


def step(adj, s, t, val, use_sum):
    """Branch on x_t := val (variables x_0..x_{t-1} are assigned). Returns False if cut."""
    x = t
    pos = s.P[x][0] <= s.P[x][1]
    if (val == 1) != pos:                       # non-preferred side: new clause
        lsign = 1 if pos else -1
        sup = {}
        for (v, sx, sv) in adj[x]:
            if v > x:                           # free neighbours (fixed order)
                sup[v] = (0 if sv == 1 else 1) if sx == lsign else (1 if sv == 1 else 0)
        k = s.P[x][0 if pos else 1] - 1
        if k < 0:
            return False                        # x was dominated: this child is empty
        if k < len(sup):
            s.cl.append([sup, k, len(sup), True])
            for w, bad in sup.items():
                add_w(s, w, bad, +1)
            s.tslack += k
    s.tmin -= min(s.m[x])                       # x leaves the free variables
    for (v, sx, sv) in adj[x]:
        if v > x:
            if not lit_true(val, sx):
                s.P[v][0 if sv == 1 else 1] -= 1
            else:
                s.P[v][1 if sv == 1 else 0] -= 1
    for c in s.cl:
        if not c[3]:
            continue
        bad = c[0].get(x)
        if bad is None:
            continue
        c[2] -= 1
        if val == bad:
            c[1] -= 1
            s.tslack -= 1
            if c[1] < 0:
                return False
        if c[2] <= c[1]:                        # vacuous: leave the sum
            c[3] = False
            s.tslack -= c[1]
            for w, b in c[0].items():
                if w > x:
                    add_w(s, w, b, -1)
    if use_sum and s.tmin > s.tslack:
        return False
    return True


def ladd(a, b):
    """log2(2^a + 2^b), stable for large exponents."""
    hi, lo = max(a, b), min(a, b)
    return hi + math.log2(1 + 2 ** (lo - hi))


def log2_tree(adj, use_sum, M, rng):
    n = len(adj)
    pop, logN, logtotal = [root(adj)], 0.0, 0.0      # all in log2 to avoid overflow
    for t in range(n):
        kids = []
        for st in pop:
            for val in (0, 1):
                ch = st.copy()
                kids.append(ch if step(adj, ch, t, val, use_sum) else None)
        logtotal = ladd(logtotal, logN + math.log2(len(kids) / len(pop)))
        live = [k for k in kids if k is not None]
        if not live or t == n - 1:
            break
        logN += math.log2(len(live) / len(pop))
        pop = [live[rng.randrange(len(live))] for _ in range(M)] if len(live) > M else live
    return logtotal


def check_identity(trials=300, seed=1):
    """For random states and random sets I of non-violated clauses check
    sum_{w free} min(m0,m1) - sum_c k_c
      == sum_c (|Delta_c|/2 + 1 + j_c - a_c/2) - sum_{w free} |b_w|/2."""
    from fractions import Fraction
    rng = random.Random(seed)
    checks = bad = 0
    for _ in range(trials):
        n = rng.randint(8, 40)
        adj = formula(n, rng.uniform(0.1, 0.9) * (n - 1), rng)
        P = [[0, 0] for _ in range(n)]
        for x in range(n):
            for (v, sx, sv) in adj[x]:
                P[x][0 if sx == -1 else 1] += 1
        clauses = []
        for t in range(n):
            x, val = t, rng.randrange(2)
            pos = P[x][0] <= P[x][1]
            if (val == 1) != pos:
                lsign = 1 if pos else -1
                sup = {v: ((0 if sv == 1 else 1) if sx == lsign else (1 if sv == 1 else 0))
                       for (v, sx, sv) in adj[x] if v > x}
                p_c = P[x][0 if pos else 1]
                clauses.append(dict(sup=sup, absDelta=len(sup) - 2 * p_c, p=p_c, a=0, j=0))
            for (v, sx, sv) in adj[x]:
                if v > x:
                    if not lit_true(val, sx):
                        P[v][0 if sv == 1 else 1] -= 1
                    else:
                        P[v][1 if sv == 1 else 0] -= 1
            for c in clauses:
                if x in c['sup']:
                    c['a'] += 1
                    c['j'] += (val == c['sup'][x])
            alive = [c for c in clauses if c['j'] < c['p']]
            I = rng.sample(alive, rng.randint(0, len(alive))) if alive else []
            free = range(t + 1, n)
            m = {w: [0, 0] for w in free}
            for c in I:
                for w, b in c['sup'].items():
                    if w > t:
                        m[w][b] += 1
            lhs = sum(min(m[w]) for w in free) - sum(c['p'] - 1 - c['j'] for c in I)
            rhs = (sum(Fraction(c['absDelta'], 2) + 1 + c['j'] - Fraction(c['a'], 2) for c in I)
                   - sum(Fraction(abs(m[w][1] - m[w][0]), 2) for w in free))
            checks += 1
            bad += lhs != rhs
    print(f"identity of Lemma 2: {checks} random states, {bad} mismatches")


def main():
    if sys.argv[1] == "check":
        check_identity()
        return
    n, M = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(3)
    for d in (64, 256, (n - 1) / 2):
        if d >= n:
            continue
        adj = formula(n, d, rng)
        a = n - log2_tree(adj, False, M, rng)
        b = n - log2_tree(adj, True, M, rng)
        print(f"n={n} d={d:6.1f}: saving with single-clause checks {a / n:.3f} n,"
              f" with the sum check {b / n:.3f} n", flush=True)


if __name__ == "__main__":
    main()
