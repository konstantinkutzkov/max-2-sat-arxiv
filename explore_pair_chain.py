#!/usr/bin/env python3
"""Chaining pair decisions (x0 ? x1, then x1 ? x2, ...).

In the branch x_i != x_{i+1} an assignment is kept only if two flips both
strictly lose:
  naive  flip x_i alone, and x_{i+1} alone
  class  flip x_i together with everything tied to it by earlier decisions
         (here x_0 .. x_i), and x_{i+1} alone
The '=' branches are kept without condition.  The naive version can lose every
optimum; the class version cannot (flipping a whole class keeps all earlier
decisions).  Formulas: the two-clause example, the circulant family C_{n,c},
and Max-Cut on K_m (clauses (x_i|x_j) and (~x_i|~x_j) for every pair).

Also printed: the number of strict local maxima (every single flip strictly
lowers the score).  Rules implied by single flips never cut them; the class
conditions can.
"""
import itertools


def score(clauses, a):
    """clauses: list of ((i, si), (j, sj)) with signs +1/-1."""
    lit = lambda v, s: a[v] if s == 1 else 1 - a[v]
    return sum(1 for (i, si), (j, sj) in clauses if lit(i, si) or lit(j, sj))


def flip(a, S):
    b = list(a)
    for v in S:
        b[v] = 1 - b[v]
    return tuple(b)


def survivors(clauses, n, use_class):
    out = []
    for a in itertools.product((0, 1), repeat=n):
        s = score(clauses, a)
        keep = all(a[i] == a[i + 1]
                   or (score(clauses, flip(a, range(i + 1) if use_class else [i])) < s
                       and score(clauses, flip(a, [i + 1])) < s)
                   for i in range(n - 1))
        if keep:
            out.append(a)
    return out


def strict_local_maxima(clauses, n):
    count = 0
    for a in itertools.product((0, 1), repeat=n):
        s = score(clauses, a)
        if all(score(clauses, flip(a, [i])) < s for i in range(n)):
            count += 1
    return count


def circulant(n, c):
    return [((i, 1), (j, 1)) if min(j - i, n - j + i) <= c else ((i, -1), (j, -1))
            for i in range(n) for j in range(i + 1, n)]


def maxcut_complete(m):
    return [cl for i in range(m) for j in range(i + 1, m)
            for cl in (((i, 1), (j, 1)), ((i, -1), (j, -1)))]


def report(name, clauses, n):
    opt = max(score(clauses, a) for a in itertools.product((0, 1), repeat=n))
    for use_class in (False, True):
        surv = survivors(clauses, n, use_class)
        best = max(score(clauses, a) for a in surv)
        print(f"{name:20s}  {'class' if use_class else 'naive'}: {len(surv):4d} of {2 ** n} survive,"
              f" best surviving score {best}, optimum {opt}")
    print(f"{name:20s}  strict local maxima: {strict_local_maxima(clauses, n)}")


if __name__ == "__main__":
    report("(x0|x1),(~x1|~x2)", [((0, 1), (1, 1)), ((1, -1), (2, -1))], 3)
    for n, c in ((9, 2), (11, 3), (13, 3)):
        report(f"C_{{{n},{c}}}", circulant(n, c), n)
    for m in (8, 10, 12):
        report(f"Max-Cut K_{m}", maxcut_complete(m), m)
