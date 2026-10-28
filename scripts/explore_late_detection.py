#!/usr/bin/env python3
"""When do domination and pruning clauses start to act on dense balanced
instances?  Random root-to-leaf walks of DPLL + domination + pruning clauses
(no propagation): each branching takes a uniformly random value.  Reported:
the number of unassigned variables at the first domination, and at the first
cut by a pruning clause (medians over walks), with the heuristic estimate
(|Delta| + sqrt(2 delta n ln n)) / delta for the cut, delta = edge probability.
"""
import math
import random
import statistics

from explore_extended_rule import Search, initial, biased


def walk(F, rng, order):
    S = Search(F, {}, True, False, None)
    P, A, cons = initial(F, {}), [None] * F.n, []
    first_dom = None
    for x in order:
        before = sum(a is None for a in A)
        ok = S.closure(P, A, cons)
        after = sum(a is None for a in A)
        if first_dom is None and after < before:
            first_dom = before
        if not ok:
            return first_dom, before
        if A[x] is not None:
            continue
        lsign = 1 if P[x][0] <= P[x][1] else -1
        val = rng.randrange(2)
        if not (val == (1 if lsign == 1 else 0)):          # pruned side
            fav = {}
            for (v, sx, sv) in F.adj[x]:
                if A[v] is None:
                    good = (0 if sv == 1 else 1) if sx == lsign else (1 if sv == 1 else 0)
                    g, w = fav.get(v, (good, 0))
                    fav[v] = (good, w + 1)
            cons.append([fav, P[x][0 if lsign == 1 else 1], 0])
        if not S.assign(P, A, cons, x, val):
            return first_dom, sum(a is None for a in A) + 1
    return first_dom, 0


def main():
    rng = random.Random(3)
    delta = 0.5
    print("    n   first domination   first cut   estimate for the cut")
    for n in (50, 100, 200, 400):
        doms, cuts = [], []
        for _ in range(3):
            F = biased(n, delta, 0.5, 0.0, rng)
            for _ in range(8):
                order = list(range(n))
                rng.shuffle(order)
                d, c = walk(F, rng, order)
                doms.append(d if d is not None else 0)
                cuts.append(c)
        est = (0.8 * math.sqrt(delta * n) + math.sqrt(2 * delta * n * math.log(n))) / delta
        print(f"  {n:4d}   {statistics.median(doms):10.0f}   {statistics.median(cuts):10.0f}"
              f"   {est:10.0f}")
    print("(first domination = 0 means: in most walks no domination happened before the cut)")


if __name__ == "__main__":
    main()
