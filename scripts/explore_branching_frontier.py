#!/usr/bin/env python3
"""Checks for the 7 October branching exploration.

Run: python3 explore_branching_frontier.py
Only small exact enumerations are used. No large-tree estimates are reported.
The weighted-sum bound counts a relaxation, not the intersection of all clauses.
"""
import itertools
import json
import math
import random
from pathlib import Path


def volume(r, k):
    if k < 0:
        return 0
    return sum(math.comb(r, j) for j in range(min(r, k) + 1))


def phase_base(r, k):
    s = volume(r, k)
    lo, hi = 1.0, 2.0
    for _ in range(65):
        lam = (lo + hi) / 2
        if lam ** -1 + s * lam ** (-r - 1) <= 1:
            hi = lam
        else:
            lo = lam
    return hi


def weighted_count(rows, bounds, weights, n):
    """Rows contain -1 (negated), 0 (absent), or +1 (positive) literals.

    Count assignments satisfying the weighted sum of the row inequalities.
    All arithmetic in the certificate is exact integer arithmetic.
    """
    a0 = [sum(a for row, a in zip(rows, weights) if row[j] == -1)
          for j in range(n)]
    a1 = [sum(a for row, a in zip(rows, weights) if row[j] == 1)
          for j in range(n)]
    budget = sum(a * k for a, k in zip(weights, bounds))
    budget -= sum(min(x, y) for x, y in zip(a0, a1))
    costs = [abs(x - y) for x, y in zip(a0, a1)]
    if budget < 0:
        return 0
    if budget >= sum(costs):
        return 2 ** n
    dp = [0] * (budget + 1)
    dp[0] = 1
    for w in costs:
        nxt = dp[:]
        for s in range(w, budget + 1):
            nxt[s] += dp[s - w]
        dp = nxt
    return sum(dp)


def restrict(rows, bounds, x, val):
    adjusted = [k - int(row[x] != 0 and val == int(row[x] == 1))
                for row, k in zip(rows, bounds)]
    return [row[:x] + row[x + 1:] for row in rows], adjusted


def exact_intersection(rows, bounds, n):
    return sum(all(sum(int(v == int(s == 1)) for v, s in zip(bits, row)
                       if s) <= k for row, k in zip(rows, bounds))
               for bits in itertools.product((0, 1), repeat=n))


def choose_bound(rows, bounds, n, inherited=None, rounds=2):
    """Polynomial-size candidate search; always retain the inherited witness."""
    m = len(rows)
    candidates = [tuple([0] * m), tuple([1] * m)]
    candidates += [tuple(int(i == j) for i in range(m)) for j in range(m)]
    if inherited is not None:
        candidates.append(tuple(inherited))
    count, a = min((weighted_count(rows, bounds, a, n), a)
                   for a in candidates)
    for _ in range(rounds):
        improved = False
        for j in range(m):
            for v in (0, 1, 2, 4):
                new = list(a)
                new[j] = v
                new = tuple(new)
                c = weighted_count(rows, bounds, new, n)
                if c < count:
                    count, a = c, new
                    improved = True
        if not improved:
            break
    return count, a


def check_certificates(seed=7102026, trials=150):
    rng = random.Random(seed)
    split_checks = new_clause_checks = 0
    improved_over_single = improved_over_all = 0
    for _ in range(trials):
        n = rng.randint(3, 9)
        m = rng.randint(1, 6)
        rows = [tuple(rng.choice((-1, 0, 1)) for _ in range(n))
                for _ in range(m)]
        bounds = [rng.randint(0, sum(s != 0 for s in row)) for row in rows]
        u, a = choose_bound(rows, bounds, n)
        exact = exact_intersection(rows, bounds, n)
        assert exact <= u <= 2 ** n
        single = min(weighted_count(rows, bounds,
                     [int(i == j) for i in range(m)], n) for j in range(m))
        all_sum = weighted_count(rows, bounds, [1] * m, n)
        improved_over_single += u < single
        improved_over_all += u < all_sum
        for x in range(n):
            total_fixed = total_improved = 0
            for val in (0, 1):
                rr, bb = restrict(rows, bounds, x, val)
                total_fixed += weighted_count(rr, bb, a, n - 1)
                uc, _ = choose_bound(rr, bb, n - 1, a)
                assert exact_intersection(rr, bb, n - 1) <= uc
                total_improved += uc
            assert total_fixed == u
            assert total_improved <= u
            split_checks += 1
        x = rng.randrange(n)
        child_counts = []
        for val in (0, 1):
            rr, bb = restrict(rows, bounds, x, val)
            aa = a
            if val == 1:
                row = tuple(rng.choice((-1, 0, 1)) for _ in range(n - 1))
                rr.append(row)
                bb.append(rng.randint(0, sum(s != 0 for s in row)))
                aa = a + (0,)
            uc, _ = choose_bound(rr, bb, n - 1, aa)
            assert exact_intersection(rr, bb, n - 1) <= uc
            child_counts.append(uc)
        assert sum(child_counts) <= u
        new_clause_checks += 1
    return dict(seed=seed, systems=trials, split_checks=split_checks,
                added_clause_checks=new_clause_checks,
                improved_over_best_single=improved_over_single,
                improved_over_unweighted_all_sum=improved_over_all)


def check_phases():
    checks = 0
    for r in range(2, 101):
        for k in range(1, (r - 1) // 2 + 1):
            s = volume(r, k)
            assert s == volume(r - 1, k) + volume(r - 1, k - 1)
            q = k / (r - k + 1)
            for t in range(1, k + 1):
                assert volume(r, k - t) / s <= q ** t + 1e-12
                checks += 1
    lam = 1.8
    forced_checks = 0
    for r in range(1, 60):
        for k in range(r + 1):
            e = r - math.log(volume(r, k), lam)
            for val in (0, 1):
                if volume(r - 1, k - val):
                    ec = r - 1 - math.log(volume(r - 1, k - val), lam)
                    assert e - ec <= 1 + 1e-10
                    forced_checks += 1
    return dict(tail_checks=checks, forced_transition_checks=forced_checks,
                full_phase_bases=[dict(D=r, k=r // 4,
                                      base=phase_base(r, r // 4))
                                  for r in (16, 32, 64, 128)])


def illustrative_examples():
    # A contradictory pair plus a weak, distracting third clause.
    n = 27
    rows = [(1,) * 7 + (0,) * 20, (-1,) * 7 + (0,) * 20,
            (0,) * 7 + (1,) * 20]
    bounds = [3, 3, 19]
    u, a = choose_bound(rows, bounds, n)
    assert u == 0
    # LP-feasible but Boolean-infeasible: three equations x+y=y+z=z+x=1.
    odd = [(1, 1, 0), (-1, -1, 0), (0, 1, 1), (0, -1, -1),
           (1, 0, 1), (-1, 0, -1)]
    assert exact_intersection(odd, [1] * 6, 3) == 0
    min_odd = min(weighted_count(odd, [1] * 6, aa, 3)
                  for aa in itertools.product(range(3), repeat=6))
    assert min_odd > 0
    return dict(distracting_clause=dict(
                    unweighted_count=weighted_count(rows, bounds, [1, 1, 1], n),
                    weighted_count=u, weights=a),
                odd_cycle=dict(actual_completions=0,
                               min_bound_weights_0_to_2=min_odd))


def check_max2sat_soundness(trials=80):
    """Exercise a full-phase search on small formulas, against brute force.

    While resolving a newly created clause, no other simplification is used.
    Other branches recurse normally. No claim about large-instance speed.
    """
    from explore_dpll_measures import Formula, assign, close
    from explore_extended_rule import brute_opt
    rng = random.Random(7112026)
    phase_nodes = 0

    def search(f, p, assignment):
        nonlocal phase_nodes
        close(f, p, assignment)
        free = [x for x, a in enumerate(assignment) if a is None]
        if not free:
            return sum(any(assignment[v] == int(s == 1) for v, s in clause)
                       for clause in f.clauses)
        x = min(free, key=lambda v: min(p[v]) / sum(p[v]))
        pos = p[x][0] <= p[x][1]
        literal = 1 if pos else -1
        k = min(p[x]) - 1
        support = [(v, (0 if sv == 1 else 1) if sx == literal
                    else (1 if sv == 1 else 0))
                   for v, sx, sv in f.adj[x] if assignment[v] is None]
        phase_nodes += 1
        pp, aa = [z[:] for z in p], assignment[:]
        assign(f, pp, aa, x, int(pos))
        best = search(f, pp, aa)
        for size in range(min(k, len(support)) + 1):
            for indices in itertools.combinations(range(len(support)), size):
                chosen = set(indices)
                pp, aa = [z[:] for z in p], assignment[:]
                assign(f, pp, aa, x, 1 - int(pos))
                for j, (v, bad) in enumerate(support):
                    assign(f, pp, aa, v, bad if j in chosen else 1 - bad)
                best = max(best, search(f, pp, aa))
        return best

    for _ in range(trials):
        n = rng.randint(3, 10)
        clauses = [((u, rng.choice((-1, 1))), (v, rng.choice((-1, 1))))
                   for u in range(n) for v in range(u + 1, n)
                   if rng.random() < .65]
        f = Formula(n, clauses)
        result = search(f, f.initial_state(), [None] * n)
        assert result == brute_opt(f, {})
    return dict(formulas=trials, phase_nodes=phase_nodes)


def small_branching_comparison():
    """Exact small-tree comparison, counting also the lookahead work.

    Each state keeps all pruning rows, so inherited certificates retain their
    indices. This prototype uses singletons/all-ones/inheritance (no local
    weight optimization) to keep the experiment short.
    """
    from explore_sum_rule import (formula, root, closure, children, score,
                                  brute)
    rng = random.Random(7122026)
    records = []

    def solve(adj, strategy):
        visited = lookahead = 0

        def bound(s, a):
            free = [v for v, x in enumerate(s.A) if x is None]
            rows = [tuple((1 if c[0][v][0] else -1) if v in c[0] else 0
                          for v in free) for c in s.cl]
            bounds = [c[1] - 1 - c[2] for c in s.cl]
            a = tuple(a) + (0,) * (len(rows) - len(a))
            return choose_bound(rows, bounds, len(free), a, rounds=0)

        def rec(s, u, a):
            nonlocal visited, lookahead
            visited += 1
            if not s.free:
                return score(adj, s.A)
            free = [v for v, x in enumerate(s.A) if x is None]
            options = free if strategy == 'joint-volume' else free[:1]
            best = None
            for x in options:
                kk = children(adj, s, 'random order', False, [x] + free)
                evaluated = []
                for kind, child in kk:
                    lookahead += 1
                    uc, ac = (0, ()) if kind == 'dead' else bound(child, a)
                    evaluated.append((kind, child, uc, ac))
                total = sum(z[2] for z in evaluated)
                assert total <= u
                key = (total, x)
                if best is None or key < best[0]:
                    best = (key, evaluated)
            ans = -1
            for kind, child, uc, ac in best[1]:
                if kind != 'dead' and uc > 0:
                    ans = max(ans, rec(child, uc, ac))
            return ans

        s = root(adj)
        assert closure(adj, s)
        u, a = bound(s, ())
        value = rec(s, u, a)
        return value, visited, lookahead

    for n in (12, 16):
        for instance in range(3):
            adj = formula(n, .7, rng)
            results = {s: solve(adj, s) for s in ('static', 'joint-volume')}
            optimum = brute(adj)
            # The existing brute helper returns the optimum score.
            assert all(v[0] == optimum for v in results.values())
            records.append(dict(n=n, instance=instance, optimum=optimum,
                                results={s: dict(visited=v[1],
                                                 lookahead_children=v[2])
                                         for s, v in results.items()}))
    return records


def main():
    result = dict(phase_checks=check_phases(),
                  certificate_checks=check_certificates(),
                  examples=illustrative_examples(),
                  max2sat_checks=check_max2sat_soundness(),
                  small_branching_comparison=small_branching_comparison())
    path = Path(__file__).with_name('branching_frontier_checks.json')
    path.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
