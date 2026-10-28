#!/usr/bin/env python3
"""The soft-count measure for adaptive branching with learned pruning constraints.

A node has free variables W and learned constraints i: support N_i (free part), a bad value
beta_i(w) in {0,1} for w in N_i, a current allowance k_i, and a weight lam_i >= 0.  With
A_w^b = sum of lam_i over the constraints in which b is the bad value of w,
    Phi = exp(sum_i lam_i k_i) * prod_{w in W} (exp(-A_w^0) + exp(-A_w^1))
        = sum over completions y of prod_i exp(lam_i (k_i - L_i(y))).

  python3 explore_soft_count.py examples   the hand examples of the note
  python3 explore_soft_count.py search     adaptive search on small random formulas, with checks
  python3 explore_soft_count.py aligned    the circulant formula C_(9,2)
  python3 explore_soft_count.py reopt      the measure with all weights re-optimized stays valid
"""
import itertools
import math
import random
import sys

LMAX = 30.0                                   # stands for an infinite weight (allowance 0)
LN2 = math.log(2)


def lse(a, b):
    """log(exp(a) + exp(b))"""
    m = max(a, b)
    return m + math.log(math.exp(a - m) + math.exp(b - m))


class Con:
    __slots__ = ("sup", "k0", "lam")

    def __init__(self, sup, k0, lam=0.0):
        self.sup, self.k0, self.lam = sup, k0, lam


def state(c, assign):
    """current allowance and free support of a constraint"""
    k = c.k0 - sum(1 for w, b in c.sup.items() if w in assign and assign[w] == b)
    free = {w: b for w, b in c.sup.items() if w not in assign}
    return k, free


def log_phi(cons, assign, free_vars):
    A = {w: [0.0, 0.0] for w in free_vars}
    s = 0.0
    for c in cons:
        if c.lam == 0:
            continue
        k, free = state(c, assign)
        s += c.lam * k
        for w, b in free.items():
            A[w][b] += c.lam
    return s + sum(lse(-a0, -a1) for (a0, a1) in A.values()), A


def brute(cons, assign, free_vars):
    """(Phi by summing over completions, number of completions satisfying every constraint)"""
    free_vars = sorted(free_vars)
    tot, cnt = 0.0, 0
    for vals in itertools.product((0, 1), repeat=len(free_vars)):
        y = dict(assign)
        y.update(zip(free_vars, vals))
        logw, ok = 0.0, True
        for c in cons:
            L = sum(1 for w, b in c.sup.items() if y[w] == b)
            if L > c.k0:
                ok = False
            logw += c.lam * (c.k0 - L)
        tot += math.exp(logw)
        cnt += ok
    return tot, cnt


def bad_probs(A, sup):
    """log-probabilities (good, bad) of each support variable under the current soft count"""
    out = []
    for w, b in sup.items():
        z = lse(-A[w][0], -A[w][1])
        out.append((-A[w][1 - b] - z, -A[w][b] - z))
    return out


def best_weight(k, lps):
    """lam >= 0 minimizing the factor of a new constraint with allowance k whose support
    variables have log-probabilities lps = [(log p_good, log p_bad)]."""
    def deriv(lam):
        return k - sum(1.0 / (1.0 + math.exp(min(700.0, lg - lb + lam))) for (lg, lb) in lps)
    if deriv(0.0) >= 0:
        return 0.0
    if deriv(LMAX) < 0:
        return LMAX
    lo, hi = 0.0, LMAX
    for _ in range(80):
        mid = (lo + hi) / 2
        if deriv(mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def log_factor(k, lps, lam):
    """log of  e^{lam k} prod_w (p_good + p_bad e^{-lam})"""
    return lam * k + sum(lse(lg, lb - lam) for (lg, lb) in lps)


def reopt(cons, assign, free_vars, sweeps=300):
    """Coordinate descent on the weights; log Phi is convex in them, so this converges to
    min over all weights.  Returns (weights, log Phi)."""
    cons = [Con(c.sup, c.k0, c.lam) for c in cons]
    for _ in range(sweeps):
        change = 0.0
        for c in cons:
            k, fr = state(c, assign)
            if not fr:
                new = 0.0 if k >= 0 else LMAX
            else:
                old = c.lam
                c.lam = 0.0
                _, A = log_phi(cons, assign, free_vars)
                c.lam = old
                new = best_weight(k, bad_probs(A, fr))
            change = max(change, abs(new - c.lam))
            c.lam = new
        if change < 1e-10:
            break
    return cons, log_phi(cons, assign, free_vars)[0]


# ---------------------------------------------------------------- the formula side
def random_formula(n, d, rng):
    p = d / (n - 1)
    cl = []
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                cl.append((i, rng.choice((1, -1)), j, rng.choice((1, -1))))
    return n, cl


def circulant(n, c):
    cl = []
    for i in range(n):
        for j in range(i + 1, n):
            s = 1 if min(j - i, n - j + i) <= c else -1
            cl.append((i, s, j, s))
    return n, cl


def incidence(F):
    n, cl = F
    inc = [[] for _ in range(n)]
    for (u, su, v, sv) in cl:
        inc[u].append((v, su, sv))
        inc[v].append((u, sv, su))
    return inc


def lit_true(val, s):
    return val == (1 if s == 1 else 0)


def gap(inc, x, assign):
    delta = D = 0
    for (v, sx, sv) in inc[x]:
        if v not in assign:
            delta += sx
            D += 1
        elif not lit_true(assign[v], sv):
            delta += 2 * sx                      # the clause is now the unit clause on x
    return delta, D


def new_constraint(inc, x, assign):
    delta, D = gap(inc, x, assign)
    pref = 1 if delta >= 0 else 0
    lsign = 1 if pref == 1 else -1
    sup = {}
    for (v, sx, sv) in inc[x]:
        if v not in assign:
            sup[v] = (0 if sv == 1 else 1) if sx == lsign else (1 if sv == 1 else 0)
    return pref, Con(sup, (D - abs(delta)) // 2 - 1)


def score(F, assign):
    n, cl = F
    return sum(1 for (u, su, v, sv) in cl if lit_true(assign[u], su) or lit_true(assign[v], sv))


# ---------------------------------------------------------------- one branching step
def step(F, inc, cons, assign, x, checks):
    """The two children of branching on x.  Returns (I_x in bits, children) where each child is
    (assignment, constraints).  The new constraint gets the weight minimizing its factor."""
    free = [w for w in range(F[0]) if w not in assign]
    lp, A = log_phi(cons, assign, free)
    pref, c = new_constraint(inc, x, assign)
    kids = []
    logs = []
    for val in (pref, 1 - pref):
        a2 = dict(assign)
        a2[x] = val
        free2 = [w for w in free if w != x]
        lc, A2 = log_phi(cons, a2, free2)
        logs.append(lc)
        cons2 = [Con(cc.sup, cc.k0, cc.lam) for cc in cons]
        if val != pref:
            lps = bad_probs(A2, c.sup)
            c.lam = best_weight(c.k0, lps) if c.sup else (LMAX if c.k0 < 0 else 0.0)
            cons2.append(c)
            lnew, _ = log_phi(cons2, a2, free2)
            checks["factor"] = checks.get("factor", 0) + 1
            assert abs(lnew - (lc + log_factor(c.k0, lps, c.lam))) < 1e-6 * (1 + abs(lnew)), "factor formula"
            assert lnew <= lc + 1e-9, "the new constraint raised Phi"
            lc = lnew
        for cc in cons2:                            # vacuous constraints: weight 0 (lowers Phi)
            k, fr = state(cc, a2)
            if cc.lam > 0 and k >= len(fr):
                cc.lam = 0.0
        lc2, _ = log_phi(cons2, a2, free2)
        assert lc2 <= lc + 1e-9, "dropping a vacuous constraint raised Phi"
        kids.append((a2, cons2, lc2))
    checks["additive"] += 1
    assert abs(lse(logs[0], logs[1]) - lp) < 1e-9, "Phi is not additive"
    info = (lp - lse(kids[0][2], kids[1][2])) / LN2
    assert info >= -1e-9, "a branching step increased Phi"
    return info, kids


def search(F, rule, checks, sample, rng):
    inc = incidence(F)
    n = F[0]
    stats = {"nodes": 0, "best": -1, "info": []}

    def rec(assign, cons, info_path):
        stats["nodes"] += 1
        free = [w for w in range(n) if w not in assign]
        for c in cons:
            if state(c, assign)[0] < 0:
                return                                    # a constraint is violated
        lp, _ = log_phi(cons, assign, free)
        if rng.random() < sample and len(free) <= 12:
            tot, cnt = brute(cons, assign, free)
            checks["closed form"] += 1
            assert abs(math.log(tot) - lp) < 1e-7, "closed form differs from the sum"
            checks["upper bound"] += 1
            assert tot >= cnt - 1e-9, "Phi below the number of permitted completions"
        if lp < -1e-12:
            return                                        # Phi < 1: no completion satisfies all
        if not free:
            stats["best"] = max(stats["best"], score(F, assign))
            stats["info"].append(info_path)
            return
        if rule == "fixed":
            x = free[0]
            info, kids = step(F, inc, cons, assign, x, checks)
        else:
            best = None
            for x in free:
                info, kids = step(F, inc, cons, assign, x, checks)
                if best is None or info > best[0] + 1e-12:
                    best = (info, kids)
            info, kids = best
        for (a2, cons2, _) in kids:
            rec(a2, cons2, info_path + info)

    rec({}, [], 0.0)
    return stats


def optimum(F):
    n = F[0]
    return max(score(F, dict(enumerate(v))) for v in itertools.product((0, 1), repeat=n))


# ---------------------------------------------------------------- modes
def examples():
    print("Example A: one constraint on four fresh variables, allowance 0 (the child x1 = 0)")
    sup = {1: 0, 2: 0, 3: 1, 4: 1}                       # bad: x2=0, x3=0, x4=1, x5=1
    for lam in (0.0, 1.0, 2.0, LMAX):
        c = Con(sup, 0, lam)
        tot, cnt = brute([c], {}, [1, 2, 3, 4])
        lp, _ = log_phi([c], {}, [1, 2, 3, 4])
        print(f"  lam={lam:5.1f}: Phi={math.exp(lp):8.4f} (sum over completions {tot:8.4f}), permitted={cnt}")
    lam = 1.0
    c = Con(sup, 0, lam)
    l1, _ = log_phi([c], {1: 1}, [2, 3, 4])
    l0, _ = log_phi([c], {1: 0}, [2, 3, 4])
    lp, _ = log_phi([c], {}, [1, 2, 3, 4])
    print(f"  branching on x2 at lam=1: {math.exp(l1):.4f} + {math.exp(l0):.4f} = {math.exp(l1) + math.exp(l0):.4f}"
          f" = Phi {math.exp(lp):.4f}")

    print("\nExample B: a constraint 'at most 1 of y1..y4 is 1' (allowance 1) is present with weight ln 3;")
    print("a second constraint with allowance 1 arrives on the same four variables.")
    first = Con({0: 1, 1: 1, 2: 1, 3: 1}, 1, math.log(3))
    lp0, A = log_phi([first], {}, range(4))
    print(f"  Phi with the first constraint alone: {math.exp(lp0):.4f} (permitted completions: 5)")
    for name, bads in (("agrees (bad values 1,1,1,1)", (1, 1, 1, 1)),
                       ("half (bad values 1,1,0,0)", (1, 1, 0, 0)),
                       ("disagrees (bad values 0,0,0,0)", (0, 0, 0, 0))):
        lps = bad_probs(A, dict(enumerate(bads)))
        lam = best_weight(1, lps)
        F = math.exp(log_factor(1, lps, lam))
        second = Con(dict(enumerate(bads)), 1, lam)
        tot, cnt = brute([first, second], {}, range(4))
        q = [round(math.exp(lb), 3) for (lg, lb) in lps]
        _, lstar = reopt([first, second], {}, list(range(4)))
        print(f"  {name:32s}: q = {q}, best weight {lam:6.3f},"
              f" factor {F:.4f}, Phi {tot:.4f}, both weights re-optimized {math.exp(lstar):.4f}, permitted {cnt}")

    print("\nExample C: one branching step on a small formula with a constraint already learned")
    F = (6, [(0, 1, 1, 1), (0, 1, 2, -1), (0, -1, 3, 1), (1, -1, 2, 1), (1, 1, 4, 1),
             (2, 1, 5, -1), (3, 1, 4, -1), (3, -1, 5, 1), (4, 1, 5, 1)])
    inc = incidence(F)
    pref0, c0 = new_constraint(inc, 0, {})
    print(f"  root: x1 has gap {gap(inc, 0, {})}, preferred value {pref0};"
          f" its constraint: support/bad {c0.sup}, allowance {c0.k0}")
    assign = {0: 1 - pref0}
    free = [w for w in range(6) if w not in assign]
    lp, A = log_phi([], assign, free)
    c0.lam = best_weight(c0.k0, bad_probs(A, c0.sup))
    cons = [c0]
    lp, A = log_phi(cons, assign, free)
    print(f"  in the child x1={1 - pref0}: weight {c0.lam:.4f}, Phi = {math.exp(lp):.4f}"
          f" (2^5 = 32 completions without the constraint)")
    checks = {"additive": 0}
    for x in free:
        info, kids = step(F, inc, cons, assign, x, checks)
        delta, D = gap(inc, x, assign)
        newc = kids[1][1][-1]
        print(f"  branch on x{x + 1}: gap {delta:+d} over {D} free neighbours; children Phi"
              f" {math.exp(kids[0][2]):.4f} + {math.exp(kids[1][2]):.4f};"
              f" new constraint allowance {newc.k0}, weight {newc.lam:.3f}; I = {info:.4f} bits")


def search_mode():
    rng = random.Random(3)
    checks = {"additive": 0, "closed form": 0, "upper bound": 0}
    print(f"{'n':>3} {'d':>3} {'plain':>6} {'fixed order':>12} {'adaptive':>9}  optimum ok")
    for (n, d) in ((10, 3), (10, 5), (12, 4), (12, 6), (12, 8), (14, 6), (16, 6), (16, 10)):
        F = random_formula(n, d, rng)
        opt = optimum(F)
        s_fix = search(F, "fixed", checks, 0.2, rng)
        s_ada = search(F, "adaptive", checks, 0.2, rng)
        ok = s_fix["best"] == opt and s_ada["best"] == opt
        print(f"{n:3d} {d:3d} {2 ** (n + 1) - 1:6d} {s_fix['nodes']:12d} {s_ada['nodes']:9d}  {ok}")
        assert ok, "the optimum was lost"
    print("checks passed:", checks)


def reopt_mode():
    """At sampled branching steps: min-over-weights Phi of the two children (each re-optimized
    from scratch) never exceeds that of the parent."""
    rng = random.Random(5)
    worst = -1e9
    count = 0
    ratios = []
    for trial in range(40):
        n = rng.randint(8, 12)
        F = random_formula(n, rng.uniform(3, 7), rng)
        inc = incidence(F)
        assign, cons = {}, []
        while len([w for w in range(n) if w not in assign]) > 2:
            free = [w for w in range(n) if w not in assign]
            if any(state(c, assign)[0] < 0 for c in cons):
                break
            x = rng.choice(free)
            _, lpar = reopt(cons, assign, free)
            checks = {"additive": 0}
            info, kids = step(F, inc, cons, assign, x, checks)
            lk = []
            for (a2, cons2, _) in kids:
                free2 = [w for w in range(n) if w not in a2]
                zero = [Con(c.sup, c.k0, 0.0) for c in cons2]          # restart from weight 0
                _, l2 = reopt(zero, a2, free2)
                lk.append(l2)
            worst = max(worst, lse(lk[0], lk[1]) - lpar)
            count += 1
            fixed_phi = log_phi(cons, assign, free)[0]
            ratios.append(fixed_phi - lpar)
            nxt = kids[rng.randrange(2)]
            assign, cons = nxt[0], nxt[1]
    print(f"{count} branching steps: largest log((Phi*(child0) + Phi*(child1)) / Phi*(parent)) = {worst:.2e}"
          f" (must be <= 0)")
    print(f"re-optimizing all weights lowers log Phi by {sum(ratios) / len(ratios):.3f} on average"
          f" (max {max(ratios):.3f}) compared with weights fixed at creation")


def aligned():
    F = circulant(9, 2)
    rng = random.Random(1)
    checks = {"additive": 0, "closed form": 0, "upper bound": 0}
    opt = optimum(F)
    for rule in ("fixed", "adaptive"):
        s = search(F, rule, checks, 0.05, rng)
        print(f"C_(9,2), {rule:8s}: {s['nodes']} nodes, {len(s['info'])} leaves, optimum ok: {s['best'] == opt},"
              f" information per leaf path: min {min(s['info']):.3f}, max {max(s['info']):.3f} bits")
    print("domination-based search on C_(9,2): 70 leaves; checks passed:", checks)


if __name__ == "__main__":
    {"examples": examples, "search": search_mode, "aligned": aligned, "reopt": reopt_mode}[sys.argv[1]]()
