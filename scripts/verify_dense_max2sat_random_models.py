"""Finite exact-arithmetic checks for the paper's random-model section.

These check distribution identities and comparison correctness on small
instances; they do not certify the asymptotic concentration bounds.
Run with Python 3, using only the standard library.
"""

from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import random


CLAUSE_TYPES = ((1, 1), (0, 0), (1, 0), (0, 1))
BITS4 = tuple(product((0, 1), repeat=4))


def pair_moments(probabilities):
    total = mean = second = clauses = F(0)
    for bits in BITS4:
        weight = F(1)
        for bit, probability in zip(bits, probabilities):
            weight *= probability if bit else 1 - probability
        interaction = bits[2] + bits[3] - bits[0] - bits[1]
        total += weight
        mean += weight * interaction
        second += weight * interaction**2
        clauses += weight * sum(bits)
    assert total == 1
    return mean, second - mean**2, clauses


def distribution_checks():
    cases = 0
    for q in (F(1, 16), F(1, 8), F(1, 4), F(1, 2)):
        for epsilon in (F(-1), F(-1, 2), F(0), F(1, 2), F(1)):
            if q * (1 + abs(epsilon)) > F(1, 2):
                continue
            mean, variance, clauses = pair_moments(
                (q * (1 + epsilon),) * 2 + (q * (1 - epsilon),) * 2
            )
            assert mean == -4 * q * epsilon
            assert variance == 4 * q - 4 * q**2 * (1 + epsilon**2)
            assert variance >= 2 * q and clauses == 4 * q
            cases += 1
    for p in (F(1, 16), F(1, 4), F(1)):
        mean = second = clauses = F(0)
        for selected in (0, 1):
            for bits in BITS4:
                weight = p if selected else 1 - p
                for bit in bits:
                    weight *= F(1, 4) if bit else F(3, 4)
                interaction = selected * (bits[2] + bits[3] - bits[0] - bits[1])
                mean += weight * interaction
                second += weight * interaction**2
                clauses += weight * selected * sum(bits)
        assert mean == 0 and second == 3 * p / 4 and clauses == p
        cases += 1
    return cases


def make_instance(n, model, rng):
    clauses = []
    for u in range(n):
        for v in range(u + 1, n):
            if model == "random_support" and rng.randrange(2) == 0:
                continue
            probabilities = (3, 3, 1, 1) if model == "biased" else (2,) * 4
            for (su, sv), numerator in zip(CLAUSE_TYPES, probabilities):
                if rng.randrange(8) < numerator:
                    clauses.append(((u, su), (v, sv)))
    # Units may depend on the binary instance and have either sign.
    for u in range(n):
        degree = sum(any(v == u for v, _ in clause) for clause in clauses if len(clause) == 2)
        clauses.extend([((u, (degree + u) % 2),)] * rng.randrange(4))
    constant, linear = 0, [0] * n
    interaction = [[0] * n for _ in range(n)]
    for clause in clauses:
        if len(clause) == 1:
            (u, sign), = clause
            constant += 1 - sign
            linear[u] += 2 * sign - 1
        else:
            (u, su), (v, sv) = clause
            au, bu = su, 1 - 2 * su
            av, bv = sv, 1 - 2 * sv
            constant += 1 - au * av
            linear[u] -= bu * av
            linear[v] -= bv * au
            interaction[u][v] -= bu * bv
            interaction[v][u] -= bu * bv
    return clauses, constant, linear, interaction


def passes(x, linear, interaction, slack, depth):
    creators = []
    gain_sum = 0
    for t in range(depth):
        delta_twice = 2 * linear[t]
        delta_twice += 2 * sum(interaction[t][j] * x[j] for j in range(t))
        delta_twice += sum(interaction[t][j] for j in range(t + 1, len(x)))
        preferred = int(delta_twice >= 0)
        if x[t] != preferred:
            gain = (1 - 2 * x[t]) * (linear[t] + sum(a * b for a, b in zip(interaction[t], x)))
            creators.append(gain)
            gain_sum += gain
    return gain_sum <= slack * len(creators), creators


def instance_checks():
    rng = random.Random(20261012)
    instances = scores_checked = flip_identities = candidate_tests = optimum_checks = 0
    for n, model, repetition in product((6, 7, 8), ("unbiased", "biased", "random_support"), range(4)):
        clauses, constant, linear, interaction = make_instance(n, model, rng)
        assignments = tuple(product((0, 1), repeat=n))
        scores = []
        for x in assignments:
            score = constant + sum(a * b for a, b in zip(linear, x))
            score += sum(interaction[u][v] * x[u] * x[v] for u in range(n) for v in range(u + 1, n))
            assert score == sum(any(x[u] == sign for u, sign in clause) for clause in clauses)
            scores.append(score)
            scores_checked += 1
        optimum = max(scores)
        denominator = n * (n - 1) // 2
        beta_numerator = sum(interaction[u][v] for u in range(n) for v in range(u + 1, n))
        remainder = [[denominator * interaction[u][v] - beta_numerator if u != v else 0
                      for v in range(n)] for u in range(n)]
        best_plain = best_count = -1
        for x, score in zip(assignments, scores):
            accepted, _ = passes(x, linear, interaction, 0, n // 2)
            candidate_tests += 1
            if accepted:
                best_plain = max(best_plain, score)
            if score == optimum:
                assert accepted
                optimum_checks += 1
            for count in range(n + 1):
                shifted = [denominator * a + beta_numerator * count for a in linear]
                accepted, gains = passes(x, shifted, remainder, abs(beta_numerator), n // 2)
                candidate_tests += 1
                if accepted:
                    best_count = max(best_count, score)
                if count == sum(x):
                    for t in range(n):
                        original = (1 - 2 * x[t]) * (linear[t] + sum(a * b for a, b in zip(interaction[t], x)))
                        auxiliary = (1 - 2 * x[t]) * (shifted[t] + sum(a * b for a, b in zip(remainder[t], x)))
                        assert denominator * original - auxiliary == beta_numerator * x[t]
                        flip_identities += 1
                    if score == optimum:
                        assert accepted and all(gain <= abs(beta_numerator) for gain in gains)
                        optimum_checks += 1
        assert best_plain == best_count == optimum
        instances += 1
    return dict(instances=instances, score_identities=scores_checked,
                flip_identities=flip_identities, candidate_tests=candidate_tests,
                optimum_survival_checks=optimum_checks)


if __name__ == "__main__":
    result = dict(distribution_cases=distribution_checks(), **instance_checks())
    result["status"] = "passed"
    result["scope"] = "Finite identities and correctness checks; not an asymptotic proof."
    Path(__file__).with_name("dense_max2sat_random_checks.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
