"""Exact checks for max2sat_redundancy_and_group_counts.tex.

Run with Python 3; no third-party packages are needed. The solver streams
count vectors and assignments. The separate verification harness may store
exhaustive scores of small instances to check every flip identity.
"""

from itertools import combinations, product
from math import log2, prod
from pathlib import Path
import json
import random


def literal_value(literal, assignment):
    value = assignment[abs(literal) - 1]
    return value if literal > 0 else 1 - value


def clause_score(clauses, assignment):
    return sum(any(literal_value(lit, assignment) for lit in clause)
               for clause in clauses)


def quadratic_form(n, clauses):
    constant = 0
    fields = [0] * n
    matrix = [[0] * n for _ in range(n)]
    for clause in clauses:
        if len(clause) == 1:
            literal = clause[0]
            u = abs(literal) - 1
            constant += int(literal < 0)
            fields[u] += 1 if literal > 0 else -1
        else:
            left, right = clause
            u, v = abs(left) - 1, abs(right) - 1
            # A false-literal indicator is a + b*x; the clause is 1-f*g.
            a, b = (1, -1) if left > 0 else (0, 1)
            c, d = (1, -1) if right > 0 else (0, 1)
            constant += 1 - a * c
            fields[u] -= b * c
            fields[v] -= a * d
            matrix[u][v] -= b * d
            matrix[v][u] -= b * d
    return constant, fields, matrix


def orient_clauses(clauses, flipped):
    return [tuple(-lit if abs(lit) - 1 in flipped else lit for lit in clause)
            for clause in clauses]


def profile_groups(matrix, side_a, side_b):
    groups = {}
    for u in side_a:
        profile = tuple(matrix[u][v] for v in side_b)
        groups.setdefault(profile, []).append(u)
    return list(groups.values())


def count_assignments(groups, counts, n):
    """Yield a reused bit vector with the specified group counts."""
    bits = [0] * n

    def visit(index):
        if index == len(groups):
            yield bits
            return
        group = groups[index]
        for selected in combinations(group, counts[index]):
            for u in group:
                bits[u] = 0
            for u in selected:
                bits[u] = 1
            yield from visit(index + 1)

    yield from visit(0)


def solve_by_group_counts(n, clauses, side_a, side_b, flipped=frozenset()):
    oriented = orient_clauses(clauses, flipped)
    constant, fields, matrix = quadratic_form(n, oriented)
    groups = profile_groups(matrix, side_a, side_b)
    outside = [u for u in range(n) if u not in set(side_a + side_b)]
    edges_a = [(u, v, matrix[u][v]) for u, v in combinations(side_a, 2)]
    edges_b = [(u, v, matrix[u][v]) for u, v in combinations(side_b, 2)]
    pattern_count = prod(len(group) + 1 for group in groups)
    best = None
    witness = None
    a_evaluations = b_evaluations = 0

    for outside_values in product((0, 1), repeat=len(outside)):
        base = [0] * n
        for u, value in zip(outside, outside_values):
            base[u] = value
        base_score = (constant + sum(fields[u] * base[u] for u in outside)
                      + sum(matrix[u][v] * base[u] * base[v]
                            for u, v in combinations(outside, 2)))
        adjusted = [fields[u] + sum(matrix[u][v] * base[v] for v in outside)
                    for u in range(n)]

        for counts in product(*(range(len(group) + 1) for group in groups)):
            best_a = None
            a_witness = None
            for bits in count_assignments(groups, counts, n):
                a_score = (sum(adjusted[u] * bits[u] for u in side_a)
                           + sum(weight * bits[u] * bits[v]
                                 for u, v, weight in edges_a))
                a_evaluations += 1
                if best_a is None or a_score > best_a:
                    best_a, a_witness = a_score, bits.copy()

            b_fields = {v: adjusted[v] + sum(k * matrix[group[0]][v]
                                            for group, k in zip(groups, counts))
                        for v in side_b}
            best_b = None
            b_witness = None
            for values in product((0, 1), repeat=len(side_b)):
                bits = dict(zip(side_b, values))
                b_score = (sum(b_fields[v] * bits[v] for v in side_b)
                           + sum(weight * bits[u] * bits[v]
                                 for u, v, weight in edges_b))
                b_evaluations += 1
                if best_b is None or b_score > best_b:
                    best_b, b_witness = b_score, bits
            score = base_score + best_a + best_b
            if best is None or score > best:
                best = score
                witness = base.copy()
                for u in side_a:
                    witness[u] = a_witness[u]
                for v in side_b:
                    witness[v] = b_witness[v]

    for u in flipped:
        witness[u] = 1 - witness[u]
    assert clause_score(clauses, witness) == best
    assert a_evaluations == 2 ** (n - len(side_b))
    assert b_evaluations == pattern_count * 2 ** (n - len(side_a))
    return best, {
        "group_sizes": [len(group) for group in groups],
        "count_vectors": pattern_count,
        "gamma": len(side_a) - log2(pattern_count),
        "a_evaluations": a_evaluations,
        "b_evaluations": b_evaluations,
    }


def exhaustive_checks(n, clauses):
    scores = {bits: clause_score(clauses, bits)
              for bits in product((0, 1), repeat=n)}
    constant, fields, matrix = quadratic_form(n, clauses)
    for bits, score in scores.items():
        expanded = (constant + sum(fields[u] * bits[u] for u in range(n))
                    + sum(matrix[u][v] * bits[u] * bits[v]
                          for u, v in combinations(range(n), 2)))
        assert expanded == score

    flip_checks = strict_checks = 0
    for u in range(n):
        others = [v for v in range(n) if v != u]
        for sign in (-1, 1):
            literal = sign * (u + 1)
            positive_neighbors = [next(lit for lit in clause if lit != literal)
                                  for clause in clauses
                                  if len(clause) == 2 and literal in clause]
            negative_neighbors = [next(lit for lit in clause if lit != -literal)
                                  for clause in clauses
                                  if len(clause) == 2 and -literal in clause]
            positive_units = clauses.count((literal,))
            negative_units = clauses.count((-literal,))
            gap = (len(positive_neighbors) + positive_units
                   - len(negative_neighbors) - negative_units)
            deficit = len(negative_neighbors) - positive_units + negative_units
            for values in product((0, 1), repeat=n - 1):
                bits = [0] * n
                for v, value in zip(others, values):
                    bits[v] = value
                a = sum(literal_value(lit, bits) for lit in positive_neighbors)
                b = sum(literal_value(lit, bits) for lit in negative_neighbors)
                bits[u] = int(sign > 0)
                true_score = scores[tuple(bits)]
                bits[u] = int(sign < 0)
                false_score = scores[tuple(bits)]
                difference = false_score - true_score
                assert difference == a - b - gap
                assert (difference > 0) == (len(positive_neighbors) - a + b <= deficit - 1)
                if difference > 0:
                    assert a >= gap + 1
                    assert b <= deficit - 1
                    strict_checks += 1
                flip_checks += 1
    return max(scores.values()), len(scores), flip_checks, strict_checks


def planted_formula(rng, n, groups, side_b, exceptions):
    side_a = [u for group in groups for u in group]
    core_b = [v for v in side_b if v not in exceptions]
    clauses = []
    for u, v in combinations(range(n), 2):
        if (u in side_a and v in core_b) or (v in side_a and u in core_b):
            continue
        if rng.random() < 0.75:
            clauses.append((rng.choice((-1, 1)) * (u + 1),
                            rng.choice((-1, 1)) * (v + 1)))
    for group in groups:
        for v in core_b:
            coefficient = rng.choice((-1, 0, 1))
            if coefficient == 0:
                continue
            for u in group:
                left_sign = rng.choice((-1, 1))
                right_sign = -coefficient * left_sign
                clauses.append((left_sign * (u + 1), right_sign * (v + 1)))
    for u in range(n):
        for _ in range(rng.randrange(4)):
            clauses.append((rng.choice((-1, 1)) * (u + 1),))
    flipped = {u for u in range(n) if rng.randrange(2)}
    return orient_clauses(clauses, flipped), side_a, core_b, flipped


def main():
    seed = 87123
    rng = random.Random(seed)
    configurations = [
        (7, [[0, 1], [2]], [3, 4, 5], []),
        (8, [[0, 1], [2, 3]], [4, 5, 6], [6]),
        (9, [[0, 1, 2], [3, 4]], [5, 6, 7], []),
        (10, [[0, 1], [2, 3], [4, 5]], [6, 7, 8], [8]),
        (9, [[0, 1], [2, 3]], [4, 5, 6, 7], [6, 7]),
        (8, [[0, 1, 2, 3]], [4, 5, 6, 7], []),
    ]
    summary = {
        "seed": seed,
        "group_count_instances": 0,
        "exception_column_instances": 0,
        "aligned_sorting_instances": 0,
        "exhaustive_assignments": 0,
        "flip_identity_checks": 0,
        "strict_improvement_implication_checks": 0,
        "group_a_evaluations": 0,
        "group_b_evaluations": 0,
        "all_checks_passed": False,
    }
    details = []
    for n, planted_groups, side_b, exceptions in configurations:
        for trial in range(8):
            clauses, side_a, core_b, flipped = planted_formula(
                rng, n, planted_groups, side_b, exceptions)
            optimum, assignments, flips, strict = exhaustive_checks(n, clauses)
            result, stats = solve_by_group_counts(n, clauses, side_a, core_b, flipped)
            assert result == optimum
            summary["group_count_instances"] += 1
            summary["exception_column_instances"] += bool(exceptions)
            summary["exhaustive_assignments"] += assignments
            summary["flip_identity_checks"] += flips
            summary["strict_improvement_implication_checks"] += strict
            summary["group_a_evaluations"] += stats["a_evaluations"]
            summary["group_b_evaluations"] += stats["b_evaluations"]
            oriented = orient_clauses(clauses, flipped)
            _, _, matrix = quadratic_form(n, oriented)
            old_groups = profile_groups(matrix, side_a, side_b)
            old_patterns = prod(len(group) + 1 for group in old_groups)
            assert stats["count_vectors"] <= old_patterns
            details.append({"n": n, "trial": trial, "exceptions": exceptions,
                            "optimum": optimum, "groups_before_exposure":
                            [len(group) for group in old_groups], **stats})

    for n in range(3, 11):
        for _ in range(2):
            clauses = []
            for u, v in combinations(range(n), 2):
                sign = rng.choice((-1, 1))
                clauses.append((sign * (u + 1), sign * (v + 1)))
            for u in range(n):
                for _ in range(rng.randrange(4)):
                    clauses.append((rng.choice((-1, 1)) * (u + 1),))
            optimum, assignments, flips, strict = exhaustive_checks(n, clauses)
            constant, fields, matrix = quadratic_form(n, clauses)
            assert all(matrix[u][v] == -1 for u, v in combinations(range(n), 2))
            ordered = sorted(fields, reverse=True)
            prefix = 0
            sorted_optimum = constant
            for k, field in enumerate(ordered, start=1):
                prefix += field
                sorted_optimum = max(sorted_optimum, constant + prefix - k * (k - 1) // 2)
            assert sorted_optimum == optimum
            summary["aligned_sorting_instances"] += 1
            summary["exhaustive_assignments"] += assignments
            summary["flip_identity_checks"] += flips
            summary["strict_improvement_implication_checks"] += strict

    summary["all_checks_passed"] = True
    output = Path(__file__).with_name("group_count_checks.json")
    output.write_text(json.dumps({"summary": summary, "instances": details}, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
