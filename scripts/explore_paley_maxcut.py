#!/usr/bin/env python3
"""Max-Cut on Paley graphs as Max 2-SAT ((u v v), (-u v -v) on every edge): do the class conditions
(R1)-(R3) of the count-guessing theorem hold for the mean-centred decomposition, in the natural
order and in a random order?  Compare with Max-Cut on G(n, 1/2).

  python3 explore_paley_maxcut.py
"""
import sys
import numpy as np
sys.path.insert(0, "/Users/konstantin.kutzkov/Desktop/max-2-sat")
from explore_count_guessing import class_constants

def paley(q):
    res = {(x * x) % q for x in range(1, q)}
    A = np.zeros((q, q))
    for i in range(q):
        for j in range(q):
            if i != j and ((i - j) % q) in res:
                A[i, j] = 1
    return A

rng = np.random.default_rng(2)
print(f"{'graph':>18} {'n':>5} {'order':>8} {'K':>6} {'g':>7} {'R3 ratio':>9}")
for q in (401, 997, 1997):
    A = paley(q)
    for name, M in (("Paley", A), ("G(n,1/2)", None)):
        if M is None:
            U = np.triu(rng.random((q, q)) < 0.5, 1).astype(float)
            M = U + U.T
        J = -2.0 * M                       # Max-Cut: two equal-polarity clauses per edge
        for order in ("natural", "random"):
            P = np.arange(q) if order == "natural" else rng.permutation(q)
            beta, D, K, g, margin, cstar = class_constants(J[np.ix_(P, P)])
            print(f"{name:>18} {q:5d} {order:>8} {K:6.2f} {g:7.4f} {margin:9.3g}", flush=True)
