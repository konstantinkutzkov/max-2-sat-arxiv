# Lean artifact for the Max 2-SAT paper

This artifact accompanies `dense_max2sat_arxiv.tex`. It formalizes the paper's
algorithms and their mathematical analysis, including the common simplifications,
pruning constraints, enumeration, and exponential search-node bounds.

## Current coverage

The [correspondence register](verification/paper-correspondence.json) covers all
35 numbered statements in the manuscript:

| Status | Statements | Meaning |
| --- | ---: | --- |
| `checked` | 23 | Corresponding mathematical statements have checked Lean proofs. |
| `checked_core` | 11 | Correctness and actual search-node bounds are checked; polynomial bit-cost and space use the paper's conventional arguments. |
| `partial` | 0 | No numbered proved statement has an unfinished mathematical formalization. |
| `unverified` | 1 | The explicitly unproved biased-subset research target. |

All four main input families are covered: relative literal bias, the random
formula models, the regular-graph Max Cut families, and the stochastic block
model. Count guessing, projection guesses, and the hidden-mean discovery lemma
are also covered. Search bounds count actual recursion calls, including rejected
calls and suffix enumeration, rather than merely counting satisfying assignments.

The [latest scope record](verification/SUBMISSION_SCOPE.txt) describes the exact
boundary. `verification/result.json` records the completed build and audit;
`verification/RESULTS.txt` gives its human-readable summary.

### Explicit domain correction

The independent-pair appendix proposition now states **integer interaction
coefficients**, as in every Max 2-SAT and Max Cut input model in this paper.
Its earlier extra generalization to continuously distributed real coefficients
is not claimed. This narrows an auxiliary analytic statement without changing
any computational input family, main theorem, algorithm, or constant.

The formal statements allow an arbitrary original probability space, arbitrary
real marginal probabilities, and almost-sure bounds. A proved finite encoding
preserves independence, event probabilities, expectations, and the usual
measure-theoretic variance exactly. It is a proof device, not an algorithm input.
The original sample space need not be finite.

For hidden-mean discovery, the final theorem constructs a measurable event of
probability at least `1-1/n`. On this event the actual formula-only algorithm has
at most `K * p_r(n) * c^n` search nodes, where `c<2` and all constants are fixed
before the input size or distribution. The event depends only on binary
coefficients, and the bound holds for every choice of added units, even when
chosen after the draw using additional randomness.

## Established results and trust boundary

Two published results remain explicit hypotheses:

- Bandeira and van Handel's Rademacher matrix-norm expectation estimate,
  Theorem 3.1, Corollary 3.2 and its Rademacher extension.
- Ledoux's convex upper-tail inequality, Corollary 3.3 and interval rescaling.

Their precise sources, statements and specializations are in
[external-results.json](verification/external-results.json) and
[EXTERNAL_RESULTS.txt](verification/EXTERNAL_RESULTS.txt). Our applications,
including symmetrization, matrix geometry, independence and parameter
substitutions, are checked. The published theorems are not custom axioms and
are not presented as Lean proofs of the cited results. No unfinished internal
claim is classified as an external result.

The kernel audit permits only the standard `propext`, `Classical.choice`, and
`Quot.sound`. No source uses a proof placeholder, custom axiom, or `native_decide`.
A standard-axiom audit alone does not discharge explicit theorem hypotheses;
the external-dependency audit records those separately.

Polynomial bit-operation overhead, polynomial space and compiler correctness
are not machine-cost theorems. The paper-to-Lean translation is documented and
fingerprinted, but semantic equivalence between prose and Lean still warrants
independent mathematical review. The proposed biased-subset extension has no
proof and is not used in any verified result.

## Reproduce the checks

The project pins Lean `v4.34.0` and mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. Dependency revisions are in
`lake-manifest.json`. With elan installed, run from this directory:

```sh
lake exe cache get
python3 verify.py
```

A fresh checkout requires network access for the cache and dependencies.
`verify.py` builds the project and fifteen example modules, audits 1,110 public
mathematical declarations and the external signatures, checks dependency
revisions, validates every paper statement fingerprint, and records the source
and manuscript hashes. It reads the adjacent working manuscript or the `paper/`
snapshot in the standalone archive. Changed statements require a new
correspondence review. Executable examples supplement the universal proofs;
execution alone is not a proof certificate.

## Main entry points

| Paper component | Lean entry points |
| --- | --- |
| Clause semantics and preprocessing | `Basic`, `Pruning`, `Reduction`, `Preprocess` |
| Constraint propagation, summation and simplification | `ConstraintCheck`, `Normalization`, `Simplification` |
| Literal-bias algorithm and node bound | `Bias/` modules; see `verification/BIAS_PROOF.txt` |
| Original random formula models and runtime | `Random/FullRuntime`, `Random/ConcreteRuntime`; see `verification/RANDOM_COMPLETE.txt` |
| Count and projection guesses | `Counts/VerifiedAccumulation`, `VerifiedNodes`, `ProgramBounds`, `TwoRounds`, `GridPrograms` |
| Regular-graph Max Cut | `Regular/` modules; see `verification/REGULAR_GRAPHS.txt` |
| Independent-pair membership | `IndependentPairs/Membership`, `InputMembership`, `MeasureMembership` |
| Rational numerical construction | `Community/RotationScalar` through `ComputedDiscovery`; see `verification/RATIONAL_DIAGONALIZATION.txt` |
| Original hidden-mean discovery theorem | `Community/MeasureRuntime.integer_discovery_family` |
| Original stochastic block model | `Community/SBMRuntime.sbm_family` |
| General probability-space transport | `Random/MeasureInput`, `FiniteSupport`, `IntegerMoments` |

`Max2SAT.lean` imports the active artifact. `Audit.lean` lists the public
declarations for the transitive proof-dependency audit; supporting lemmas are
checked as dependencies. `ExternalAudit.lean` exposes the signatures conditional
on published results. The correspondence register maps paper labels to specific
audited declarations and records any conventional implementation boundary.

The text files in `verification/` describe earlier stages in detail. Their
remaining-work lists are historical; `SUBMISSION_SCOPE.txt` and the current
correspondence register take precedence. The former cumulative README is
preserved in `verification/README_HISTORY.txt`. Historical submission archives
are preserved separately and are not overwritten.
