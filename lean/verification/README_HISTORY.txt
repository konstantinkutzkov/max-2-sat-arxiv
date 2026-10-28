Historical cumulative README before final probability-space translation.
Current scope: README.md and verification/SUBMISSION_SCOPE.txt.

# Lean verification for the Max 2-SAT paper

This is the active formal artifact for `dense_max2sat_arxiv.tex`. It contains the
paper's fixed-preference literal-gap algorithm and the deterministic random-formula
algorithm with preferences recomputed from residual formulas. Both use summed
pruning constraints and streaming suffix enumeration. The older adaptive
implementation is excluded from the active build and submission archive; it is
preserved locally in `archive/pre-paper-alignment/` and in the earlier milestone
archives. Supporting lemmas are retained when they justify paper statements or
procedures. They need not each become a separate numbered lemma in the paper.

## What is checked

Lean checks the score-preserving reductions, comparison constraints, arithmetic
checker, exact enumeration, simultaneous-optimum argument, finite concentration
inequality, and the literal-bias candidate and recursion-node bounds. It also
checks recursion-depth and constraint-representation bounds for the literal-gap
algorithm. For the random-formula algorithm it checks deterministic correctness,
formula-only initialization, rational weighted-sum feasibility, and exact suffix
enumeration. The finite sampling models and observed-support conditioning
lemma, the full endpoint exposure lemma, and the absolute-gain and
second-moment lemma are also checked. The conditional-range and
bounded-differences lemma is checked on finite probability spaces, including
adaptive widths with a pathwise budget and the zero-influence case. The full
requirement and compensation estimates and fixed-support candidate counts are
also checked. These now imply expected and high-probability recursion-node
bounds for the actual initialized search on arbitrary original labels, with a
fixed exponential base below two. Restriction to observed pairs, conditioning,
empty supports, averaging over supports, and both concrete model wrappers are
checked. See [RANDOM_COMPLETE.txt](verification/RANDOM_COMPLETE.txt).
The conventional
polynomial bit-overhead and space arguments are explained in the paper; they are
not formal machine-cost or compiler proofs.

The [correspondence record](verification/paper-correspondence.json) lists **every
numbered result and proposed theorem** in the active manuscript. Its statuses mean:

- `checked`: the stated mathematical content has corresponding checked Lean
  declarations, with the translation and scope explained in the record.
- `checked_core`: the correctness, explicit node counts, and structural resource
  bounds are checked, while the final bit-complexity implementation argument is
  ordinary mathematics in the paper.
- `partial`: useful dependencies are checked, but additional mathematical claims
  in this result remain to be formalized.
- `unverified`: no verification of the complete result is claimed.

The dense-gap corollary now has the same `checked_core` status as the relative-bias
theorem, including its preprocessing-gap preservation and simple-input occurrence
estimates. The random-formula correctness lemma is `checked`; its main runtime
theorem is `checked_core`, including the complete probability argument and
actual initialized recursion-node bounds. The observed-pairs and exposure lemmas are both `checked`.
The absolute-gain and second-moment lemma is `checked`, including the
second assertion on arbitrary probability spaces. The conditional-range
lemma is `checked` on finite probability spaces. The accumulated-requirement
and compensation lemmas are `checked`, including their full-prefix
applications and input averaging. The general random-sign theorem and its two
concrete random-input cases are `checked_core`: the joint feasibility,
original-label candidate counts, conditioning, observed-support averaging,
and initialized-search node bounds are checked. The regular-graph corollary
is also `checked_core`, including its spectral estimates, both search branches,
and the uniform exponential node bound. The stochastic-block-model theorem
also has `checked_core` status, conditional on the two explicitly registered
published probability estimates; see the hidden-community section below.
The appendix extension is an unproved research target,
recorded as `unverified` with no Lean declarations. A
correspondence entry is not itself a proof of equivalence between prose and Lean;
its mathematical translation must still be reviewed.

## Reproduce the checks

The project pins Lean `v4.34.0` and mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. All dependency revisions are recorded in
`lake-manifest.json`. With elan installed, run from this directory:

```sh
lake exe cache get
python3 verify.py
```

The cache command requires network access on a fresh machine. `verify.py` builds
the modules, checks the examples, audits theorem axioms and package revisions,
validates the correspondence labels, statement fingerprints, and declaration names, and records source
and manuscript fingerprints in `verification/result.json`. It uses the adjacent
working manuscript, or the `paper/` snapshot included in the standalone archive.
Rerun it after editing sources or the manuscript. Changed statement text requires a fresh correspondence review. These syntactic
checks cannot establish semantic equivalence between prose and formal statements.

No proof uses `sorry`, `admit`, a custom axiom, or `native_decide`. The dependency
audit allows only the standard `propext`, `Classical.choice`, and `Quot.sound`.
Executable `#eval` examples supplement the universal proofs and are not proof
certificates themselves. Results and hashes describe precisely the checked files.

## Mathematical model and algorithm correspondence

An assignment is `Fin n → Bool`. A formula is a list of unit and binary clauses;
its integer score counts satisfied copies. `wellFormed` requires two different
variables in every binary clause. The formal results therefore cover simple
inputs and the unit multiplicities produced by preprocessing; many also hold for
arbitrary repeated clauses. `Simple F` additionally requires the list of clause
literal sets to have no duplicates: reversing a binary clause does not make it
a different clause. Simplicity is required only of the original input in the
dense-gap result. The model has no external hard input constraints.

A constraint stores literal occurrences and an integer bound. An occurrence
contributes zero or one, and duplicates are counted separately. `v.force true x`
sets the literal `v` to true. The strict comparison uses an offset of minus one.
`Constraint.infeasible_iff` decides feasibility of a **single** normalized
constraint; passing the sum test does not certify joint feasibility of a
collection.

`Bias.solveBiasPreprocessed` is the paper's literal-gap algorithm. It preprocesses
`F`, computes initial preferred bits and the half carrying more total absolute
gap, branches over that half, and streams the completions satisfying each
prefix's sum. It returns an optimal original assignment; its original score can
be read with `score F`. Thus returning a score/assignment pair in the pseudocode
adds only the final score evaluation.

The Lean implementation creates cuts when processing a prefix rather than
precomputing a table of identical cuts. Its suffix recursion substitutes and
normalizes at each call. The paper's oriented nonnegative-coefficient inequality
has the same feasible completions; choosing the order of the two children does
not change the node-count bound. Both versions retain only the best assignment.
Neither assumes that a suffix must satisfy every individual cut.

The correctness theorem holds without density assumptions. Under
`Bias.RelativeBias` on the preprocessed formula and `n > 0`,
`Bias.relative_bias_preprocessed` also proves the explicit bound

\[
 \mathrm{nodes}\le(4+2n)2^{(1-\varepsilon^2\eta^2/(3000R))n}.
\]

`Bias.relative_bias_nodes` gives the stronger natural-exponential constant 512.
`Bias.exponential_base_lt_two` proves the stated base is below two. The real
parameters and witness set `S` are proof parameters, not algorithm inputs.

For the general candidate lemma, `Bias.gap_mass_output_count` proves

\[
 W\le2^n\exp\left(-G^2/(512Q)\right),\qquad
 G=\sum_i|g_i|,\quad Q=\sum_i B_i^2>0.
\]

For the dense-gap corollary, `Bias.dense_gap_preprocessed` assumes a simple
**original** formula and at least eta*n original gaps of magnitude epsilon*n.
It proves optimality and the explicit bound

\[
 \mathrm{nodes}\le(4+2n)2^{(1-\varepsilon^2\eta^2/48000)n},
\]

with the same executable algorithm. Its proof includes preservation of effective
gaps by preprocessing, nonincrease of occurrence counts, the bound
B_i <= 4(n-1)+2 for a simple input, and the resulting Q <= 16n^3 and
G >= epsilon*eta*n^2 estimates. `Bias.dense_gap_output_count` gives the
corresponding candidate bound with natural-exponential denominator 8192.
The node theorem is stated for n > 0; general solver correctness covers n=0.
`Bias.dense_gap_base_lt_two` verifies the strict saving for positive parameters.

The implementation of `Simplify` as a complete loop is not part of the checked
literal-gap algorithm. Its individual rules and the guarded domination condition
are proved separately. The literal-gap algorithm needs only preprocessing,
restriction, and complementary cancellation.

## Random-formula algorithm

`Random.randomFormula` implements the formula-only procedure in Section 4.
`Random.randomFormula_correct` proves it returns both an optimum original score
and an assignment attaining it. The theorem covers repeated clauses, unit-only
variables, empty support, and zero variables. No generating graph or randomness
is supplied to the implementation.

Its support and distinct-neighbor weights are computed before preprocessing;
its order is the sorted original labels of variables with binary occurrences.
At each prefix node it computes the preferred literal from the residual effective
gap and adds a weighted strict cut to the nonpreferred branch. It checks the
weighted sum, and at the fixed stopping depth enumerates exactly its satisfying
suffixes. The proof follows the earliest-optimum argument in `lem:exactA`.

A rational per-variable cost representation performs exact complementary
cancellation without expanding weights into repeated literals. Residuals are
recomputed from the fixed preprocessed formula, and substitution in inherited
constraints is performed when their sum is tested. Exact score and minimum
identities justify these functional representations. The executable procedure
streams candidates; its full decision tree and list of outputs are proof objects.

See [RANDOM_CORRECTNESS.txt](verification/RANDOM_CORRECTNESS.txt) for the detailed
paper-to-code correspondence and remaining probabilistic obligations. This
milestone does **not** verify the random-input exponential runtime guarantee.

## Random-input distributions and conditioning

The finite-law development proves normalization, independent product laws,
conditioning on coordinate events, and exact joint-law preservation under
random endpoint flips. A pair multiset has four bounded multiplicities.
The two concrete input models have the claimed symmetries and second moments:
1 for one uniform clause, and 4q(1-q) for four independent inclusion trials.

The sampled pair counts generate the actual `Formula` representation.
Their nonempty support is proved to coincide with `Random.neighbors` before
preprocessing, even with arbitrary fixed units. Conditioning on the observed
support preserves independence and symmetry and cannot decrease the endpoint
second moments. This completes `lem:observed_pairs`.

For `lem:random_exposure`, the full auxiliary experiment has exactly the
prescribed joint law of pair patterns and an independent uniform assignment.
The checked history determines each coefficient while leaving the required
signs fresh. The full gain, its average over unassigned values, and the
preferred value after initialization and preprocessing are connected to the
actual algorithm. Conditional mean, variance, the bound using the observed
degree, and the later-deviation identities and joint sign laws are checked.
No independence of the pruning constraints is assumed. See
[RANDOM_PROBABILITY.txt](verification/RANDOM_PROBABILITY.txt) for sampling and
conditioning, and [RANDOM_EXPOSURE.txt](verification/RANDOM_EXPOSURE.txt) for
the complete exposure correspondence and remaining obligations.

The complete absolute-gain and second-moment lemma is checked. The
fourth-moment identity is proved by induction, averaging one fresh sign
at a time. Two Cauchy--Schwarz inequalities give the moment interpolation;
truncation and symmetry handle an arbitrary shift. The second assertion
is formalized on arbitrary probability spaces, then specialized to the
finite sampling laws through checked integral/expectation identities.
The sharp one-step range estimate and exponential Markov bound are also
checked. The full sequential argument with history-dependent interval lengths and a
pathwise budget is now checked, together with bounded differences for arbitrary
finite independent coordinate laws. The manuscript explicitly restricts this
lemma to finite probability spaces; all its applications have this form. The
main results and algorithms are unchanged. See
[RANDOM_MOMENTS.txt](verification/RANDOM_MOMENTS.txt) for the moment estimates.

The accumulated-requirement and compensation lemmas are now **checked in full**.
For requirements, a simpler pointwise bound replaces the variance calculation:
`sqrt(Y) >= Y/(m0*sqrt(d))`. Its expected lower bound implies the paper's
original constant. The independent-edge representation, sensitivities, and
whole-prefix budgets are checked. For compensation, actual score differences
are identified with edge contributions, grouped by later vertices, and charged
once to earlier endpoints. The full conditional exponential estimate is then
averaged over base patterns.

The joint feasibility bound and its transfer to the original input law are also
checked, followed by expected and high-probability candidate counts on a fixed
support. The search connection is now checked as well: every output satisfies
the complete prefix sum, no output is duplicated, and all recursive calls
(including rejected calls) are charged. The initialized algorithm's rational
constraints are identified with the original formula's score comparisons.
Preprocessing, the strict +1 offset, tie choices, and the prescribed order are
included in this identity. No algorithm, theorem statement, input family, or
stated constant changed.

`FixedSupportNodes` proves actual initialized-search expectation and tail bounds
for a nonempty fixed support whose indexed vertices are all active. It also
instantiates the conditional retained-pair law. `RuntimeRates` gives exponential
bases strictly below two for both bounds. The general deterministic node bound
allows inactive variables, and an empty active set has exactly one terminal call.

`ActiveSupport` through `ConcreteRuntime` now complete the original-label
transfer, observed-support averaging, and model wrappers. The proof charges
only active variables, fixes the other coordinates when counting candidates,
and preserves the comparison statistic when empty pair draws are deleted.
`FullRuntime` proves expected nodes at most `(4+6*n)*2^n*exp(-c0*n)` and a
`(4+2*n)*2^n*exp(-c0*n/2)` node threshold with failure probability at most
`3*exp(-c0*n/2)`. `ConcreteRuntime` instantiates both stated distributions.
No count or concentration bound is assumed in these final theorems.
The runtime results are **checked_core**; the final polynomial bit-cost and
streamed-space arguments remain conventional.
See [RANDOM_COMPLETE.txt](verification/RANDOM_COMPLETE.txt) for this completed
assembly and [RANDOM_RUNTIME.txt](verification/RANDOM_RUNTIME.txt) for the
preceding fixed-support milestone. [RANDOM_ACCUMULATION.txt](verification/RANDOM_ACCUMULATION.txt)
and [RANDOM_CONCENTRATION.txt](verification/RANDOM_CONCENTRATION.txt) describe
the underlying probability estimates.

## Count and projection guessing

`Counts.countResult` implements the count-comparison procedure, including
preprocessing, at most n+1 count guesses (one when beta=0), the original variable
labels and supplied rounds, exact rational suffix enumeration, and an original
optimum score with an attaining assignment. `lem:count_correctness` is checked.
The newly stated `lem:slice` has direct proofs in `Counts.Slice`: the exact
gain identity at the correct count and its inequality for either polarity,
including the diagonal correction and absolute-value allowance.

`Counts.projectionComparisons_correct` and `projection_optimum_enumerated` prove
`lem:counts-exact` for any supplied rational representation and covering guess
list. The diagonal correction and allowance are derived from actual clause
scores. Every optimum survives in an approximating run; candidates need not match
the guessed quantities. The explicit grid construction has checked coverage,
cardinality, and total-allowance bounds, including the square-root estimates in
`cor:spectral`.

The prefix/suffix node bound includes failed tests and is summed over every
guess. Both concentration inputs are now proved: finite-cube entropy and
smoothing give the common-gap tail, while a random partition gives the
sufficient quadratic tail. The paper contains these simpler proofs and the
revised explicit round constant; algorithms and input classes are unchanged.

`VerifiedAccumulation` proves the per-run bounds using only the paper's
deterministic norm, gap, and allowance hypotheses. `VerifiedNodes` connects
them to the executed searches. `ProgramBounds` specializes to actual formula
gains; count preprocessing and independence from the guess are proved.
`TwoRounds` supplies the main-text prefix of size floor(n/2) and the n+1 count
bound. `GridPrograms` combines the constructed grid's cardinality and allowance
bounds with both variants. The exponential base is proved strictly below two.
Correctness is supplied by the already checked count/projection procedures.

The common-gap lemma and the new finite-sign concentration lemma are `checked`.
The accumulation theorem, count specialization, and grid corollary are
`checked_core`: correctness and explicit node bounds are checked, while
polynomial arithmetic-cost and space remain conventional paper arguments.
The regular-graph corollary is now `checked_core`; see the next section.
Finite-law independent-pair membership is now checked conditional on the two
recorded published results. Hidden-community numerical discovery and the
full SBM runtime assembly remain incomplete; see the later status sections.
See [COUNT_COMPLETE.txt](verification/COUNT_COMPLETE.txt) for the current
correspondence, constants, and boundary of verification. Earlier batch reports
retain their historical scope and point forward to that report.

## Regular-graph Max-Cut

`cor:maxcut` now has a complete mathematical and recursive-call proof. The
formal hypothesis uses actual adjacency eigenvalues with multiplicity, omitting
exactly one occurrence of the regular degree. From it Lean derives the centered
operator estimate, mixing inequality, corrected row energy, rounded two-round
profile, and comparison allowance. It also checks the Max-Cut clause encoding
and the score identity, with arbitrary additional unit clauses.

The complete procedure first handles small inputs exhaustively, then selects
between a greedy independent-set search and the two-round count search by an
integer degree threshold. The independent-set construction, its size, optimal
unit-only completion, and its exact enumeration count are all checked.
`Regular.regular_result_correct` proves optimality on every graph.
`Regular.regular_family_nodes` chooses thresholds and constants once for the
family and bounds the actual nodes by `C*(n+1)*(2+14*n)*c^n`, where `1 <= c < 2`.
No mixing, norm, profile, or concentration estimate is assumed in that theorem.

See [REGULAR_GRAPHS.txt](verification/REGULAR_GRAPHS.txt) for the module map,
statement translation, and boundaries. The mathematical graph-to-formula encoding
uses a noncomputable edge-list ordering; a polynomial edge enumeration and the
per-node arithmetic/space analysis remain conventional implementation arguments.
Named Paley and Ramanujan graph constructions are not formalized. This milestone added `Regular.Examples`; the current build also includes
`IndependentPairs.Examples`.

## Independent-pair scalar estimates

`prop:pairmembership` is now `partial`. The scalar stage has direct finite-law
proofs: variance-sensitive exponential moments and tails, squared-entry
concentration, empirical-mean estimates, independent-copy moments/symmetry,
and deterministic effects of empirical centering. The sampling model has one
independent variable per unordered pair and builds the actual symmetric matrix.
Its energy normalization and the earlier-neighbor row laws are checked.

`IndependentPairs.scalar_event_probability` combines the scalar events without
assuming they are independent. Its hypotheses contain entry bounds, second
moments and explicit inequalities for the chosen mean threshold; its conclusion
is an explicit exponential failure bound. `bernoulli_scalar_event` instantiates
this for inhomogeneous Bernoulli edges, with Max-Cut variance `4*q*(1-q)`.
The manuscript now includes the elementary scalar argument. No algorithm or
input-family statement changes.

This scalar milestone is documented in
[INDEPENDENT_PAIRS_SCALAR.txt](verification/INDEPENDENT_PAIRS_SCALAR.txt).
The subsequent matrix milestone below checks the application of the published
norm results. The full membership proposition, its general non-finite laws,
and the SBM runtime theorem are not yet fully checked.
The full build now runs fourteen example modules.

## Published matrix estimates and their checked application

Our verification policy is to prove our own deductions and carefully check
our use of established published results; their proofs need not be formalized.
`IndependentPairs.ExternalResults` defines two explicitly named propositions:
the Rademacher expectation bound of Bandeira--van Handel (Theorem 3.1 and
Corollary 3.2), and Ledoux's mean-centered convex upper-tail inequality
(Corollary 3.3, pp. 165--166). These propositions are hypotheses of the
application theorems, not axioms or purported Lean proofs of the cited results.

`IndependentPairs.independent_pair_norm_tail` derives the actual upper-matrix
norm event and its n^-3 failure bound, conditional on these two results. The
pair sampling, symmetrization, independent signs, Euclidean operator norm,
convexity, Lipschitz property, row/column moments, and numerical substitutions
are checked. `scalar_operator_event` joins this with empirical centering and
the earlier scalar event. It does not assume independence after centering.

See `verification/EXTERNAL_RESULTS.txt` for exact source statements and the
scope of the application, and `verification/external-results.json` for the
external dependency register. The audit records these dependencies separately:
only standard axioms appearing in proof terms does **not** mean that the
external mathematical theorems have been formally proved. Independent review
of the source-to-Lean translation remains valuable.

The next membership batch completes both finite-law cases. The rounded
row-profile sum, comparison allowance, all scalar parameter substitutions,
final probability at least 1-1/n, and the count-accumulation size condition
are checked. `empirical_input_membership` and `supplied_input_membership`
state this for the original sampled coefficients under the original size
and density conditions; no intermediate concentration or membership bound
is assumed. Bernoulli specializations cover homogeneous empirical centering
and inhomogeneous supplied means. The gap constant and input classes are
unchanged; the proof uses a simpler sufficient profile lower bound of .61.

The full proposition remains partial only for arbitrary non-finite input laws.
The two published matrix estimates remain explicit hypotheses. This is not
a proof of the hidden-SBM runtime or numerical discovery. See
[INDEPENDENT_PAIR_MEMBERSHIP.txt](verification/INDEPENDENT_PAIR_MEMBERSHIP.txt)
for the theorem-by-theorem scope and index conventions.

## Hidden-community preprocessing

The new batch verifies the exact search wrapper for any total rational
representation callback, including exhaustive fallbacks and zero coefficient
mass. It implements the factor-two spacing using an integer square root,
checks the cap and grid size, and proves the positive-mass branch node bound
under explicit approximation conditions. Frobenius perturbation estimates
supply the deterministic energy and cross-round profile implications. The
symmetric noise bound reuses the existing upper-triangle estimate and the
same two published-result hypotheses. The paper uses K=400*chi in this proof.

The community assembly completes both coefficient cases of the runtime,
the formula remainder identity and the coefficient budget. It proves the
original-law cross-round/total-energy/norm event with probability at least
1-1/n. The numerical postprocessing supplies rational sorting, unit columns,
exact Rayleigh coefficients, truncation and the rank-to-Frobenius bound.

The new batch constructs the required frame directly from the formula.
A finite rational grid chooses each exactly orthogonal plane rotation.
Lean proves the largest-pivot energy identity, progress, termination within
M*n^10 steps and final Frobenius error at most n^-4. Both the grid and
iteration counts are polynomial in the explicitly listed formula length.
The actual formula-only algorithm now has unconditional exactness and a
high-probability search-node bound under explicit model/density/size
conditions. It assumes no numerical callback or approximation guarantees.
The hidden-community correctness lemma is checked. The new family/SBM
batch also completes the original density substitution and all bounded-size
cases. The original Bernoulli graph law, actual formula encoding, block-mean
rank/norm, minimum/maximum variance, and arbitrary graph-dependent units
are connected to the complete formula-only algorithm. One fixed rational
parameter, density constant, multiplier and base c<2 work uniformly over
all sizes, partitions, block probabilities and units in the stated family.
The SBM theorem is `checked_core`. The broader discovery lemma remains
partial only for translation of its original general integer-valued random
inputs to the finite sampling representation.
The same two published probability estimates are explicit hypotheses.
Bit-operation costs and polynomial space use the conventional paper
argument. See [SBM_COMPLETE.txt](verification/SBM_COMPLETE.txt) for the
current boundary and [RATIONAL_DIAGONALIZATION.txt](verification/RATIONAL_DIAGONALIZATION.txt)
for the numerical construction.

## Source organization

The random-search runtime connection uses `SearchNodes`, `PathBudget`,
`SearchCounts`, `ScorePaths`, `CanonicalOrder`, `FixedSupportNodes`, and
`RuntimeRates`. `RuntimeExamples` checks empty-support and rejection boundaries
and evaluates concrete node and output counts. The count is a mathematical
recursive-call model of the streaming search, not a compiler instruction count.

The completed count analysis additionally uses `QuadraticTail`, `CubeEntropy`,
`CubeMGF`, `Herbst`, `SmoothGap`, `SmoothEnergy`, `GapConcentration`,
`ProfileParameters`, `ProfileNorms`, `ScalarRates`, `CompletePassing`,
`VerifiedAccumulation`, `VerifiedNodes`, `GuessInvariance`, `ProgramBounds`,
`TwoRounds`, and `GridPrograms`. Their public theorems are included in the
transitive axiom audit; `CompleteExamples` checks representation boundaries.

- `Basic`, `Pruning`, `Reduction`, and `Preprocess`: score model, comparisons,
  reductions, and the executable preprocessing procedure.
- `ConstraintCheck`, `Normalization`, and `Simplification`: substitution,
  propagation, summation, exact minimum, and guarded domination.
- `PartialAssignment` and `Enumeration`: prefix compatibility and exact
  nonnegative rational-inequality enumeration with explicit node/depth bounds.
- `Bias/FairCoin`, `Incidence`, `Moments`, `Influence`, and `Accumulation`:
  the finite concentration proof and the formula statistics it bounds.
- `Bias/Optimal`, `ConstraintEnumeration`, and `Hybrid`: the common optimum,
  exact occurrence-constraint enumeration, and streaming prefix/suffix search.
- `Bias/Parameters`, `Counting`, `Complexity`, and `Resources`: branching-set
  choice, general candidate count, relative-bias theorem, and storage bounds.
- `Bias/PreprocessStats`, `Simple`, and `DenseGap`: preprocessing statistics,
  logical-clause simplicity and its incidence bound, and the dense-gap corollary.
- `Random/Residual` and `Support`: exact formula substitution, observed support,
  unit-only optimization, and the prescribed rational weights.
- `Random/Weighted` and `WeightedEnumeration`: weighted sums, exact minimum,
  completion enumeration, and its streaming implementation.
- `Random/ComparisonTree`, `FullTree`, `Search`, and `Algorithm`: the proof's
  earliest optimum, adaptive prefix search, and the formula-only outer procedure.
- `Random/FiniteLaw`, `ProductLaw`, and `FreshBits`: finite distributions,
  conditional product laws, and independent-sign transformations.
- `Random/PairModel`, `Sampling`, `Encoding`, and `ObservedFormula`: the input
  models, their formula representation, and observed-support conditioning.
- `Random/EndpointSigns`: symmetry construction and per-edge exposure identities.
- `Random/ProductTools`, `BlockLaws`, and `SignMoments`: coordinate projections,
  exact conditional laws, and finite signed-sum moments.
- `Random/FormulaGains` and `GainAverage`: actual score differences, residual
  gaps, preprocessing preservation, and uniform-completion averages.
- `Random/ExposureGraph`, `ExposureSupport`, and `ExposureLaw`: bit indices,
  coefficients, observed degree, history transitions, and the full sampling law.
- `Random/SequentialExposure` and `Exposure`: conditional exposure results and
  their connection to the initialized formula-only algorithm.
- `Random/MeasureBridge` and `MomentBounds`: finite-law/measure correspondence
  and moment inequalities on general probability spaces.
- `Random/FourthMoment` and `AbsoluteGains`: exact signed fourth moments,
  expected absolute gaps, truncation, symmetry, and arbitrary shifts.
- `Random/Hoeffding`, `HistoryAverage`, and `AdaptiveRanges`: sharp one-step
  estimates, exact finite conditional expectations, and sequential concentration
  with history-dependent widths and a pathwise budget.
- `Random/BoundedDifferences` and `BitHistory`: independent-input concentration
  and the connection between history classes and the actual exposure laws.
- `Random/RequirementMean`, `WeightBounds`, `RequirementDegree`, and
  `RequirementTail`: local requirement drift, actual rational normalization,
  conditional concentration, and exceptional-event bookkeeping.
- `Random/PredictableSigns`, `ConditionalMGF`, and `CompensationRow`: adaptive
  signed increments, block composition, and conditional incoming-row estimates
  for coefficients from actual residual comparisons.
- `Random/OrderedExposure`, `CompensationSum`, and `CompensationTail`: the fixed
  order, exact full compensation identity, total budget, and averaged tail.
- `Random/ConcentrationTools`, `EdgeVariance`, `EdgeDataLaw`, `DriftMean`,
  `DriftSensitivity`, and `DriftTail`: independent edge representation, the simpler
  mean estimate, normalized coordinate influences, and available-drift tails.
- `Random/RequirementAccumulation` and `AccumulatedRequirements`: the full
  prefix process and the complete two-term requirement bound.
- `Random/SumFeasibility` and `CandidateProbability`: the actual comparison sum,
  joint feasibility, and expected/high-probability counts on a fixed support.
- `Counts/Affine`, `FormulaGains`, and `Adjustments`: rational gain expressions,
  exact formula identities, count guesses, and projection error allowances.
- `Counts/Comparisons`, `PrefixSearch`, `Runs`, and `Algorithms`: earlier-round
  preferences, actual summed budgets, streamed enumeration and optimum output.
- `Counts/Grids` and `GridBounds`: computed coordinate grids and tuples, coverage,
  cardinality, Cauchy--Schwarz, and the total comparison allowance.
- `Counts/AccumulationIdentity` and `Resources`: the exact comparison statistic
  and conditional conversion from passing probabilities to total search nodes.
- `Counts/GapProfile` and `GapBridge`: deterministic clipping, shifted first
  moments, and the exact signed-row representation of computed averages.
- `Counts/BitExposure` and `CreatorTail`: actual ordered assignments, conditional
  fair bits, creator concentration, and comparison-allowance subtraction.
- `Counts/SequentialCompensation`, `OperatorEnergy`, and `SequentialPassing`:
  implemented compensation, Euclidean operator budgets, and the passing bound
  modular passing bound whose probability input is discharged in CompletePassing.
- `Counts/RoundCompensation`: the fixed-round quadratic-plus-linear expansion,
  joint fair-mask law, and linear tail. No assumed quadratic concentration axiom.
- `Counts/RoundSplit` and `LaterRounds`: actual later/within-round compensation,
  predictable individual-bit exposure, block energy budgets, and the later tail.
- `Counts/RoundHistory`, `BlockNorms`, and `WithinRounds`: conditional joint laws,
  norm restriction/conjugation, actual linear tails, and transfer of the explicit
  quadratic-tail hypothesis.
- `Counts/RoundPassing`: the full exceptional-event assembly, conditional on the
  common-gap and generic quadratic probability estimates.
- `Counts/GainStructure`: symmetry and zero diagonal from the actual formula
  gains, count adjustments, and arbitrary supplied projection adjustments.
- `IndependentPairs/Profile`, `MembershipParameters`, and `MembershipProbability`:
  rounded root sums, original density/size substitutions, allowance and the
  complete exceptional-probability budget.
- `IndependentPairs/Membership` and `InputMembership`: both complete finite-law
  membership events, original-coefficient translation, and Bernoulli models.
- `Community/Algorithm`, `Spacing`, `RationalRoot`, and `Computed`: executable
  search wrapper, all exact fallback branches, and actual capped rational grids.
- `Community/Perturbation`, `Energy`, `Noise`, `Rounds`, and `Runtime`:
  deterministic quality bounds, reused symmetric-noise tail, and conditional
  positive-mass recursion-node bound.
- `Community/FullSearch`, `CrossRows`, `RandomEvent`, `CoefficientBudget`,
  `RepresentationMatrix`, and `DiscoveryBridge`: zero-mass runtime, joint
  original-law noise event, Rayleigh budget, and the conditional link from
  numerical guarantees to the actual search's high-probability node bound.
- `Community/RankGeometry`, `DiagonalTruncation`, `SpectralTruncation`,
  `RationalFrame`, `TopSelection`, and `FrameGuarantees`: elementary truncation,
  rank-to-Frobenius error, exact rational postprocessing and its connection
  to all four search approximation guarantees.
- `Community/RotationScalar`, `PlaneRotation`, `GridRotation`, `PlaneEnergy`,
  `JacobiStep`, `JacobiIteration`, `JacobiParameters`, `FrameResidual`,
  `FormulaScale`, and `ComputedDiscovery`: actual rational diagonalization,
  termination/error and polynomial iteration/grid bounds, plus formula-only
  exactness and the search-node probability bound.
- `Community/FamilyParameters`, `UniversalNodes`, `FamilyRuntime`, `SBMModel`,
  `SBMVariance`, and `SBMRuntime`: density substitution, fixed class constants,
  all input sizes, actual original Bernoulli graphs and their formula encoding,
  block-mean rank/norm, and the complete SBM node bound.
- The fifteen example modules: kernel-checked regressions and small executions;
  the random examples cover distributional identities, adaptive budgets,
  accumulated counts, and exact boundary feasibility. Count examples also cover
  negative adjustments, grid endpoints, rank zero, count-mismatching outputs,
  simultaneous later/within-round compensation, and empty intermediate rounds.

`Audit.lean` lists public declarations for the transitive axiom audit. Further
supporting lemmas are checked as dependencies. See
[BIAS_PROOF.txt](verification/BIAS_PROOF.txt) for a prose guide.

The policy for subsequent work is to revise a paper statement and its formal
counterpart together, record any remaining gap explicitly, and rebuild before
reporting verification. Full coverage of the paper is a goal; the current
artifact does not claim it.
